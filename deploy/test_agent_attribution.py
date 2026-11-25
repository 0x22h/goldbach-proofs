"""Submission provenance is self-reported, immutable and tied to an authorized head."""
import json
import sqlite3
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from deploy.desk import Desk, agent_metadata
from deploy import test_desk as desk_tests
from deploy.test_desk import GAPS, START
from tools import goldbach


class AttributionTests(unittest.TestCase):
    def setUp(self):
        self.helper = desk_tests.DeskTests()
        self.helper.setUp()
        self.addCleanup(self.helper.doCleanups)
        self.desk = self.helper.desk
        self.agent = dict(model='Model-A-2026', harness='codex', harness_version='1.2.3')

    def submit(self, token, agent=None, **options):
        body = dict(pr=8, head='a' * 40)
        body.update(options)
        if agent is not None:
            body['agent'] = agent
        return self.helper.request('submit', body, token=token)

    def test_validation_and_normalization(self):
        self.assertEqual(agent_metadata(self.agent)['model'], 'model-a-2026')
        self.assertEqual(agent_metadata({'model': 'MODEL  A', 'harness': 'CODEX'})['model'], 'model a')
        for value in ([], 'codex', {'model': ''}, {'model': True}, {'model': 'a'*97},
                      {'model': '<script>'}, {'model': 'a\nb'}, {'harness': 'made-up'}, {'extra': 1}):
            with self.subTest(value=value), self.assertRaises(ValueError):
                agent_metadata(value)
        token = self.helper.claim()
        self.assertEqual(self.submit(token, {'harness': 'made-up'})[0], 400)
        self.assertEqual(self.submit(token, self.agent)[0], 200)

    def test_new_submissions_require_both_fields_without_consuming_lease(self):
        token = self.helper.claim()
        for fields in ({}, {"agent": None}, {"agent": {}}, {"agent": {"model": "a"}},
                       {"agent": {"harness": "codex"}}):
            body = {"pr": 8, "head": "a"*40, **fields}
            self.assertEqual(self.helper.request("submit", body, token=token),
                             (400, {"error": "agent_model_and_harness_required"}))
        self.assertEqual(self.submit(token, {"model": "model-a", "harness": "codex"})[0], 200)

    def test_metadata_frozen_and_legacy_retry_does_not_erase_it(self):
        token = self.helper.claim()
        self.assertEqual(self.submit(token, self.agent)[0], 200)
        self.assertEqual(self.submit(token, self.agent)[0], 200)
        self.assertEqual(self.submit(token)[0], 200)
        self.assertEqual(self.submit(token, dict(self.agent, model='model-b')),
                         (409, {'error': 'submission_metadata_frozen'}))
        self.assertEqual(self.submit(token, self.agent, head='b'*40)[0], 409)
        with self.desk.transaction() as conn:
            row = conn.execute('SELECT model, harness, harness_version FROM goldbach_leases').fetchone()
        self.assertEqual(tuple(row), ('model-a-2026', 'codex', '1.2.3'))

    def test_changed_head_keeps_its_own_attribution_and_authorized_run(self):
        token = self.helper.claim()
        self.submit(token, self.agent)
        self.assertEqual(self.helper.request('authorize', self.helper.authorization(), sign=True)[0], 200)
        with patch('deploy.desk.time.time', return_value=START+10):
            self.helper.record(102, GAPS[0]['id'], 'REJECTED')
        token2 = self.helper.claim(now=START+20)
        self.assertEqual(self.submit(token2, dict(self.agent, model='model-b'), head='b'*40)[0], 200)
        self.assertEqual(self.helper.request('authorize', self.helper.authorization(head='a'*40, run_id=103), sign=True)[0], 409)
        self.assertEqual(self.helper.request('authorize', self.helper.authorization(head='b'*40, run_id=103), sign=True)[0], 200)
        with patch('deploy.desk.time.time', return_value=START+30):
            self.helper.record(103, GAPS[0]['id'], 'ACCEPTED')
            self.helper.record(103, GAPS[0]['id'], 'ACCEPTED', attempt=2)
            self.helper.record(103, GAPS[0]['id'], 'REJECTED', attempt=3)
        records = [{'run_id': 102, 'lemma_id': GAPS[0]['id']}, {'run_id': 103, 'lemma_id': GAPS[0]['id']}, {'run_id': 103, 'lemma_id': GAPS[1]['id']}]
        with self.desk.transaction() as conn:
            self.desk.annotate_verdicts(records, conn)
        self.assertEqual([r['agent']['model'] for r in records], ['model-a-2026', 'model-b', 'unknown'])
        self.assertEqual(records[0]['agent']['source'], 'self_reported')
        ranks = self.helper.status(now=START+40)['agent_rankings']
        self.assertEqual(ranks, {'models': [{'name': 'model-b', 'accepted': 1}], 'harnesses': [{'name': 'codex', 'accepted': 1}], 'proofs': 1})

    def test_first_acceptance_unknown_history_and_separate_models(self):
        with self.desk.transaction(write=True) as conn:
            for run, gap, model, harness, verdict in [
                (1, 'first', 'model-a', 'codex', 'ACCEPTED'),
                (2, 'first', 'model-b', 'cursor', 'ACCEPTED'),
                (3, 'second', 'model-a-v2', 'codex', 'ACCEPTED'),
                (4, 'third', 'unknown', 'unknown', 'ACCEPTED'),
                (6, 'fifth', 'model-c', 'unknown', 'ACCEPTED'),
                (7, 'sixth', 'unknown', 'cursor', 'ACCEPTED'),
                (5, 'fourth', 'model-b', 'cursor', 'REJECTED'),
            ]:
                conn.execute("""INSERT INTO goldbach_leases (token_hash,gap,statement_sha256,handle,ip_key,claimed_at,expires_at,absolute_expires_at,run_id,finished_at,verdict,model,harness)
                    VALUES (?,?,'hash','alice','network',0,0,0,?,?,?,?,?)""", (str(run),gap,run,START+run,verdict,model,harness))
        status = self.helper.status(now=START+20)
        ranks = status['agent_rankings']
        self.assertEqual(ranks['proofs'], 4)
        self.assertEqual(status['rankings']['proofs'], 5)
        self.assertEqual(ranks['models'], [{'name': x, 'accepted': 1} for x in ['model-a', 'model-a-v2', 'model-c']])
        self.assertEqual(ranks['harnesses'], [{'name': 'codex', 'accepted': 2}, {'name': 'cursor', 'accepted': 1}])
        self.assertNotIn('ip_key', json.dumps(status))
        self.assertNotIn('token_hash', json.dumps(status))

    def test_additive_migration_and_missing_metadata(self):
        token = self.helper.claim()
        self.assertEqual(self.submit(token, self.agent)[0], 200)
        with sqlite3.connect(self.helper.db) as conn:
            for column in ('model', 'harness', 'harness_version', 'agent_reported'):
                conn.execute(f'ALTER TABLE goldbach_leases DROP COLUMN {column}')
        for _ in range(2):
            migrated = Desk(self.helper.db, GAPS, b'test-secret')
            with migrated.transaction() as conn:
                row = conn.execute('SELECT model,harness,harness_version,agent_reported,pr,head FROM goldbach_leases').fetchone()
            self.assertEqual(tuple(row), ('unknown', 'unknown', 'unknown', 0, 8, 'a'*40))
        self.assertEqual(self.submit(token)[0], 200)


class SubmissionToolTests(unittest.TestCase):
    def setUp(self):
        folder = self.enterContext(tempfile.TemporaryDirectory())
        self.path = Path(folder)/'lease.json'
        self.state = dict(branch='task-branch', handle='alice', base='c'*40, token='private-lease', gap=dict(id='L-goldbach-test', file='lean/PEqualNP/Outside/Test.lean'))
        self.agent = dict(model='model-a', harness='codex', harness_version='unknown')
        pr = dict(state='open', user={'login':'alice'}, head={'sha':'a'*40}, base={'ref':'main','repo':{'full_name':goldbach.REPO,'default_branch':'main'}}, changed_files=1)
        self.command = self.enterContext(patch.object(goldbach, 'command', side_effect=lambda *args: json.dumps(pr) if args[:2]==('gh','api') else ('a'*40 if args[:2]==('git','rev-parse') else '')))
        self.enterContext(patch.object(goldbach,'current_branch',return_value='task-branch'))
        self.enterContext(patch.object(goldbach,'authenticated_login',return_value='alice'))
        self.enterContext(patch.object(goldbach.subprocess,'check_output',return_value='A\0'+self.state['gap']['file']+'\0'))
        self.desk = self.enterContext(patch.object(goldbach,'desk',return_value={'submitted':True}))
        self.comment = self.enterContext(patch.object(goldbach.subprocess,'run'))

    def test_submit_and_idempotent_retry(self):
        goldbach.submit(self.path,self.state,8,self.agent)
        self.assertEqual(self.desk.call_args.args[1]['agent'],self.agent)
        self.assertEqual(json.loads(self.path.read_text())['agent'],self.agent)
        goldbach.submit(self.path,self.state,8,self.agent)
        self.assertEqual(self.desk.call_count,1)
        self.assertEqual(self.comment.call_count,1)
        with self.assertRaises(SystemExit):
            goldbach.submit(self.path,self.state,8,dict(self.agent,model='other-model'))
        self.assertEqual(self.desk.call_count,1)

    def test_comment_retry_keeps_attribution_before_comment(self):
        self.comment.side_effect=RuntimeError('temporary comment failure')
        with self.assertRaises(RuntimeError):
            goldbach.submit(self.path,self.state,8,self.agent)
        saved=json.loads(self.path.read_text())
        self.assertEqual(saved['agent'],self.agent)
        self.assertEqual(saved['submitted_head'],'a'*40)
        self.comment.side_effect=None
        goldbach.submit(self.path,saved,8,self.agent)
        self.assertEqual(self.desk.call_count,2)
        self.assertEqual(self.desk.call_args_list[0].args[1],self.desk.call_args_list[1].args[1])


if __name__ == '__main__':
    unittest.main()
