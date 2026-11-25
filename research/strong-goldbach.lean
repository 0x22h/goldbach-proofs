import Mathlib

/-- The strong Goldbach conjecture as a proposition. -/
def StrongGoldbach : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- Positive prime-only log mass detects precisely the existence of a prime pair. -/
theorem strongGoldbach_iff_primeMass : StrongGoldbach ↔
    ∀ n : ℕ, 4 ≤ n → Even n →
      let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0
      0 < Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) := by
  let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0
  have pos {k : ℕ} (hk : Nat.Prime k) : 0 < w k := by
    simp only [w, if_pos hk]
    exact Real.log_pos (by exact_mod_cast hk.one_lt)
  have nn (k : ℕ) : 0 ≤ w k := by
    by_cases h : Nat.Prime k
    · exact (pos h).le
    · simp [w, h]
  constructor
  · intro h n hn he
    obtain ⟨p, q, hp, hq, hpq⟩ := h n hn he
    change 0 < ∑ i ∈ Finset.range (n+1), w i * w (n-i)
    have hm : p ∈ Finset.range (n+1) := Finset.mem_range.mpr (by omega)
    have hd : n-p = q := by omega
    have hpos : 0 < w (n-p) := by simpa only [hd] using pos hq
    exact lt_of_lt_of_le (mul_pos (pos hp) hpos)
      (Finset.single_le_sum (f := fun i => w i * w (n-i))
        (fun i _ => mul_nonneg (nn i) (nn (n-i))) hm)
  · intro h n hn he
    have hs := h n hn he
    change 0 < ∑ i ∈ Finset.range (n+1), w i * w (n-i) at hs
    by_contra noPair
    have hz : (∑ i ∈ Finset.range (n+1), w i * w (n-i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := Finset.mem_range.mp hi
      by_cases hp : Nat.Prime i
      · have hq : ¬ Nat.Prime (n-i) := fun hq => noPair ⟨i,n-i,hp,hq,by omega⟩
        simp [w,hq]
      · simp [w,hp]
    linarith

namespace GoldbachBudget
noncomputable section

private def w (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
private def phase (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
private def spec (n : ℕ) (a : ℕ → ℝ) (t : ℝ) :=
  ∑ k ∈ Finset.range (n+1), (a k : ℂ) * phase ((k:ℝ)*t)
private def arcs (n : ℕ) : Set ℝ :=
  let Q := (Nat.log 2 (n+2))^2
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))}
private def full (n : ℕ) (s : Set ℝ) : ℂ :=
  intervalIntegral (fun t => s.indicator
    (fun u => (spec n w u)^2 * phase (-(n:ℝ)*u)) t) 0 1 MeasureTheory.volume
private def pair (n : ℕ) (a b : ℕ → ℝ) : ℂ :=
  intervalIntegral (fun t => (arcs n)ᶜ.indicator
    (fun u => spec n a u * spec n b u * phase (-(n:ℝ)*u)) t) 0 1 MeasureTheory.volume
private def low (n k : ℕ) := if k^3 ≤ n then w k else 0
private def high (n k : ℕ) := w k - low n k
private def mass (n : ℕ) := ∑ p ∈ Finset.range (n+1), w p * w (n-p)

/-- Arithmetic inputs are hypotheses. The conclusion concerns the original frequency n. -/
theorem fixedToDyadic
    (coeff : ∀ n, full n (arcs n) + full n (arcs n)ᶜ = (mass n : ℂ))
    (major : ∃ M : ℕ, ∀ n ≥ M, Even n → (n:ℝ)/144 ≤ (full n (arcs n)).re)
    (split : ∀ n, pair n w w =
      pair n (low n) (low n) + 2*pair n (low n) (high n) + pair n (high n) (high n))
    (ll : ∀ e : ℝ, 0 < e → ∃ U : ℕ, ∀ n ≥ U, ‖pair n (low n) (low n)‖ ≤ e*(n:ℝ))
    (lh : ∀ e : ℝ, 0 < e → ∃ V : ℕ, ∀ n ≥ V, ‖pair n (low n) (high n)‖ ≤ e*(n:ℝ))
    (bulk : ∃ H : ℕ, ∀ n ≥ H, Even n → -(n:ℝ)/288 ≤ (pair n (high n) (high n)).re) :
    ∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X →
      Even n → c*(n:ℝ) ≤ mass n := by
  obtain ⟨M,hM⟩ := major
  obtain ⟨H,hH⟩ := bulk
  obtain ⟨U,hU⟩ := ll (1/2304) (by norm_num)
  obtain ⟨V,hV⟩ := lh (1/2304) (by norm_num)
  refine ⟨1/576, max (max M H) (max U V), by norm_num, ?_⟩
  intro X n hX hXn _ hn
  have bound {z : ℂ} {a : ℝ} (hz : ‖z‖ ≤ a) : -a ≤ z.re :=
    le_trans (neg_le_neg hz) (abs_le.mp (Complex.abs_re_le_norm z)).1
  have hm := hM n (by omega) hn
  have hh := hH n (by omega) hn
  have hll := bound (hU n (by omega))
  have hlh := bound (hV n (by omega))
  have eqminor : full n (arcs n)ᶜ = pair n w w := by simp only [full, pair, pow_two]
  have eqc := coeff n
  rw [eqminor, split n, two_mul] at eqc
  have hr := congrArg Complex.re eqc
  simp only [Complex.add_re, Complex.ofReal_re] at hr
  linarith only [hr, hm, hh, hll, hlh, Nat.cast_nonneg (α := ℝ) n]

private def K (n : ℕ) (t : ℝ) : ℝ :=
  let L := max 1 (Nat.log 2 n / 2)
  (∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L:ℝ)
private def J (n : ℕ) (v : ℝ → ℝ) :=
  (intervalIntegral (fun t => (arcs n)ᶜ.indicator
    (fun u => (v u:ℂ)*spec n (high n) u*spec n (high n) u*phase (-(n:ℝ)*u)) t)
    0 1 MeasureTheory.volume).re

private theorem measurableArcs (n : ℕ) : MeasurableSet (arcs n) := by
  let Q := (Nat.log 2 (n+2))^2
  let Index := {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2 ≤ p.1 ∧ p.2.Coprime p.1}
  have cover : arcs n = ⋃ i : Index,
      {t : ℝ | |t-(i.val.2:ℝ)/(i.val.1:ℝ)| ≤ (Q:ℝ)/((i.val.1:ℝ)*(n:ℝ))} := by
    ext t
    constructor
    · rintro ⟨q,a,hq,hQ,ha,hc,ht⟩
      exact Set.mem_iUnion.mpr ⟨⟨(q,a),hq,hQ,ha,hc⟩,ht⟩
    · intro ht
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ht
      exact ⟨i.val.1,i.val.2,i.property.1,i.property.2.1,i.property.2.2.1,i.property.2.2.2,hi⟩
  rw [cover]
  exact MeasurableSet.iUnion fun _ =>
    (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const).measurableSet

private def kernelIntegrand (n : ℕ) (v : ℝ → ℝ) (t : ℝ) :=
  (arcs n)ᶜ.indicator
    (fun u => (v u:ℂ)*spec n (high n) u*spec n (high n) u*phase (-(n:ℝ)*u)) t

private theorem kernelIntegrable (n : ℕ) (v : ℝ → ℝ) (hv : Continuous v) :
    IntervalIntegrable (kernelIntegrand n v) MeasureTheory.volume (0:ℝ) 1 := by
  have cont : Continuous (fun u : ℝ => (v u:ℂ)*spec n (high n) u*spec n (high n) u*phase (-(n:ℝ)*u)) := by
    unfold spec phase
    fun_prop
  have h := cont.intervalIntegrable (μ := MeasureTheory.volume) 0 1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h ⊢
  exact h.indicator (measurableArcs n).compl

theorem packetPartition (n : ℕ) :
    (pair n (high n) (high n)).re = J n (K n) + J n (fun t => 1-K n t) := by
  let F := fun t : ℝ => spec n (high n) t * spec n (high n) t * phase (-(n:ℝ)*t)
  let T := kernelIntegrand n
  have hK : Continuous (K n) := by unfold K; fun_prop
  have partition : (fun t => (arcs n)ᶜ.indicator F t) =
      fun t => T (K n) t + T (fun u => 1-K n u) t := by
    funext t
    by_cases ht : t ∈ (arcs n)ᶜ
    · simp only [F, T, kernelIntegrand, Set.indicator_of_mem ht, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    · simp [T, kernelIntegrand, ht]
  unfold pair J
  change (intervalIntegral (fun t => (arcs n)ᶜ.indicator F t) 0 1 MeasureTheory.volume).re = _
  have hD : Continuous (fun t : ℝ => 1 - K n t) := continuous_const.sub hK
  rw [partition, intervalIntegral.integral_add (kernelIntegrable n (K n) hK)
    (kernelIntegrable n (fun t => 1 - K n t) hD)] <;> rfl

private def cutoff (n : ℕ) : ℝ := 1 / (2304 * (1 + (Real.log (n:ℝ))^2))
private def small (n : ℕ) (t : ℝ) :=
  max (-(cutoff n)) (min (cutoff n) (1 - K n t))
private def rest (n : ℕ) (t : ℝ) := 1 - K n t - small n t

theorem restZero (n : ℕ) (t : ℝ) (h : |1-K n t| ≤ cutoff n) : rest n t = 0 := by
  rcases abs_le.mp h with ⟨hl,hu⟩
  simp only [rest, small, min_eq_right hu, max_eq_right hl, sub_self]

private theorem defectSplit (n : ℕ) :
    J n (fun t => 1-K n t) = J n (small n) + J n (rest n) := by
  have hk : Continuous (K n) := by unfold K; fun_prop
  have hd : Continuous (fun t : ℝ => 1-K n t) := continuous_const.sub hk
  have hs : Continuous (small n) := continuous_const.max (continuous_const.min hd)
  have hr : Continuous (rest n) := hd.sub hs
  have hsum : kernelIntegrand n (fun t => 1-K n t) = fun t =>
      kernelIntegrand n (small n) t + kernelIntegrand n (rest n) t := by
    funext t
    by_cases ht : t ∈ (arcs n)ᶜ
    · simp only [kernelIntegrand, Set.indicator_of_mem ht, rest, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    · simp [kernelIntegrand, ht]
  change (intervalIntegral (kernelIntegrand n _) 0 1 MeasureTheory.volume).re = _
  rw [hsum, intervalIntegral.integral_add (kernelIntegrable n _ hs) (kernelIntegrable n _ hr)] <;> rfl

private theorem energyControl {n : ℕ} {a : ℝ} (ha : 0 ≤ a) {v : ℝ → ℝ}
    (hv : ∀ t, |v t| ≤ a) :
    |J n v| ≤ a * intervalIntegral (fun t => ‖spec n (high n) t‖^2) 0 1 MeasureTheory.volume := by
  have hp (x : ℝ) : ‖phase x‖ = 1 := by simp [phase, Complex.norm_exp]
  have pt (t : ℝ) : ‖kernelIntegrand n v t‖ ≤ a * ‖spec n (high n) t‖^2 := by
    by_cases ht : t ∈ (arcs n)ᶜ
    · simp only [kernelIntegrand, Set.indicator_of_mem ht, norm_mul, hp, mul_one, Complex.norm_real,
        Real.norm_eq_abs, pow_two, ← mul_assoc]
      gcongr
      exact hv t
    · simpa [kernelIntegrand, ht] using mul_nonneg ha (sq_nonneg ‖spec n (high n) t‖)
  have hc : Continuous (fun t : ℝ => a * ‖spec n (high n) t‖^2) := by unfold spec phase; fun_prop
  have hi := intervalIntegral.norm_integral_le_of_norm_le
    (f := kernelIntegrand n v) (by norm_num : (0:ℝ) ≤ 1)
    (Filter.Eventually.of_forall fun t _ => pt t) (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
  rw [intervalIntegral.integral_const_mul] at hi
  exact (Complex.abs_re_le_norm _).trans hi

theorem clippedBound
    (energy : ∀ n : ℕ, 2 ≤ n → intervalIntegral (fun t => ‖spec n (high n) t‖^2)
      0 1 MeasureTheory.volume ≤ ((n:ℝ)+1)*(Real.log (n:ℝ))^2) :
    ∀ n : ℕ, 2 ≤ n → |J n (small n)| ≤ (n:ℝ)/1152 := by
  intro n hn
  have ht : 0 ≤ cutoff n := by unfold cutoff; positivity
  have cap (t : ℝ) : |small n t| ≤ cutoff n := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  apply (energyControl ht cap).trans
  apply (mul_le_mul_of_nonneg_left (energy n hn) ht).trans
  unfold cutoff
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hlog := sq_nonneg (Real.log (n:ℝ))
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr (show (1:ℝ) ≤ n by linarith)) hlog]

theorem restToDefect
    (cap : ∀ n : ℕ, 2 ≤ n → |J n (small n)| ≤ (n:ℝ)/1152)
    (far : ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/1152 ≤ J n (rest n)) :
    ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/576 ≤ J n (fun t => 1-K n t) := by
  obtain ⟨N,hN⟩ := far
  refine ⟨max 2 N, ?_⟩
  intro n hn he
  rw [defectSplit]
  linarith only [(abs_le.mp (cap n (by omega))).1, hN n (by omega) he]

theorem packetToBulk
    (packet : ∃ P : ℕ, ∀ n ≥ P, Even n → -(n:ℝ)/576 ≤ J n (K n))
    (defect : ∃ D : ℕ, ∀ n ≥ D, Even n → -(n:ℝ)/576 ≤ J n (fun t => 1-K n t))
    (split : ∀ n, (pair n (high n) (high n)).re = J n (K n) + J n (fun t => 1-K n t)) :
    ∃ H : ℕ, ∀ n ≥ H, Even n → -(n:ℝ)/288 ≤ (pair n (high n) (high n)).re := by
  obtain ⟨P,hP⟩ := packet
  obtain ⟨D,hD⟩ := defect
  refine ⟨max P D, ?_⟩
  intro n hn he
  rw [split]
  linarith only [hP n (by omega) he, hD n (by omega) he]

/-- The clipping loss is dominated by half the energy on the actual resonant minor arcs. -/
theorem capComparison (n : ℕ) :
    let B := {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}
    J n (fun t => min (K n t) (1/2)) -
        intervalIntegral (B.indicator (fun t => ‖spec n (high n) t‖^2)) 0 1 MeasureTheory.volume / 2
      ≤ J n (K n) := by
  let B := {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}
  let cap := fun t => min (K n t) (1/2)
  let excess := fun t => K n t - cap t
  let energy := fun t : ℝ => ‖spec n (high n) t‖^2
  have hk : Continuous (K n) := by unfold K; fun_prop
  have hc : Continuous cap := hk.min continuous_const
  have he : Continuous excess := hk.sub hc
  have hB : MeasurableSet B := by
    change MeasurableSet ((arcs n)ᶜ ∩ {t : ℝ | (1:ℝ)/2 < K n t})
    exact (measurableArcs n).compl.inter
      (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)/2)) hk).measurableSet
  have henergy : Continuous energy := by unfold energy spec phase; fun_prop
  have hmask : IntervalIntegrable (B.indicator energy) MeasureTheory.volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (henergy.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator hB
  have hKle (t : ℝ) : K n t ≤ 1 := by
    let L := max 1 (Nat.log 2 n / 2)
    have hL : 0 < L := by dsimp [L]; omega
    change (∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L:ℝ) ≤ 1
    apply (div_le_iff₀ (by exact_mod_cast hL : (0:ℝ) < L)).mpr
    calc
      _ ≤ ∑ _j ∈ Finset.range L, (1:ℝ) := Finset.sum_le_sum fun _ _ => Real.cos_le_one _
      _ = _ := by simp
  have unit (x : ℝ) : ‖phase x‖ = 1 := by simp [phase, Complex.norm_exp]
  have pt (t : ℝ) : ‖kernelIntegrand n excess t‖ ≤ (1/2:ℝ) * B.indicator energy t := by
    by_cases hm : t ∈ (arcs n)ᶜ
    · by_cases hp : (1:ℝ)/2 < K n t
      · have hb : t ∈ B := ⟨hm,hp⟩
        have hx : |excess t| ≤ 1/2 := by
          simp only [excess, cap, min_eq_right hp.le, abs_of_nonneg (sub_nonneg.mpr hp.le)]
          linarith [hKle t]
        simp only [kernelIntegrand, Set.indicator_of_mem hm, Set.indicator_of_mem hb, norm_mul,
          unit, mul_one, Complex.norm_real, Real.norm_eq_abs, energy, pow_two, ← mul_assoc]
        gcongr <;> exact hx
      · have hb : t ∉ B := fun h => hp h.2
        have hz : excess t = 0 := by
          change K n t - min (K n t) (1/2) = 0
          rw [min_eq_left (le_of_not_gt hp), sub_self]
        simp [kernelIntegrand, hm, hb, hz]
    · have hb : t ∉ B := fun h => hm h.1
      simp [kernelIntegrand, hm, hb]
  have hi := intervalIntegral.norm_integral_le_of_norm_le
    (f := kernelIntegrand n excess) (by norm_num : (0:ℝ) ≤ 1)
    (Filter.Eventually.of_forall fun t _ => pt t) (hmask.const_mul (1/2:ℝ))
  rw [intervalIntegral.integral_const_mul] at hi
  have bound := (Complex.abs_re_le_norm _).trans hi
  have add : kernelIntegrand n (K n) = fun t => kernelIntegrand n cap t + kernelIntegrand n excess t := by
    funext t
    by_cases ht : t ∈ (arcs n)ᶜ
    · simp only [kernelIntegrand, Set.indicator_of_mem ht, excess, Complex.ofReal_sub]
      ring
    · simp [kernelIntegrand, ht]
  have eqSum : J n (K n) = J n cap + J n excess := by
    change (intervalIntegral (kernelIntegrand n (K n)) 0 1 MeasureTheory.volume).re = _
    rw [add, intervalIntegral.integral_add (kernelIntegrable n _ hc) (kernelIntegrable n _ he)]
    rfl
  change J n cap - intervalIntegral (B.indicator energy) 0 1 MeasureTheory.volume / 2 ≤ J n (K n)
  change |J n excess| ≤ _ at bound
  rw [eqSum]
  linarith only [(abs_le.mp bound).1]

/-- Compare two exact lag expansions on a common mask before using the budgets. -/
theorem energyFromLags {U short long : ℕ → (ℕ → ℝ) → ℝ}
    (expand : ∀ n a, U n a = short n a + long n a)
    (wheel : ∃ N : ℕ, ∀ n ≥ N, Even n →
      U n (fun k => if Nat.Coprime k 30 then (30:ℝ)/8 else 0) ≤ (n:ℝ)/2304)
    (near : ∃ N : ℕ, ∀ n ≥ N, Even n →
      |short n (high n) - short n (fun k => if Nat.Coprime k 30 then (30:ℝ)/8 else 0)| ≤ (n:ℝ)/2304)
    (far : ∃ N : ℕ, ∀ n ≥ N, Even n →
      long n (high n) - long n (fun k => if Nat.Coprime k 30 then (30:ℝ)/8 else 0) ≤ (n:ℝ)/1152) :
    ∃ N : ℕ, ∀ n ≥ N, Even n → U n (high n) ≤ (n:ℝ)/576 := by
  obtain ⟨A,hA⟩ := wheel
  obtain ⟨B,hB⟩ := near
  obtain ⟨C,hC⟩ := far
  refine ⟨max A (max B C), ?_⟩
  intro n hn he
  have hw := hA n (by omega) he
  rw [expand] at hw ⊢
  linarith only [hw, (abs_le.mp (hB n (by omega) he)).2, hC n (by omega) he]

/-- A signed capped-packet floor and a positive masked-energy cap suffice. -/
theorem packetFromCapped {U : ℕ → ℝ}
    (cap : ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/1152 ≤ J n (fun t => min (K n t) (1/2)))
    (energy : ∃ N : ℕ, ∀ n ≥ N, Even n → U n ≤ (n:ℝ)/576)
    (compareCap : ∀ n, J n (fun t => min (K n t) (1/2)) - U n/2 ≤ J n (K n)) :
    ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/576 ≤ J n (K n) := by
  obtain ⟨A,hA⟩ := cap
  obtain ⟨B,hB⟩ := energy
  refine ⟨max A B, ?_⟩
  intro n hn he
  linarith only [hA n (by omega) he, hB n (by omega) he, compareCap n]

/-- The finite certificate must reach the very threshold supplied by the analytic bounds. -/
theorem completeAtCommonCutoff (N : ℕ) (c : ℝ) (hc : 0 < c)
    (prefixMass : ∀ n : ℕ, 4 ≤ n → n < N → Even n → 0 < mass n)
    (tailMass : ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X → Even n → c*(n:ℝ) ≤ mass n) :
    StrongGoldbach := by
  apply strongGoldbach_iff_primeMass.mpr
  intro n hn he
  change 0 < mass n
  by_cases h : n < N
  · exact prefixMass n hn h he
  · exact lt_of_lt_of_le (mul_pos hc (by exact_mod_cast (show 0 < n by omega)))
      (tailMass n n (by omega) le_rfl (by omega) he)

end
end GoldbachBudget

namespace GoldbachPacket
noncomputable section

private theorem pairHalves (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in (0:ℝ)..1, f t) = ∫ t in (0:ℝ)..(1/2), f t + f (t+1/2) := by
  have hs : Continuous (fun t : ℝ => f (t+1/2)) := hf.comp (continuous_id.add continuous_const)
  rw [intervalIntegral.integral_add (hf.intervalIntegrable ..) (hs.intervalIntegrable ..),
    intervalIntegral.integral_comp_add_right]
  norm_num only [zero_add, show (1/2:ℝ)+1/2 = 1 by norm_num]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)).symm

private theorem scaleHalf (g : ℝ → ℝ) :
    (∫ t in (0:ℝ)..(1/2), g (2*t)) = (1/2) * ∫ t in (0:ℝ)..1, g t := by
  rw [intervalIntegral.integral_comp_mul_left g (by norm_num : (2:ℝ) ≠ 0)]
  norm_num

private theorem doublePeriod (g : ℝ → ℝ) (hc : Continuous g) (hp : Function.Periodic g 1) :
    (∫ t in (0:ℝ)..1, g (2*t)) = ∫ t in (0:ℝ)..1, g t := by
  have hd : Continuous (fun t : ℝ => g (2*t)) := hc.comp (continuous_const.mul continuous_id)
  rw [pairHalves _ hd]
  simp only [show ∀ t : ℝ, 2*(t+1/2) = 2*t+1 by intro t; ring, show ∀ y : ℝ, g (y+1) = g y from hp]
  rw [intervalIntegral.integral_add (hd.intervalIntegrable ..) (hd.intervalIntegrable ..), scaleHalf]
  ring

/-- The two inverse branches of doubling give opposite first cosines and the same remaining weight. -/
theorem doublingTilt (s : ℝ) (g : ℝ → ℝ) (hg : Continuous g)
    (hp : Function.Periodic g 1) (hn : ∀ t, 0 ≤ g t) :
    (∫ t in (0:ℝ)..1, Real.exp (s*Real.cos (2*Real.pi*t))*g (2*t)) ≤
      Real.cosh s * ∫ t in (0:ℝ)..1, g t := by
  let f := fun t : ℝ => Real.exp (s*Real.cos (2*Real.pi*t))*g (2*t)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hs : Continuous (fun t : ℝ => f (t+1/2)) := hf.comp (continuous_id.add continuous_const)
  have hd : Continuous (fun t : ℝ => (2*Real.cosh s)*g (2*t)) := by fun_prop
  change (∫ t in (0:ℝ)..1, f t) ≤ _
  rw [pairHalves f hf]
  calc
    _ ≤ ∫ t in (0:ℝ)..(1/2), (2*Real.cosh s)*g (2*t) := by
      apply intervalIntegral.integral_mono_on (by norm_num) ((hf.add hs).intervalIntegrable ..)
        (hd.intervalIntegrable ..)
      intro t _
      have hcos : Real.cosh (s*Real.cos (2*Real.pi*t)) ≤ Real.cosh s := by
        apply Real.cosh_le_cosh.mpr
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (abs_le.mpr
          ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) (abs_nonneg s)).trans_eq (mul_one _)
      change Real.exp (s*Real.cos (2*Real.pi*t))*g (2*t) +
        Real.exp (s*Real.cos (2*Real.pi*(t+1/2)))*g (2*(t+1/2)) ≤ _
      rw [show 2*Real.pi*(t+1/2) = 2*Real.pi*t+Real.pi by ring, Real.cos_add_pi,
        show 2*(t+1/2) = 2*t+1 by ring, hp (2*t), mul_neg, ← add_mul]
      rw [Real.cosh_eq] at hcos
      exact mul_le_mul_of_nonneg_right (by linarith) (hn _)
    _ = _ := by rw [intervalIntegral.integral_const_mul, scaleHalf]; ring

private def series (m : ℕ) (t : ℝ) := ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^j*t)
private def packet (m : ℕ) (t : ℝ) := ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)

private theorem periodSeries (m : ℕ) : Function.Periodic (series m) 1 := by
  intro t
  unfold series
  apply Finset.sum_congr rfl
  intro j _
  have heq : 2*Real.pi*(2:ℝ)^j*(t+1) = 2*Real.pi*(2:ℝ)^j*t + ((2^j:ℕ):ℝ)*(2*Real.pi) := by
    push_cast
    ring
  rw [heq, Real.cos_add_nat_mul_two_pi]

private theorem seriesSucc (m : ℕ) (t : ℝ) :
    series (m+1) t = Real.cos (2*Real.pi*t) + series m (2*t) := by
  unfold series
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  rw [add_comm (∑ j ∈ Finset.range m, _) _]
  apply congrArg (fun u : ℝ => Real.cos (2*Real.pi*t) + u)
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [pow_succ]
  ring

/-- Laplace transform of the actual unnormalised real packet, starting at frequency two. -/
theorem exponentialMoment (m : ℕ) (s : ℝ) :
    (∫ t in (0:ℝ)..1, Real.exp (s*packet m t)) ≤ (Real.cosh s)^m := by
  have hc (k : ℕ) : Continuous (fun t => Real.exp (s*series k t)) := by unfold series; fun_prop
  have hp (k : ℕ) : Function.Periodic (fun t => Real.exp (s*series k t)) 1 :=
    fun t => congrArg (fun u : ℝ => Real.exp (s*u)) (periodSeries k t)
  have h (k : ℕ) : (∫ t in (0:ℝ)..1, Real.exp (s*series k t)) ≤ (Real.cosh s)^k := by
    induction k with
    | zero => simp [series]
    | succ k ih =>
      simp only [seriesSucc, mul_add, Real.exp_add]
      exact (doublingTilt s _ (hc k) (hp k) (fun t => (Real.exp_pos _).le)).trans
        ((mul_le_mul_of_nonneg_left ih (Real.cosh_pos _).le).trans_eq (pow_succ' ..).symm)
  have shift (t : ℝ) : packet m t = series m (2*t) := by
    unfold packet series
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [pow_succ]
    ring
  simp only [shift]
  exact (doublePeriod _ (hc m) (hp m)).le.trans (h m)

/-- Exponential Markov at s=1/2, for the one-sided real exceptional set. -/
theorem upperTail (m : ℕ) (_hm : 0 < m) :
    (∫ t in (0:ℝ)..1, if (m:ℝ)/2 < packet m t then (1:ℝ) else 0) ≤ Real.exp (-(m:ℝ)/8) := by
  let A := {t : ℝ | (m:ℝ)/2 < packet m t}
  have hc : Continuous (packet m) := by unfold packet; fun_prop
  have hA : MeasurableSet A :=
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (m:ℝ)/2)) hc).measurableSet
  have hi : IntervalIntegrable (A.indicator (fun _ => (1:ℝ))) MeasureTheory.volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (intervalIntegrable_const : IntervalIntegrable (fun _ => (1:ℝ)) MeasureTheory.volume 0 1)).indicator hA
  have he : Continuous (fun t : ℝ => Real.exp (-(m:ℝ)/4) * Real.exp ((1/2)*packet m t)) := by fun_prop
  change (∫ t in (0:ℝ)..1, A.indicator (fun _ => (1:ℝ)) t) ≤ _
  calc
    _ ≤ ∫ t in (0:ℝ)..1, Real.exp (-(m:ℝ)/4) * Real.exp ((1/2)*packet m t) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hi (he.intervalIntegrable ..)
      intro t _
      rw [← Real.exp_add]
      by_cases ht : t ∈ A
      · rw [Set.indicator_of_mem ht]
        change (m:ℝ)/2 < packet m t at ht
        exact (Real.one_le_exp_iff.mpr (by linarith))
      · rw [Set.indicator_of_notMem ht]
        exact (Real.exp_pos _).le
    _ ≤ Real.exp (-(m:ℝ)/4) * (Real.cosh (1/2))^m := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (exponentialMoment m (1/2)) (Real.exp_pos _).le
    _ ≤ Real.exp (-(m:ℝ)/4) * (Real.exp (1/8))^m := by
      have hs := Real.cosh_le_exp_half_sq (1/2)
      norm_num at hs
      gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

private def length (n : ℕ) := max 1 (Nat.log 2 n / 2)
private def resonant (n : ℕ) := {t : ℝ | t ∉ GoldbachBudget.arcs n ∧
  (1:ℝ)/2 < packet (length n) t / (length n:ℝ)}

private theorem maskedArea (n : ℕ) :
    (∫ t in (0:ℝ)..1, (resonant n).indicator (fun _ => (1:ℝ)) t) ≤
      Real.exp (-(length n:ℝ)/8) := by
  let m := length n
  have hm : 0 < m := by dsimp [m, length]; omega
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  let A := {t : ℝ | (m:ℝ)/2 < packet m t}
  have hc : Continuous (packet m) := by unfold packet; fun_prop
  have hA : MeasurableSet A :=
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (m:ℝ)/2)) hc).measurableSet
  have heq : resonant n = (GoldbachBudget.arcs n)ᶜ ∩ A := by
    ext t
    change (_ ∧ (1:ℝ)/2 < packet m t / (m:ℝ)) ↔ (_ ∧ (m:ℝ)/2 < packet m t)
    rw [lt_div_iff₀ hmr, show (1:ℝ)/2*(m:ℝ) = (m:ℝ)/2 by ring] <;> rfl
  have integ {s : Set ℝ} (hs : MeasurableSet s) :
      IntervalIntegrable (s.indicator (fun _ => (1:ℝ))) MeasureTheory.volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (intervalIntegrable_const : IntervalIntegrable (fun _ => (1:ℝ)) MeasureTheory.volume 0 1)).indicator hs
  rw [heq]
  apply le_trans _ (upperTail m hm)
  change (∫ t in (0:ℝ)..1, ((GoldbachBudget.arcs n)ᶜ ∩ A).indicator (fun _ => (1:ℝ)) t) ≤
    ∫ t in (0:ℝ)..1, A.indicator (fun _ => (1:ℝ)) t
  apply intervalIntegral.integral_mono_on (by norm_num)
    (integ ((GoldbachBudget.measurableArcs n).compl.inter hA)) (integ hA)
  intro t _
  by_cases ht : t ∈ A <;> by_cases hs : t ∈ (GoldbachBudget.arcs n)ᶜ <;> simp [ht,hs]

/-- The real one-sided exception remains small after multiplying by any fixed log power. -/
theorem maskLogDecay (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, (1+Real.log (n:ℝ))^d *
      (∫ t in (0:ℝ)..1, (resonant n).indicator (fun _ => (1:ℝ)) t) ≤ ε := by
  have ht : Filter.Tendsto (fun x : ℝ => x^d * Real.exp (-(1/8:ℝ)*x))
      Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d:ℝ) (1/8) (by norm_num)
  have hε' : 0 < ε/(5:ℝ)^d := by positivity
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const hε')
  obtain ⟨M,hM⟩ := exists_nat_ge R
  refine ⟨max 1 (2^(2*M)), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hlog := Nat.le_log_of_pow_le (by decide : 1 < 2) (show 2^(2*M) ≤ n by omega)
  have hl1 : 1 ≤ length n := le_max_left _ _
  have hlM : M ≤ length n := by unfold length; omega
  have htM := hR (length n:ℝ) (hM.trans (by exact_mod_cast hlM))
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hx : (n:ℝ) < (2:ℝ)^((Nat.log 2 n)+1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1<2) n
  have hln := Real.log_le_log hn0 hx.le
  rw [Real.log_pow] at hln
  have hceil : Nat.log 2 n + 1 ≤ 2*length n+2 := by unfold length; omega
  have hrceil : ((Nat.log 2 n + 1:ℕ):ℝ) ≤ 2*(length n:ℝ)+2 := by exact_mod_cast hceil
  have ht2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hpoly : 1+Real.log (n:ℝ) ≤ 5*(length n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left ht2 (Nat.cast_nonneg (α := ℝ) (Nat.log 2 n + 1))
    have hl : (1:ℝ) ≤ length n := by exact_mod_cast hl1
    linarith
  have hnon : 0 ≤ 1+Real.log (n:ℝ) := by linarith [Real.log_nonneg (show (1:ℝ) ≤ n by exact_mod_cast hn1)]
  calc
    _ ≤ (1+Real.log (n:ℝ))^d * Real.exp (-(length n:ℝ)/8) :=
      mul_le_mul_of_nonneg_left (maskedArea n) (pow_nonneg hnon _)
    _ ≤ (5*(length n:ℝ))^d * Real.exp (-(length n:ℝ)/8) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnon hpoly _) (Real.exp_pos _).le
    _ ≤ ε := by
      rw [mul_pow, mul_assoc, show -(length n:ℝ)/8 = -(1/8:ℝ)*(length n:ℝ) by ring]
      have hh := (lt_div_iff₀ (by positivity : 0 < (5:ℝ)^d)).mp htM
      linarith only [hh]

private def cosineMoment (n h : ℕ) :=
  ∫ t in (0:ℝ)..1, (resonant n).indicator (fun u => Real.cos (2*Real.pi*(h:ℝ)*u)) t
private def correlation (n h : ℕ) (a : ℕ → ℝ) :=
  ∑ k ∈ Finset.range (n+1-h), a k * a (k+h)
private def shortPart (n : ℕ) (a : ℕ → ℝ) :=
  correlation n 0 a * cosineMoment n 0 + 2 * ∑ h ∈ Finset.Icc 1 (min n ((length n)^2)),
    correlation n h a * cosineMoment n h
private def wheel (k : ℕ) := if Nat.Coprime k 30 then (30:ℝ)/8 else 0

private theorem zeroMoment (n : ℕ) :
    cosineMoment n 0 = ∫ t in (0:ℝ)..1, (resonant n).indicator (fun _ => (1:ℝ)) t := by
  simp [cosineMoment]

private theorem cosineMomentBound (n h : ℕ) : |cosineMoment n h| ≤ cosineMoment n 0 := by
  have hc : Continuous (fun t => packet (length n) t / (length n:ℝ)) := by unfold packet; fun_prop
  have hm : MeasurableSet (resonant n) := (GoldbachBudget.measurableArcs n).compl.inter
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)/2)) hc).measurableSet
  have hi : IntervalIntegrable ((resonant n).indicator (fun _ => (1:ℝ))) MeasureTheory.volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (intervalIntegrable_const : IntervalIntegrable (fun _ => (1:ℝ)) MeasureTheory.volume 0 1)).indicator hm
  rw [zeroMoment, cosineMoment]
  change ‖∫ t in (0:ℝ)..1, (resonant n).indicator (fun u => Real.cos (2*Real.pi*(h:ℝ)*u)) t‖ ≤ _
  apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num) _ hi
  apply Filter.Eventually.of_forall
  intro t _
  by_cases ht : t ∈ resonant n
  · simpa [ht, Real.norm_eq_abs] using (abs_le.mpr
      ⟨Real.neg_one_le_cos (2*Real.pi*(h:ℝ)*t), Real.cos_le_one _⟩)
  · simp [ht]

private theorem correlationBound (n h : ℕ) (a : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ k ≤ n, |a k| ≤ M) : |correlation n h a| ≤ ((n:ℝ)+1)*M^2 := by
  unfold correlation
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range (n+1-h), M^2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [abs_mul, pow_two]
      exact mul_le_mul (ha k (by omega)) (ha (k+h) (by omega)) (abs_nonneg _) hM
    _ = ((n+1-h:ℕ):ℝ) * M^2 := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg M)
      exact_mod_cast Nat.sub_le (n+1) h

/-- Include lag zero once and each positive lag twice, even if the cutoff exceeds n. -/
theorem shortEnvelope (n : ℕ) (a : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (ha : ∀ k ≤ n, |a k| ≤ M) :
    |shortPart n a| ≤ (1+2*(length n:ℝ)^2)*((n:ℝ)+1)*M^2*cosineMoment n 0 := by
  let H := min n ((length n)^2)
  let B := ((n:ℝ)+1)*M^2*cosineMoment n 0
  have hm0 : 0 ≤ cosineMoment n 0 := (abs_nonneg _).trans (cosineMomentBound n 0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have each (h : ℕ) : |correlation n h a * cosineMoment n h| ≤ B := by
    rw [abs_mul]
    exact mul_le_mul (correlationBound n h a M hM ha) (cosineMomentBound n h) (abs_nonneg _) (by positivity)
  have hs : |∑ h ∈ Finset.Icc 1 H, correlation n h a * cosineMoment n h| ≤ (length n:ℝ)^2*B := by
    calc
      _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _h ∈ Finset.Icc 1 H, B := Finset.sum_le_sum fun h _ => each h
      _ = (H:ℝ)*B := by simp [Nat.card_Icc]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hB
        exact_mod_cast (min_le_right n ((length n)^2))
  unfold shortPart
  apply (abs_add_le ..).trans
  rw [abs_mul (2:ℝ), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  calc
    _ ≤ B + 2*((length n:ℝ)^2*B) := add_le_add (each 0) (by linarith only [hs])
    _ = _ := by dsimp [B]; ring

/-- From n=8 onward the cutoff removes the only even prime. Both lag sequences vanish at odd indices. -/
theorem evenLagSupport (n : ℕ) (hn : 8 ≤ n) (h : ℕ) (hh : Odd h) :
    correlation n h (GoldbachBudget.high n) = 0 ∧ correlation n h wheel = 0 := by
  have highEven (k : ℕ) (hk : k % 2 = 0) : GoldbachBudget.high n k = 0 := by
    by_cases hp : Nat.Prime k
    · have heq := hp.eq_two_or_odd.resolve_right (by omega)
      subst k
      have hcut : 2^3 ≤ n := by omega
      simp only [GoldbachBudget.high, GoldbachBudget.low, if_pos hcut, sub_self]
    · simp [GoldbachBudget.high, GoldbachBudget.low, GoldbachBudget.w, hp]
  have wheelEven (k : ℕ) (hk : k % 2 = 0) : wheel k = 0 := by
    have hnc : ¬Nat.Coprime k 30 := by
      intro hcop
      have hd := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hk) (by decide : 2 ∣ 30)
      rw [hcop.gcd_eq_one] at hd
      norm_num at hd
    simp [wheel, hnc]
  have zero (a : ℕ → ℝ) (ha : ∀ k, k % 2 = 0 → a k = 0) : correlation n h a = 0 := by
    unfold correlation
    apply Finset.sum_eq_zero
    intro k _
    obtain ⟨j,hj⟩ := hh
    by_cases hk : k % 2 = 0
    · rw [ha k hk, zero_mul]
    · rw [ha (k+h) (by omega), mul_zero]
  exact ⟨zero _ highEven, zero _ wheelEven⟩

private theorem lengthUpper (n : ℕ) (hn : 1 ≤ n) : (length n:ℝ) ≤ 2*(1+Real.log (n:ℝ)) := by
  have he : (2:ℝ)^(Nat.log 2 n) ≤ (n:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hl := Real.log_le_log (by positivity : 0 < (2:ℝ)^(Nat.log 2 n)) he
  rw [Real.log_pow] at hl
  have half : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hnat : length n ≤ Nat.log 2 n + 1 := by unfold length; omega
  have hr : (length n:ℝ) ≤ (Nat.log 2 n:ℝ) + 1 := by exact_mod_cast hnat
  linarith [mul_le_mul_of_nonneg_left half (Nat.cast_nonneg (α := ℝ) (Nat.log 2 n))]

/-- The sublinear estimate is uniform over all bounded weights at the prime logarithmic scale. -/
private theorem shortAtLogScale (n : ℕ) (hn : 1 ≤ n) (a : ℕ → ℝ)
    (ha : ∀ k ≤ n, |a k| ≤ 4*(1+Real.log (n:ℝ))) :
    |shortPart n a| ≤ 288*(n:ℝ)*(1+Real.log (n:ℝ))^4*cosineMoment n 0 := by
  let x := 1+Real.log (n:ℝ)
  have hx : 1 ≤ x := by dsimp [x]; linarith [Real.log_nonneg (by exact_mod_cast hn : (1:ℝ) ≤ n)]
  have hl : (length n:ℝ) ≤ 2*x := lengthUpper n hn
  have hl2 : (length n:ℝ)^2 ≤ (2*x)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hl 2
  have hf : 1+2*(length n:ℝ)^2 ≤ 9*x^2 := by nlinarith [sq_nonneg (x-1)]
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : 0 ≤ cosineMoment n 0 := (abs_nonneg _).trans (cosineMomentBound n 0)
  apply (shortEnvelope n a (4*x) (by linarith) ha).trans
  calc
    _ ≤ (9*x^2)*(2*(n:ℝ))*(4*x)^2*cosineMoment n 0 := by
      gcongr <;> linarith
    _ = _ := by change _ = 288*(n:ℝ)*x^4*cosineMoment n 0; ring

/-- Both absolute short pieces are sublinear, so their difference is sublinear for every n. -/
theorem shortWheelSublinear (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, |shortPart n (GoldbachBudget.high n) - shortPart n wheel| ≤ ε*(n:ℝ) := by
  obtain ⟨N,hN⟩ := maskLogDecay 4 (ε/576) (by positivity)
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  let M := 4*(1+Real.log (n:ℝ))
  have hpr (k : ℕ) (hk : k ≤ n) : |GoldbachBudget.high n k| ≤ M := by
    unfold GoldbachBudget.high GoldbachBudget.low
    by_cases hl : k^3 ≤ n
    · simp [hl]; dsimp [M]; linarith
    · simp only [hl, if_false, sub_zero, GoldbachBudget.w]
      by_cases hp : Nat.Prime k
      · have hpos : (1:ℝ) ≤ k := by exact_mod_cast hp.one_lt.le
        rw [if_pos hp, abs_of_nonneg (Real.log_nonneg hpos)]
        have hle := Real.log_le_log (by positivity : 0 < (k:ℝ)) (show (k:ℝ) ≤ n by exact_mod_cast hk)
        dsimp [M]; linarith
      · simp [hp]; dsimp [M]; linarith
  have hwh (k : ℕ) (_hk : k ≤ n) : |wheel k| ≤ M := by
    dsimp [wheel,M]; split <;> norm_num <;> linarith
  have harea := hN n (by omega)
  rw [← zeroMoment] at harea
  have sum := (abs_sub (shortPart n (GoldbachBudget.high n)) (shortPart n wheel)).trans
    (add_le_add (shortAtLogScale n hn1 _ hpr) (shortAtLogScale n hn1 _ hwh))
  have hx := mul_le_mul_of_nonneg_left harea (Nat.cast_nonneg (α := ℝ) n)
  linarith only [sum,hx]

theorem shortWheelBudget :
    ∃ N : ℕ, ∀ n ≥ N, Even n →
      |shortPart n (GoldbachBudget.high n) - shortPart n wheel| ≤ (n:ℝ)/2304 := by
  obtain ⟨N,hN⟩ := shortWheelSublinear (1/2304) (by norm_num)
  exact ⟨N, fun n hn _ => by linarith only [hN n hn]⟩

/-- Any chosen set of lags of this cardinality has sublinear absolute contribution.
    No restriction on the positions of the selected lags is needed. -/
theorem sparseLagBudget (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (F : Finset ℕ) (a : ℕ → ℝ),
      (F.card:ℝ) ≤ Real.exp ((length n:ℝ)/16) →
      (∀ k ≤ n, |a k| ≤ 4*(1+Real.log (n:ℝ))) →
      (∑ h ∈ F, |correlation n h a * cosineMoment n h|) ≤ ε*(n:ℝ) := by
  obtain ⟨N,hN⟩ := maskLogDecay 4 ((ε/32)^2) (by positivity)
  refine ⟨max 1 N, ?_⟩
  intro n hn F a hF ha
  let x := 1+Real.log (n:ℝ)
  let v := cosineMoment n 0
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hx : 0 ≤ x := by dsimp [x]; linarith [Real.log_nonneg hn1]
  have hv : 0 ≤ v := (abs_nonneg _).trans (cosineMomentBound n 0)
  have area := hN n (by omega)
  rw [← zeroMoment] at area
  change x^4*v ≤ (ε/32)^2 at area
  have decay : v ≤ Real.exp (-(length n:ℝ)/8) := (zeroMoment n).le.trans (maskedArea n)
  have count : (F.card:ℝ)^2*v ≤ 1 := by
    calc
      _ ≤ (Real.exp ((length n:ℝ)/16))^2 * Real.exp (-(length n:ℝ)/8) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hF 2) decay hv (by positivity)
      _ = 1 := by rw [pow_two, ← Real.exp_add, ← Real.exp_add]; ring_nf; simp
  have sq : ((F.card:ℝ)*x^2*v)^2 ≤ (ε/32)^2 := by
    calc
      _ = ((F.card:ℝ)^2*v)*(x^4*v) := by ring
      _ ≤ 1*(ε/32)^2 := mul_le_mul count area (mul_nonneg (by positivity) hv) zero_le_one
      _ = _ := one_mul _
  have small : (F.card:ℝ)*x^2*v ≤ ε/32 := (sq_le_sq₀ (by positivity) (by positivity)).mp sq
  have uniform (h : ℕ) : |correlation n h a * cosineMoment n h| ≤ ((n:ℝ)+1)*(4*x)^2*v := by
    rw [abs_mul]
    exact mul_le_mul (correlationBound n h a (4*x) (by positivity) ha) (cosineMomentBound n h)
      (abs_nonneg _) (by positivity)
  calc
    _ ≤ ∑ _h ∈ F, ((n:ℝ)+1)*(4*x)^2*v := Finset.sum_le_sum fun h _ => uniform h
    _ = (16*((n:ℝ)+1))*((F.card:ℝ)*x^2*v) := by simp; ring
    _ ≤ (32*(n:ℝ))*(ε/32) := mul_le_mul (by linarith) small (by positivity) (by positivity)
    _ = _ := by ring

private theorem upperTriangleLags (n : ℕ) (g : ℕ → ℕ → ℝ) :
    (∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1), if i<j then g i j else 0) =
      ∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.range (n+1-h), g k (k+h) := by
  let R := Finset.range (n+1)
  let U := (R ×ˢ R).filter (fun p => p.1 < p.2)
  let D := (Finset.Icc 1 n).sigma (fun h => Finset.range (n+1-h))
  calc
    _ = ∑ p ∈ U, g p.1 p.2 := by
      dsimp [U,R]
      rw [Finset.sum_filter, Finset.sum_product]
    _ = ∑ d ∈ D, g d.2 (d.2+d.1) := by
      apply Finset.sum_nbij' (fun p : ℕ × ℕ => (⟨p.2-p.1,p.1⟩ : Σ _ : ℕ, ℕ))
        (fun d => (d.2,d.2+d.1))
      · rintro ⟨i,j⟩ hp
        simp only [U,R,D,Finset.mem_filter,Finset.mem_product,Finset.mem_range,Finset.mem_sigma,
          Finset.mem_Icc] at hp ⊢
        omega
      · rintro ⟨h,k⟩ hd
        simp only [U,R,D,Finset.mem_filter,Finset.mem_product,Finset.mem_range,Finset.mem_sigma,
          Finset.mem_Icc] at hd ⊢
        omega
      · rintro ⟨i,j⟩ hu
        have hij := (Finset.mem_filter.mp hu).2
        change (i,i+(j-i)) = (i,j)
        rw [show i+(j-i)=j by omega]
      · rintro ⟨h,k⟩ _
        change (⟨k+h-k,k⟩ : Σ _ : ℕ, ℕ) = ⟨h,k⟩
        rw [show k+h-k=h by omega]
      · rintro ⟨i,j⟩ hu
        have hij := (Finset.mem_filter.mp hu).2
        change g i j = g i (i+(j-i))
        rw [show i+(j-i)=j by omega]
    _ = _ := Finset.sum_sigma ..

private theorem squareLags (n : ℕ) (g : ℕ → ℕ → ℝ) (hsym : ∀ i j, g i j = g j i) :
    (∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1), g i j) =
      (∑ i ∈ Finset.range (n+1), g i i) +
      2*(∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.range (n+1-h), g k (k+h)) := by
  let R := Finset.range (n+1)
  let up := fun i j => if i<j then g i j else 0
  let diag := fun i j => if i=j then g i i else 0
  have split (i j : ℕ) : g i j = diag i j + up i j + up j i := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [diag,up,hij,ne_of_lt hij,not_lt_of_ge hij.le]
    · simp [diag,up]
    · simp [diag,up,hji,ne_of_gt hji,not_lt_of_ge hji.le,hsym i j]
  have hd : (∑ i ∈ R, ∑ j ∈ R, diag i j) = ∑ i ∈ R, g i i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [diag,hi]
  have hu : (∑ i ∈ R, ∑ j ∈ R, up j i) = ∑ i ∈ R, ∑ j ∈ R, up i j := Finset.sum_comm
  calc
    _ = ∑ i ∈ R, ∑ j ∈ R, (diag i j + up i j + up j i) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => split i j
    _ = (∑ i ∈ R, g i i) + 2*(∑ i ∈ R, ∑ j ∈ R, up i j) := by
      simp only [Finset.sum_add_distrib,hd,hu]; ring
    _ = _ := by rw [show (∑ i ∈ R, ∑ j ∈ R, up i j) = _ from upperTriangleLags n g]

private theorem pointwiseLagEnergy (n : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    ‖GoldbachBudget.spec n a t‖^2 = correlation n 0 a +
      2*∑ h ∈ Finset.Icc 1 n, correlation n h a * Real.cos (2*Real.pi*(h:ℝ)*t) := by
  let angle := fun k : ℕ => 2*Real.pi*((k:ℝ)*t)
  let g := fun i j : ℕ => a i * a j * Real.cos (angle j - angle i)
  have sym (i j : ℕ) : g i j = g j i := by
    dsimp [g]
    rw [← Real.cos_neg (angle i-angle j), neg_sub]
    ring
  calc
    _ = (∑ k ∈ Finset.range (n+1), a k * Real.cos (angle k))^2 +
        (∑ k ∈ Finset.range (n+1), a k * Real.sin (angle k))^2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, GoldbachBudget.spec, GoldbachBudget.phase,
        Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, zero_add, add_zero, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, angle, pow_two]
    _ = ∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1), g i j := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [g]; rw [Real.cos_sub]; ring
    _ = _ := by
      rw [squareLags n g sym]
      have hd : (∑ i ∈ Finset.range (n+1), g i i) = correlation n 0 a := by simp [g,correlation]
      rw [hd]
      congr 2
      apply Finset.sum_congr rfl
      intro h _
      rw [correlation, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [g]
      rw [show angle (k+h)-angle k = 2*Real.pi*(h:ℝ)*t by dsimp [angle]; push_cast; ring]

private def longPart (n : ℕ) (a : ℕ → ℝ) :=
  2*∑ h ∈ Finset.Icc ((length n)^2+1) n, correlation n h a * cosineMoment n h

/-- Exact masked energy of any real weight, including the diagonal and both orders of each pair. -/
theorem lagEnergyIdentity (n : ℕ) (a : ℕ → ℝ) :
    (∫ t in (0:ℝ)..1, (resonant n).indicator (fun u => ‖GoldbachBudget.spec n a u‖^2) t) =
      shortPart n a + longPart n a := by
  let f := fun (h : ℕ) => (resonant n).indicator (fun t : ℝ => Real.cos (2*Real.pi*(h:ℝ)*t))
  let A := fun h => correlation n h a
  let H := Finset.Icc 1 n
  have hk : Continuous (fun t => packet (length n) t / (length n:ℝ)) := by unfold packet; fun_prop
  have hm : MeasurableSet (resonant n) := (GoldbachBudget.measurableArcs n).compl.inter
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)/2)) hk).measurableSet
  have hi (h : ℕ) : IntervalIntegrable (f h) MeasureTheory.volume (0:ℝ) 1 := by
    have hc : Continuous (fun t : ℝ => Real.cos (2*Real.pi*(h:ℝ)*t)) := by fun_prop
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator hm
  have hiA (h : ℕ) := (hi h).const_mul (A h)
  have ident : (resonant n).indicator (fun t => ‖GoldbachBudget.spec n a t‖^2) =
      fun t => A 0 * f 0 t + 2*∑ h ∈ H, A h * f h t := by
    funext t
    by_cases ht : t ∈ resonant n
    · simpa [f,A,H,ht] using pointwiseLagEnergy n a t
    · simp [f,ht]
  have hs : IntervalIntegrable (fun t => ∑ h ∈ H, A h * f h t) MeasureTheory.volume (0:ℝ) 1 :=
    IntervalIntegrable.fun_sum fun h _ => hiA h
  have split : H = Finset.Icc 1 (min n ((length n)^2)) ∪ Finset.Icc ((length n)^2+1) n := by
    ext h; simp only [H,Finset.mem_union,Finset.mem_Icc]; omega
  have dis : Disjoint (Finset.Icc 1 (min n ((length n)^2))) (Finset.Icc ((length n)^2+1) n) := by
    rw [Finset.disjoint_left]
    intro h ha hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  rw [ident, intervalIntegral.integral_add (hiA 0) (hs.const_mul 2)]
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun h _ => hiA h)]
  change A 0 * cosineMoment n 0 + 2*(∑ h ∈ H, A h * cosineMoment n h) = _
  rw [split, Finset.sum_union dis]
  unfold shortPart longPart
  dsimp only [A]
  ring

end
end GoldbachPacket
