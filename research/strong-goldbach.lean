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

theorem packetPartition (n : ℕ) :
    (pair n (high n) (high n)).re = J n (K n) + J n (fun t => 1-K n t) := by
  let F := fun t : ℝ => spec n (high n) t * spec n (high n) t * phase (-(n:ℝ)*t)
  let T := fun (v : ℝ → ℝ) (t : ℝ) =>
    (arcs n)ᶜ.indicator (fun u => (v u:ℂ)*spec n (high n) u*spec n (high n) u*phase (-(n:ℝ)*u)) t
  have hK : Continuous (K n) := by unfold K; fun_prop
  have integrable (v : ℝ → ℝ) (hv : Continuous v) :
      IntervalIntegrable (T v) MeasureTheory.volume (0:ℝ) 1 := by
    have cont : Continuous (fun u : ℝ => (v u:ℂ)*spec n (high n) u*spec n (high n) u*phase (-(n:ℝ)*u)) := by
      unfold spec phase
      fun_prop
    have h := cont.intervalIntegrable (μ := MeasureTheory.volume) 0 1
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h ⊢
    exact h.indicator (measurableArcs n).compl
  have partition : (fun t => (arcs n)ᶜ.indicator F t) =
      fun t => T (K n) t + T (fun u => 1-K n u) t := by
    funext t
    by_cases ht : t ∈ (arcs n)ᶜ
    · simp only [F, T, Set.indicator_of_mem ht, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    · simp [T, ht]
  unfold pair J
  change (intervalIntegral (fun t => (arcs n)ᶜ.indicator F t) 0 1 MeasureTheory.volume).re = _
  rw [partition, intervalIntegral.integral_add (integrable _ hK) (integrable _ (continuous_const.sub hK))] <;> rfl

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
