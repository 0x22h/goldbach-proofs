import Mathlib

/-
QP-0041 · Polarize two distinct complex tests on a frequency band.

Pointwise, `‖a + b‖ ^ 2 - ‖a - b‖ ^ 2` is `4 * (a * star b).re`. Summing that over the band
gives the claim. The squared norm of a complex number is `z.re * z.re + z.im * z.im`
(`Complex.norm_def` together with `Complex.normSq_apply`), so the pointwise statement is a ring
identity in real and imaginary parts.
-/

theorem PEqualNP.Outside.L_quadratic_primes_levent_finite_polarization :
    ∀ (S : Finset ℕ) (u v : ℕ → ℂ),
      (∑ k ∈ S, ‖u k + v k‖ ^ 2) - (∑ k ∈ S, ‖u k - v k‖ ^ 2)
        = 4 * ∑ k ∈ S, (u k * star (v k)).re := by
  intro S u v
  have hnorm (z : ℂ) : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply]
  have h (a b : ℂ) : ‖a + b‖ ^ 2 - ‖a - b‖ ^ 2 = 4 * (a * star b).re := by
    rw [hnorm (a + b), hnorm (a - b)]
    simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, star]
    ring
  calc (∑ k ∈ S, ‖u k + v k‖ ^ 2) - ∑ k ∈ S, ‖u k - v k‖ ^ 2
      = ∑ k ∈ S, (‖u k + v k‖ ^ 2 - ‖u k - v k‖ ^ 2) := by rw [Finset.sum_sub_distrib]
    _ = ∑ k ∈ S, 4 * (u k * star (v k)).re := Finset.sum_congr rfl fun k _ => h (u k) (v k)
    _ = 4 * ∑ k ∈ S, (u k * star (v k)).re := by rw [Finset.mul_sum]
