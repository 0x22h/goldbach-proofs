import Mathlib

namespace PEqualNP.Outside

/-- The standard representatives modulo `q` of the roots of `X ^ 2 + a`. -/
def rcmRoots (a q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun r => q ∣ r^2 + a)

lemma rcm_mem_roots (a q r : ℕ) : r ∈ rcmRoots a q ↔ r < q ∧ q ∣ r^2 + a := by
  simp [rcmRoots, Finset.mem_filter, Finset.mem_range]

/-- The `ZMod` avatar of membership in `rcmRoots a q`. -/
lemma rcm_zmod_root (a q r : ℕ) : ((r : ZMod q)^2 + a = 0) ↔ q ∣ r^2 + a := by
  have h : ((r : ZMod q)^2 + a : ZMod q) = (r^2 + a : ℕ) := by
    simp only [Nat.cast_add, Nat.cast_pow]
  rw [h, ZMod.natCast_eq_zero_iff]

lemma rcm_coe_mod (n m : ℕ) : ((n % m : ℕ) : ZMod m) = (n : ZMod m) := by
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq n m

lemma rcm_eq_of_cast {n : ℕ} [NeZero n] {x y : ℕ} (hx : x < n) (hy : y < n)
    (h : (x : ZMod n) = (y : ZMod n)) : x = y := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

/-- The Chinese remainder equivalence sends a natural number to the pair of its two residues. -/
lemma rcm_crt_natCast {a b : ℕ} (h : Nat.Coprime a b) (n : ℕ) :
    ZMod.chineseRemainder h (n : ZMod (a * b)) = ((n : ZMod a), (n : ZMod b)) :=
  map_natCast (ZMod.chineseRemainder h) n

lemma rcm_crt_fst {a b : ℕ} (h : Nat.Coprime a b) (n : ℕ) :
    (ZMod.chineseRemainder h (n : ZMod (a * b))).1 = (n : ZMod a) :=
  congrArg Prod.fst (rcm_crt_natCast h n)

lemma rcm_crt_snd {a b : ℕ} (h : Nat.Coprime a b) (n : ℕ) :
    (ZMod.chineseRemainder h (n : ZMod (a * b))).2 = (n : ZMod b) :=
  congrArg Prod.snd (rcm_crt_natCast h n)

/-- Reducing a root modulo a divisor of the modulus again gives a root. -/
lemma rcm_mod_roots {a m n : ℕ} (hm : 0 < m) (hmn : m ∣ n) (r : ℕ) (hr : r ∈ rcmRoots a n) :
    r % m ∈ rcmRoots a m := by
  have hd : n ∣ r^2 + a := (rcm_mem_roots a n r).mp hr |>.2
  have hz : ((r : ZMod m)^2 + a = 0) := (rcm_zmod_root a m r).mpr (dvd_trans hmn hd)
  rw [← rcm_coe_mod r m] at hz
  exact (rcm_mem_roots a m (r % m)).mpr
    ⟨Nat.mod_lt r hm, (rcm_zmod_root a m (r % m)).mp hz⟩

lemma rcm_from_mem {a b c : ℕ} [NeZero a] [NeZero b] (h : Nat.Coprime a b)
    (p : { u : ℕ // u ∈ rcmRoots c a } × { v : ℕ // v ∈ rcmRoots c b }) :
    ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) ∈ rcmRoots c (a * b) := by
  haveI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have hc : ZMod.chineseRemainder h ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) =
      (↑p.1.1, ↑p.2.1) := RingEquiv.apply_symm_apply _ _
  have hu : ((p.1.1 : ℕ) : ZMod a)^2 + c = 0 :=
    (rcm_zmod_root c a p.1.1).mpr ((rcm_mem_roots c a p.1.1).mp p.1.2).2
  have hv : ((p.2.1 : ℕ) : ZMod b)^2 + c = 0 :=
    (rcm_zmod_root c b p.2.1).mpr ((rcm_mem_roots c b p.2.1).mp p.2.2).2
  have hprod : (((p.1.1 : ZMod a), (p.2.1 : ZMod b)) : ZMod a × ZMod b)^2 + c = 0 := by
    show ((↑p.1.1 ^ 2 + c, ↑p.2.1 ^ 2 + c) : ZMod a × ZMod b) = (0, 0)
    simp [hu, hv]
  have h0 : ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1))^2 + c = 0 := by
    apply (ZMod.chineseRemainder h).map_eq_zero_iff.mp
    rw [map_add, map_pow, map_natCast, hc]
    exact hprod
  refine (rcm_mem_roots c (a * b) _).mpr ⟨ZMod.val_lt _, ?_⟩
  have hz : (((ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) : ℕ) :
      ZMod (a * b)))^2 + c = 0 := by
    rw [ZMod.natCast_zmod_val]
    exact h0
  exact (rcm_zmod_root c (a * b) _).mp hz

def rcm_to {a b c : ℕ} [NeZero a] [NeZero b] (_h : Nat.Coprime a b)
    (r : { r : ℕ // r ∈ rcmRoots c (a * b) }) :
    { u : ℕ // u ∈ rcmRoots c a } × { v : ℕ // v ∈ rcmRoots c b } :=
  ⟨⟨r.1 % a, rcm_mod_roots (Nat.pos_of_ne_zero (NeZero.ne a)) (dvd_mul_right a b) r.1 r.2⟩,
    ⟨r.1 % b, rcm_mod_roots (Nat.pos_of_ne_zero (NeZero.ne b)) (dvd_mul_left b a) r.1 r.2⟩⟩

def rcm_from {a b c : ℕ} [NeZero a] [NeZero b] (h : Nat.Coprime a b)
    (p : { u : ℕ // u ∈ rcmRoots c a } × { v : ℕ // v ∈ rcmRoots c b }) :
    { r : ℕ // r ∈ rcmRoots c (a * b) } :=
  ⟨ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)), rcm_from_mem h p⟩

lemma rcm_from_to {a b c : ℕ} [NeZero a] [NeZero b] (h : Nat.Coprime a b)
    (r : { r : ℕ // r ∈ rcmRoots c (a * b) }) :
    rcm_from h (rcm_to h r) = r := by
  haveI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have key : ((ZMod.chineseRemainder h).symm (↑(r.1 % a), ↑(r.1 % b)) : ZMod (a * b)) =
      (r.1 : ZMod (a * b)) := by
    rw [rcm_coe_mod r.1 a, rcm_coe_mod r.1 b, ← rcm_crt_natCast h r.1,
      RingEquiv.symm_apply_apply]
  have hval : ZMod.val ((ZMod.chineseRemainder h).symm (↑(r.1 % a), ↑(r.1 % b))) = r.1 :=
    rcm_eq_of_cast (ZMod.val_lt _) ((rcm_mem_roots c (a * b) r.1).mp r.2).1
      ((ZMod.natCast_zmod_val _).trans key)
  exact Subtype.ext hval

lemma rcm_to_from {a b c : ℕ} [NeZero a] [NeZero b] (h : Nat.Coprime a b)
    (p : { u : ℕ // u ∈ rcmRoots c a } × { v : ℕ // v ∈ rcmRoots c b }) :
    rcm_to h (rcm_from h p) = p := by
  haveI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have hc : ZMod.chineseRemainder h ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) =
      (↑p.1.1, ↑p.2.1) := RingEquiv.apply_symm_apply _ _
  have hxa : (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) : ZMod a) =
      (p.1.1 : ZMod a) := by
    rw [← rcm_crt_fst h (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1))),
      ZMod.natCast_zmod_val, hc]
  have hxb : (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) : ZMod b) =
      (p.2.1 : ZMod b) := by
    rw [← rcm_crt_snd h (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1))),
      ZMod.natCast_zmod_val, hc]
  have h1 : ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) % a = p.1.1 :=
    rcm_eq_of_cast (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne a)))
      ((rcm_mem_roots c a p.1.1).mp p.1.2).1
        ((rcm_coe_mod (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1))) a).trans hxa)
  have h2 : ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) % b = p.2.1 :=
    rcm_eq_of_cast (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne b)))
      ((rcm_mem_roots c b p.2.1).mp p.2.2).1
        ((rcm_coe_mod (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1))) b).trans hxb)
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · exact h1
  · exact h2

/-- Coprimality splits the roots of `X ^ 2 + a` modulo a product into pairs of roots: the count is
multiplicative. -/
theorem rcm_crt_density (a q m : ℕ) (hq : 0 < q) (hm : 0 < m) (hcq : Nat.Coprime q m) :
    (rcmRoots a (q * m)).card = (rcmRoots a q).card * (rcmRoots a m).card := by
  haveI : NeZero q := ⟨ne_of_gt hq⟩
  haveI : NeZero m := ⟨ne_of_gt hm⟩
  haveI : NeZero (q * m) := ⟨mul_ne_zero (ne_of_gt hq) (ne_of_gt hm)⟩
  have hcard : (rcmRoots a (q * m)).card = ((rcmRoots a q) ×ˢ (rcmRoots a m)).card := by
    refine Finset.card_bij (fun r _ => (r % q, r % m)) ?_ ?_ ?_
    · intro r hr
      refine Finset.mem_product.mpr
        ⟨rcm_mod_roots hq (dvd_mul_right q m) r hr, rcm_mod_roots hm (dvd_mul_left m q) r hr⟩
    · intro r₁ hr₁ r₂ hr₂ h
      have h1 : r₁ % q = r₂ % q := congrArg Prod.fst h
      have h2 : r₁ % m = r₂ % m := congrArg Prod.snd h
      have h3 : (r₁ : ZMod (q * m)) = (r₂ : ZMod (q * m)) := by
        apply (ZMod.chineseRemainder hcq).injective
        rw [rcm_crt_natCast hcq r₁, rcm_crt_natCast hcq r₂, ← rcm_coe_mod r₁ q,
          ← rcm_coe_mod r₂ q, ← rcm_coe_mod r₁ m, ← rcm_coe_mod r₂ m, h1, h2]
      exact rcm_eq_of_cast ((rcm_mem_roots a (q * m) r₁).mp hr₁).1
        ((rcm_mem_roots a (q * m) r₂).mp hr₂).1 h3
    · intro p hp
      obtain ⟨hpq, hpm⟩ := Finset.mem_product.mp hp
      set x : { r : ℕ // r ∈ rcmRoots a (q * m) } := rcm_from hcq ⟨⟨p.1, hpq⟩, ⟨p.2, hpm⟩⟩
      refine ⟨x.1, x.2, ?_⟩
      exact congrArg
        (fun z : { u : ℕ // u ∈ rcmRoots a q } × { v : ℕ // v ∈ rcmRoots a m } => (z.1.1, z.2.1))
        (rcm_to_from hcq ⟨⟨p.1, hpq⟩, ⟨p.2, hpm⟩⟩)
  exact hcard.trans (Finset.card_product _ _)

/-- The number of square roots of `-1` among the residues below a prime: one for the prime two,
two for the primes congruent to one mod four, and none for the primes congruent to three mod four.
-/
theorem rcm_prime_card (p : ℕ) (hp : Nat.Prime p) :
    (rcmRoots 1 p).card = if p = 2 then 1 else if p % 4 = 1 then 2 else 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h1p : 1 < p := Nat.Prime.one_lt hp
  have hroots : ∀ a q : ℕ, rcmRoots a q = Finset.filter (fun r => q ∣ r^2 + a) (Finset.range q) :=
    fun _ _ => rfl
  have key : ∀ r : ℕ, ((r^2 + 1 : ℕ) : ZMod p) = (r : ZMod p)^2 + 1 := by
    intro r
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  -- Membership in the filtered range says that the cast is a square root of minus one.
  have hmem : ∀ r : ℕ, r ∈ rcmRoots 1 p ↔ r < p ∧ (r : ZMod p)^2 = -1 := by
    intro r
    rw [hroots]
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hlt, hdvd⟩
      refine ⟨hlt, neg_eq_iff_eq_neg.mp (neg_eq_iff_add_eq_zero.mpr ?_)⟩
      rw [← key]
      exact (ZMod.natCast_eq_zero_iff (r^2 + 1) p).mpr hdvd
    · rintro ⟨hlt, hroot⟩
      refine ⟨hlt, (ZMod.natCast_eq_zero_iff (r^2 + 1) p).mp (key r ▸ ?_)⟩
      exact neg_eq_iff_add_eq_zero.mp (neg_eq_iff_eq_neg.mpr hroot)
  have hdvd : ∀ r : ℕ, r < p → (r : ZMod p)^2 = -1 → p ∣ r^2 + 1 := by
    intro r hr hroot
    have h0 : ((r^2 + 1 : ℕ) : ZMod p) = 0 := by
      rw [key]
      exact neg_eq_iff_add_eq_zero.mp (neg_eq_iff_eq_neg.mpr hroot)
    exact (ZMod.natCast_eq_zero_iff (r^2 + 1) p).mp h0
  rcases hp.eq_two_or_odd with rfl | hodd
  · -- The even prime: the only root below two is one.
    have hset : (Finset.filter (fun r => 2 ∣ r^2 + 1) (Finset.range 2) : Finset ℕ) = {1} := by
      decide
    rw [hroots, hset, Finset.card_singleton]
    exact by decide
  · haveI hnz : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
    have hpos : p ≠ 2 := by omega
    have hfour : p % 4 = 1 ∨ p % 4 = 3 := by omega
    by_cases h1 : p % 4 = 1
    · -- Minus one is a square: pick a root and list its two representatives.
      obtain ⟨x, hx⟩ : ∃ y : ZMod p, y^2 = -1 := by
        obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega : p % 4 ≠ 3)
        exact ⟨y, by rw [pow_two]; exact hy.symm⟩
      have hval : x.val < p := ZMod.val_lt x
      have hcoe : (x.val : ZMod p) = x := @ZMod.natCast_zmod_val p hnz x
      have hsqv : (x.val : ZMod p)^2 = -1 := by rw [hcoe]; exact hx
      have had : p ∣ x.val^2 + 1 := hdvd x.val hval hsqv
      have hxv : 0 < x.val := by
        by_contra hz
        have hz2 : x.val = 0 := Nat.eq_zero_of_not_pos hz
        have hd : p ∣ 1 := by simpa [hz2] using had
        have : p ≤ 1 := Nat.le_of_dvd (by omega : (0 : ℕ) < 1) hd
        omega
      have hsub : p - x.val < p := by omega
      -- The negation of a root is the representative obtained by subtracting from the prime.
      have hpx : ((p - x.val : ℕ) : ZMod p) = -x := by
        rw [Nat.cast_sub (Nat.le_of_lt hval), ZMod.natCast_self, zero_sub, hcoe]
      have hmain : rcmRoots 1 p = {x.val, p - x.val} := by
        apply Finset.ext
        intro r
        have hiff : r ∈ ({x.val, p - x.val} : Finset ℕ) ↔ r = x.val ∨ r = p - x.val := by simp
        rw [hmem, hiff]
        constructor
        · rintro ⟨hr, hroot⟩
          have h2 : (r : ZMod p)^2 = x^2 := by rw [hx]; exact hroot
          have h3 : (r : ZMod p) = x ∨ (r : ZMod p) = -x := sq_eq_sq_iff_eq_or_eq_neg.mp h2
          rcases h3 with h | h
          · exact Or.inl (by
              have hc : ZMod.val (r : ZMod p) = ZMod.val x := congrArg ZMod.val h
              rwa [ZMod.val_natCast_of_lt hr] at hc)
          · exact Or.inr (by
              have hn : (r : ZMod p) = ((p - x.val : ℕ) : ZMod p) := by rw [hpx, h]
              have hc : ZMod.val (r : ZMod p) = ZMod.val ((p - x.val : ℕ) : ZMod p) :=
                congrArg ZMod.val hn
              rwa [ZMod.val_natCast_of_lt hr, ZMod.val_natCast_of_lt hsub] at hc)
        · rintro (h | h)
          · subst h
            exact ⟨hval, hsqv⟩
          · subst h
            refine ⟨hsub, ?_⟩
            rw [hpx, neg_sq, ← hcoe]
            exact hsqv
      have hne : x.val ≠ p - x.val := by omega
      rw [if_neg hpos, if_pos h1]
      exact Finset.card_eq_two.mpr ⟨x.val, p - x.val, hne, hmain⟩
    · -- Minus one is not a square: the filtered range is empty.
      have h3 : p % 4 = 3 := by
        rcases hfour with h | h
        · exact absurd h h1
        · exact h
      have hempty : rcmRoots 1 p = ∅ := by
        apply Finset.ext
        intro r
        rw [hmem]
        constructor
        · rintro ⟨_, hroot⟩
          exact absurd h3 (ZMod.mod_four_ne_three_of_sq_eq_neg_one hroot)
        · exact fun h => absurd h (by simp)
      rw [if_neg hpos, if_neg h1, hempty, Finset.card_empty]

/-- Walking along the squarefree factorisation one prime at a time: the number of the roots of
`X ^ 2 + 1` below a squarefree modulus is the product, over the prime divisors of the modulus, of
the number of roots below each of them. The step splits off one prime factor by the Chinese
remainder theorem, and the product over the prime factors splits off the same factor. -/
theorem L_quadratic_primes_levent_root_count_multiplicative :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a);
    ∀ q : ℕ, 0<q → Squarefree q →
      (roots 1 q).card = ∏ p ∈ q.primeFactors, (if p=2 then 1 else if p % 4 = 1 then 2 else 0) := by
  intro roots
  intro q
  induction q using Nat.strong_induction_on with
  | ind n ih =>
    intro hn hsf
    have hcast : (roots 1 n).card = (rcmRoots 1 n).card := rfl
    refine hcast.trans ?_
    by_cases hn1 : n = 1
    · -- The empty factorisation: the single residue below one is a root, the product is empty.
      subst hn1
      have hbase : rcmRoots 1 1 = ({0} : Finset ℕ) := by
        have h : (Finset.range 1).filter (fun r => 1 ∣ r^2 + 1) = ({0} : Finset ℕ) := by decide
        exact h
      rw [hbase, Finset.card_singleton, Nat.primeFactors_one, Finset.prod_empty]
    · have hgt : 1 < n := by omega
      obtain ⟨p, hp⟩ := (Nat.nonempty_primeFactors (n := n)).mpr hgt
      have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      set m : ℕ := n / p
      have hpos : 0 < m := Nat.div_pos (Nat.le_of_dvd (by omega : 0 < n) hpd) hp'.pos
      have hmul : p * m = n := Nat.mul_div_cancel' hpd
      have hm0 : m ≠ 0 := Nat.ne_of_gt hpos
      -- Squarefreeness says the split off prime does not divide the cofactor.
      have hnotdvd : ¬ p ∣ m := by
        intro h
        have h2 : p * p ∣ p * m := Nat.mul_dvd_mul_left p h
        exact (Nat.squarefree_iff_prime_squarefree.mp hsf p hp') (by rwa [hmul] at h2)
      have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp').mpr hnotdvd
      have hmd : m ∣ n := by rw [← hmul]; exact Nat.dvd_mul_left m p
      have hsqm : Squarefree m :=
        (Nat.squarefree_iff_prime_squarefree).mpr (fun x hx hxm =>
          (Nat.squarefree_iff_prime_squarefree.mp hsf x hx) (dvd_trans hxm hmd))
      have hmn : m < n := Nat.div_lt_self (by omega : 0 < n) (Nat.Prime.one_lt hp')
      have hcard : (rcmRoots 1 n).card = (rcmRoots 1 p).card * (rcmRoots 1 m).card := by
        rw [← hmul]
        exact rcm_crt_density 1 p m hp'.pos hpos hcop
      have ihm : (rcmRoots 1 m).card =
          ∏ x ∈ m.primeFactors, (if x=2 then 1 else if x % 4 = 1 then 2 else 0) :=
        ih m hmn hpos hsqm
      have hnp : p ∉ m.primeFactors := fun h => hnotdvd (Nat.dvd_of_mem_primeFactors h)
      have hdisj : Disjoint ({p} : Finset ℕ) m.primeFactors :=
        Finset.disjoint_singleton_left.mpr hnp
      have hpf : n.primeFactors = ({p} : Finset ℕ) ∪ m.primeFactors := by
        rw [← hmul, Nat.primeFactors_mul hp'.ne_zero hm0, hp'.primeFactors]
      have hprod : (if p=2 then 1 else if p % 4 = 1 then 2 else 0) *
          (∏ x ∈ m.primeFactors, (if x=2 then 1 else if x % 4 = 1 then 2 else 0)) =
          ∏ x ∈ n.primeFactors, (if x=2 then 1 else if x % 4 = 1 then 2 else 0) := by
        rw [hpf, Finset.prod_union hdisj, Finset.prod_singleton]
      calc
        (rcmRoots 1 n).card
        = (rcmRoots 1 p).card * (rcmRoots 1 m).card := hcard
        _ = (if p=2 then 1 else if p % 4 = 1 then 2 else 0) *
            (∏ x ∈ m.primeFactors, (if x=2 then 1 else if x % 4 = 1 then 2 else 0)) := by
          rw [rcm_prime_card p hp', ihm]
        _ = ∏ x ∈ n.primeFactors, (if x=2 then 1 else if x % 4 = 1 then 2 else 0) := hprod

end PEqualNP.Outside
