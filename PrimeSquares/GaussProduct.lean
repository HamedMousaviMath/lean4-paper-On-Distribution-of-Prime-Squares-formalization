import PrimeSquares.GaussCRT
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Global finite product bound and support for the principal square sum

The prime-power majorant retains the zero factors. CRT and coprime induction
bound the actual sum by that majorant, proving global support and the product
in equation e:sproductbound without any prime-distribution input.
-/

open Finset

namespace PrimeSquares

noncomputable def gaussOddPrimeFactor (p : ℕ) : ℝ := (1 - (Real.sqrt p)⁻¹)⁻¹

noncomputable def gaussPrimePowerBound (p j : ℕ) : ℝ :=
  if j = 0 then 1 else if p = 2 then (if j ≤ 3 then 4 else 0)
  else if j = 1 then gaussOddPrimeFactor p else 0

noncomputable def gaussProductBound (q : ℕ) : ℝ := q.factorization.prod gaussPrimePowerBound

noncomputable def gaussOddProduct (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors.filter (fun p => 2 < p), gaussOddPrimeFactor p

theorem gaussOddPrimeFactor_pos (p : ℕ) (hp : 2 ≤ p) : 0 < gaussOddPrimeFactor p := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hs := Real.sq_sqrt (Nat.cast_nonneg p)
  have hr := Real.sqrt_nonneg (p : ℝ)
  have hr1 : 1 < Real.sqrt (p : ℝ) := by nlinarith
  unfold gaussOddPrimeFactor
  exact inv_pos.mpr (sub_pos.mpr ((inv_lt_one₀ (by linarith)).mpr hr1))

theorem gaussPrimePowerBound_nonneg (p j : ℕ) [Fact p.Prime] :
    0 ≤ gaussPrimePowerBound p j := by
  have hp : p.Prime := Fact.out
  have he := gaussOddPrimeFactor_pos p hp.two_le
  unfold gaussPrimePowerBound
  split_ifs <;> positivity

theorem gaussProductBound_nonneg (q : ℕ) : 0 ≤ gaussProductBound q := by
  classical
  change 0 ≤ ∏ p ∈ q.primeFactors, gaussPrimePowerBound p (q.factorization p)
  apply prod_nonneg
  intro p hp
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  exact gaussPrimePowerBound_nonneg _ _

theorem gaussProductBound_one : gaussProductBound 1 = 1 := by
  simp [gaussProductBound]

theorem gaussProductBound_mul (m n : ℕ) (hc : m.Coprime n) :
    gaussProductBound (m * n) = gaussProductBound m * gaussProductBound n := by
  classical
  unfold gaussProductBound
  rw [Nat.factorization_mul_of_coprime hc, Finsupp.prod_add_index_of_disjoint]
  exact hc.disjoint_primeFactors

theorem gaussProductBound_prime_pow (p j : ℕ) [Fact p.Prime] :
    gaussProductBound (p ^ j) = gaussPrimePowerBound p j := by
  have hp : p.Prime := Fact.out
  simp [gaussProductBound, hp.factorization_pow, gaussPrimePowerBound]

/-- Each local weight bounds every actual unit-coefficient prime-power sum. -/
theorem scaled_norm_principalSquareSum_prime_pow_le (p j : ℕ) [Fact p.Prime]
    (hj : 0 < j) (a : ZMod (p ^ j)) (ha : IsUnit a) :
    Real.sqrt (p ^ j : ℕ) * ‖principalSquareSum (p ^ j) a‖ ≤ gaussPrimePowerBound p j := by
  by_cases hp2 : p = 2
  · subst p
    by_cases hj3 : j ≤ 3
    · simpa only [gaussPrimePowerBound, ite_eq_right (Nat.ne_of_gt hj), ite_true,
        ite_eq_left hj3] using scaled_norm_principalSquareSum_two_pow_le j a ha
    · rw [principalSquareSum_two_pow_eq_zero j (by omega) a ha, norm_zero, mul_zero]
      simp [gaussPrimePowerBound, hj.ne', hj3]
  · by_cases hj1 : j = 1
    · subst j
      have H (d : ℕ) [NeZero d] (hd : d = p) (c : ZMod d) (hc : IsUnit c) :
          Real.sqrt d * ‖principalSquareSum d c‖ ≤ gaussPrimePowerBound p 1 := by
        subst d
        simpa only [gaussPrimePowerBound, gaussOddPrimeFactor,
          ite_eq_right (by decide : (1 : ℕ) ≠ 0), ite_eq_right hp2, ite_true]
          using scaled_norm_principalSquareSum_odd_prime_le p hp2 c hc
      exact H (p ^ 1) (pow_one p) a ha
    · rw [principalSquareSum_odd_prime_pow_eq_zero p j hp2 (by omega) a ha,
        norm_zero, mul_zero]
      simp [gaussPrimePowerBound, hj.ne', hp2, hj1]

/-- Uniformity in the unit coefficient permits coprime induction despite CRT scaling. -/
theorem scaled_norm_principalSquareSum_le_product (q : ℕ) [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    Real.sqrt q * ‖principalSquareSum q a‖ ≤ gaussProductBound q := by
  have H : ∀ r : ℕ, ∀ [NeZero r] (c : ZMod r), IsUnit c →
      Real.sqrt r * ‖principalSquareSum r c‖ ≤ gaussProductBound r := by
    refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_
    · intro p j hp hj _ c hc
      have : Fact p.Prime := ⟨hp⟩
      rw [gaussProductBound_prime_pow]
      exact scaled_norm_principalSquareSum_prime_pow_le p j hj c hc
    · intro _ c _
      exact False.elim (NeZero.ne 0 rfl)
    · intro _ c _
      simpa only [Nat.cast_one, Real.sqrt_one, one_mul, gaussProductBound_one] using
        norm_principalSquareSum_le_one 1 c
    · intro m n hm hn h ih_m ih_n _ c hc
      have : NeZero m := ⟨by omega⟩
      have : NeZero n := ⟨by omega⟩
      rw [scaled_norm_principalSquareSum_coprime_mul m n h, gaussProductBound_mul m n h]
      apply mul_le_mul
      · exact ih_m _ ((hc.map (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m))).mul
          ((ZMod.unitOfCoprime n h.symm)⁻¹).isUnit)
      · exact ih_n _ ((hc.map (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n))).mul
          ((ZMod.unitOfCoprime m h)⁻¹).isUnit)
      · positivity
      · exact gaussProductBound_nonneg m
  exact H q a ha

theorem gaussProductBound_odd_prime_sq_zero (q p : ℕ) (hq : q ≠ 0)
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : p ^ 2 ∣ q) : gaussProductBound q = 0 := by
  classical
  have hp : p.Prime := Fact.out
  have hj : 2 ≤ q.factorization p := (hp.pow_dvd_iff_le_factorization hq).mp hd
  have hm : p ∈ q.primeFactors := by
    change p ∈ q.factorization.support
    exact Finsupp.mem_support_iff.mpr (show q.factorization p ≠ 0 by omega)
  change (∏ r ∈ q.primeFactors, gaussPrimePowerBound r (q.factorization r)) = 0
  apply prod_eq_zero hm
  simp [gaussPrimePowerBound, hp2, show q.factorization p ≠ 0 by omega,
    show q.factorization p ≠ 1 by omega]

theorem gaussProductBound_sixteen_dvd_zero (q : ℕ) (hq : q ≠ 0) (hd : 16 ∣ q) :
    gaussProductBound q = 0 := by
  classical
  have hj : 4 ≤ q.factorization 2 := (Nat.prime_two.pow_dvd_iff_le_factorization hq).mp hd
  have hm : 2 ∈ q.primeFactors := by
    change 2 ∈ q.factorization.support
    exact Finsupp.mem_support_iff.mpr (show q.factorization 2 ≠ 0 by omega)
  change (∏ r ∈ q.primeFactors, gaussPrimePowerBound r (q.factorization r)) = 0
  apply prod_eq_zero hm
  simp [gaussPrimePowerBound, show q.factorization 2 ≠ 0 by omega,
    show ¬q.factorization 2 ≤ 3 by omega]

theorem principalSquareSum_eq_zero_of_product_zero (q : ℕ) [NeZero q] (a : ZMod q)
    (ha : IsUnit a) (hz : gaussProductBound q = 0) : principalSquareSum q a = 0 := by
  have he := scaled_norm_principalSquareSum_le_product q a ha
  rw [hz] at he
  have hp : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos q)
  have hn := norm_nonneg (principalSquareSum q a)
  apply norm_eq_zero.mp
  nlinarith

theorem principalSquareSum_odd_prime_sq (q p : ℕ) [NeZero q] [Fact p.Prime]
    (hp2 : p ≠ 2) (hd : p ^ 2 ∣ q) (a : ZMod q) (ha : IsUnit a) :
    principalSquareSum q a = 0 := by
  exact principalSquareSum_eq_zero_of_product_zero q a ha
    (gaussProductBound_odd_prime_sq_zero q p (NeZero.ne q) hp2 hd)

theorem principalSquareSum_sixteen_dvd (q : ℕ) [NeZero q] (hd : 16 ∣ q)
    (a : ZMod q) (ha : IsUnit a) : principalSquareSum q a = 0 := by
  exact principalSquareSum_eq_zero_of_product_zero q a ha
    (gaussProductBound_sixteen_dvd_zero q (NeZero.ne q) hd)

/-- A nonzero actual sum has exactly the prime-power support claimed in the source. -/
theorem principalSquareSum_support (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (hne : principalSquareSum q a ≠ 0) :
    q.factorization 2 ≤ 3 ∧ ∀ p ∈ q.primeFactors, p ≠ 2 → q.factorization p = 1 := by
  constructor
  · by_contra! hj
    exact hne (principalSquareSum_sixteen_dvd q
      ((Nat.prime_two.pow_dvd_iff_le_factorization (k := 4) (NeZero.ne q)).mpr (by omega)) a ha)
  · intro p hp hp2
    have hp' := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hp'⟩
    have hj : 0 < q.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    by_contra! he
    exact hne (principalSquareSum_odd_prime_sq q p hp2
      ((hp'.pow_dvd_iff_le_factorization (k := 2) (NeZero.ne q)).mpr (by omega)) a ha)

theorem gaussOddProduct_nonneg (q : ℕ) : 0 ≤ gaussOddProduct q := by
  classical
  apply prod_nonneg
  intro p hp
  exact (gaussOddPrimeFactor_pos p (Nat.le_of_lt (mem_filter.mp hp).2)).le

theorem gaussPrimePowerBound_le (p j : ℕ) [Fact p.Prime] (hj : 0 < j) :
    gaussPrimePowerBound p j ≤ if p = 2 then 4 else gaussOddPrimeFactor p := by
  have hp : p.Prime := Fact.out
  have hg := (gaussOddPrimeFactor_pos p hp.two_le).le
  unfold gaussPrimePowerBound
  split_ifs <;> norm_num at * <;> linarith

/-- Separate the sole factor at two from the remaining prime product. -/
theorem gaussProductBound_le_oddProduct (q : ℕ) :
    gaussProductBound q ≤ 4 * gaussOddProduct q := by
  classical
  have hb : gaussProductBound q ≤
      ∏ p ∈ q.primeFactors, if p = 2 then (4 : ℝ) else gaussOddPrimeFactor p := by
    change (∏ p ∈ q.primeFactors, gaussPrimePowerBound p (q.factorization p)) ≤ _
    apply prod_le_prod₀
    · intro p hp
      have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      exact gaussPrimePowerBound_nonneg _ _
    · intro p hp
      have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      exact gaussPrimePowerBound_le p _
        (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp))
  by_cases h2 : 2 ∈ q.primeFactors
  · have hs : q.primeFactors = insert 2 (q.primeFactors.filter (fun p => 2 < p)) := by
      ext p
      simp only [mem_insert, mem_filter]
      constructor
      · intro hp
        by_cases he : p = 2
        · exact Or.inl he
        · exact Or.inr ⟨hp, by have := (Nat.prime_of_mem_primeFactors hp).two_le; omega⟩
      · rintro (rfl | hp)
        · exact h2
        · exact hp.1
    rw [hs, prod_insert (by simp), ite_eq_left rfl] at hb
    have he : (∏ p ∈ q.primeFactors.filter (fun p => 2 < p),
        if p = 2 then (4 : ℝ) else gaussOddPrimeFactor p) = gaussOddProduct q := by
      apply prod_congr rfl
      intro p hp
      exact ite_eq_right (ne_of_gt (mem_filter.mp hp).2)
    rwa [he] at hb
  · have hs : q.primeFactors.filter (fun p => 2 < p) = q.primeFactors := by
      apply filter_eq_self.mpr
      intro p hp
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      have hp2 : p ≠ 2 := fun he => h2 (he ▸ hp)
      omega
    have he : (∏ p ∈ q.primeFactors, if p = 2 then (4 : ℝ) else gaussOddPrimeFactor p) =
        gaussOddProduct q := by
      unfold gaussOddProduct
      rw [hs]
      apply prod_congr rfl
      intro p hp
      have hp2 : p ≠ 2 := by
        intro he
        subst p
        exact h2 hp
      exact ite_eq_right hp2
    rw [he] at hb
    nlinarith [gaussOddProduct_nonneg q]

/-- Equation e:sproductbound, with explicit constant four and every positive q. -/
theorem principalSquareSum_finite_product_bound (q : ℕ) [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    ‖principalSquareSum q a‖ ≤ (4 / Real.sqrt q) * gaussOddProduct q := by
  have he := (scaled_norm_principalSquareSum_le_product q a ha).trans
    (gaussProductBound_le_oddProduct q)
  have hq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos q)
  calc
    _ ≤ (4 * gaussOddProduct q) / Real.sqrt q :=
      (le_div_iff₀ hq).mpr (by simpa only [mul_comm] using he)
    _ = _ := by ring

theorem principalSquareSum_finite_product_bound_int (q : ℕ) [NeZero q] (a : ℤ)
    (ha : IsCoprime (q : ℤ) a) :
    ‖principalSquareSum q (a : ZMod q)‖ ≤ (4 / Real.sqrt q) * gaussOddProduct q := by
  exact principalSquareSum_finite_product_bound q (a : ZMod q)
    ((ZMod.coe_int_isUnit_iff_isCoprime a q).mpr ha)

/-- The source's support statement as an explicit odd squarefree decomposition. -/
theorem principalSquareSum_support_decomposition (q : ℕ) [NeZero q]
    (a : ZMod q) (ha : IsUnit a) (hne : principalSquareSum q a ≠ 0) :
    ∃ j d : ℕ, j ≤ 3 ∧ 0 < d ∧ ¬2 ∣ d ∧ Squarefree d ∧ q = 2 ^ j * d := by
  classical
  have hs := principalSquareSum_support q a ha hne
  let d := q / 2 ^ q.factorization 2
  have hd : 0 < d := Nat.ordCompl_pos 2 (NeZero.ne q)
  have hodd : ¬2 ∣ d := Nat.not_dvd_ordCompl Nat.prime_two (NeZero.ne q)
  have hsf : Squarefree d := by
    apply Nat.squarefree_of_factorization_le_one hd.ne'
    intro p
    dsimp only [d]
    rw [Nat.factorization_ordCompl, Finsupp.erase_apply]
    by_cases hp2 : p = 2
    · simp [hp2]
    · rw [ite_eq_right hp2]
      by_cases hz : q.factorization p = 0
      · simp [hz]
      · have hm : p ∈ q.primeFactors := by
          change p ∈ q.factorization.support
          exact Finsupp.mem_support_iff.mpr hz
        rw [hs.2 p hm hp2]
  exact ⟨q.factorization 2, d, hs.1, hd, hodd, hsf,
    (Nat.ordProj_mul_ordCompl_eq_self q 2).symm⟩

end PrimeSquares
