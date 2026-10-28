import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# An elementary upper bound for a finite prime product

We prove a sufficient Mertens-type upper bound without assuming Mertens'
theorem. A factorial bounds sum(log p / p); the logarithmic moment of the
squarefree subset expansion then concentrates half its mass below Q^6.
The truncated mass is bounded by the harmonic sum.
-/

open Finset

namespace PrimeSquares

/-- The first term of Legendre's formula suffices here. -/
theorem div_le_factorization_factorial (N p : ℕ) (hp : p.Prime) :
    N / p ≤ N.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (show Nat.log p N < Nat.log p N + 2 by omega)]
  have hm : 1 ∈ Ico 1 (Nat.log p N + 2) := by simp
  simpa using (single_le_sum (fun i _ => Nat.zero_le (N / p ^ i)) hm)

/-- Sum log(p) over a finite prime set below N, using the primorial bound. -/
theorem sum_log_primes_le (S : Finset ℕ) (N : ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N) :
    (∑ p ∈ S, Real.log (p : ℝ)) ≤ (N : ℝ) * Real.log 4 := by
  have hs : S ⊆ Nat.primesLE N := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(hS p hp).2, (hS p hp).1⟩
  calc
    _ ≤ ∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg hs
      intro p hp _
      exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
    _ = Real.log (primorial N : ℝ) := by
      rw [primorial_eq_prod_primesLE, Nat.cast_prod,
        Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primesLE hp).ne_zero)]
    _ ≤ Real.log ((4 : ℝ) ^ N) := by
      apply Real.log_le_log
      · exact_mod_cast primorial_pos N
      · exact_mod_cast primorial_le_four_pow N
    _ = _ := Real.log_pow _ _

/-- A factorial bounds the logarithmically weighted reciprocal-prime sum. -/
theorem sum_log_div_prime_le (S : Finset ℕ) (N : ℕ) (hN : 0 < N)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N) :
    (∑ p ∈ S, Real.log (p : ℝ) / p) ≤ Real.log N + Real.log 4 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog (p : ℕ) (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hfac : (∑ p ∈ S, (N / p : ℕ) * Real.log (p : ℝ)) ≤
      Real.log (N.factorial : ℝ) := by
    calc
      _ ≤ ∑ p ∈ S, (N.factorial.factorization p : ℝ) * Real.log (p : ℝ) := by
        apply sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast div_le_factorization_factorial N p (hS p hp).1)
          (hlog p (hS p hp).1)
      _ ≤ ∑ p ∈ N.factorial.primeFactors,
          (N.factorial.factorization p : ℝ) * Real.log (p : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Nat.mem_primeFactors.mpr ⟨(hS p hp).1,
            (hS p hp).1.dvd_factorial.mpr (hS p hp).2, Nat.factorial_ne_zero _⟩
        · intro p hp _
          exact mul_nonneg (Nat.cast_nonneg _) (hlog p (Nat.prime_of_mem_primeFactors hp))
      _ = _ := (Real.log_nat_eq_sum_factorization _).symm
  have hfloor : (N : ℝ) * (∑ p ∈ S, Real.log (p : ℝ) / p) ≤
      (∑ p ∈ S, (N / p : ℕ) * Real.log (p : ℝ)) + ∑ p ∈ S, Real.log (p : ℝ) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    have hp' : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
    have hd : (N : ℝ) / p ≤ (N / p : ℕ) + 1 := by
      apply (div_le_iff₀ hp').mpr
      have he := Nat.lt_mul_div_succ N (hS p hp).1.pos
      exact le_of_lt (by simpa only [mul_comm] using (show (N : ℝ) < (p : ℝ) * ((N / p : ℕ) + 1) by exact_mod_cast he))
    have ht := mul_le_mul_of_nonneg_right hd (hlog p (hS p hp).1)
    simpa only [add_mul, one_mul, div_mul_eq_mul_div, mul_div_assoc, mul_comm] using ht
  have hfactlog : Real.log (N.factorial : ℝ) ≤ (N : ℝ) * Real.log N := by
    calc
      _ ≤ Real.log ((N : ℝ) ^ N) := by
        apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
        exact_mod_cast Nat.factorial_le_pow N
      _ = _ := Real.log_pow _ _
  apply (mul_le_mul_iff_right₀ hN').mp
  nlinarith [sum_log_primes_le S N hS]

/-- Logarithmic moments of a finite product, proved by subset induction. -/
theorem weighted_powerset_moment (S : Finset ℕ) (f g : ℕ → ℝ)
    (hf : ∀ p ∈ S, 1 + f p ≠ 0) :
    (∑ t ∈ S.powerset, (∏ p ∈ t, f p) * ∑ p ∈ t, g p) =
      (∏ p ∈ S, (1 + f p)) * ∑ p ∈ S, f p * g p / (1 + f p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hS : ∀ p ∈ S, 1 + f p ≠ 0 := fun p hp => hf p (mem_insert_of_mem hp)
    have ha0 : 1 + f a ≠ 0 := hf a (mem_insert_self _ _)
    have he (t : Finset ℕ) (ht : t ∈ S.powerset) :
        (∏ p ∈ insert a t, f p) * ∑ p ∈ insert a t, g p =
          (f a * g a) * (∏ p ∈ t, f p) +
            f a * ((∏ p ∈ t, f p) * ∑ p ∈ t, g p) := by
      have hat : a ∉ t := fun h => ha (mem_powerset.mp ht h)
      rw [prod_insert hat, sum_insert hat]
      ring
    rw [sum_powerset_insert ha]
    calc
      _ = (∑ t ∈ S.powerset, (∏ p ∈ t, f p) * ∑ p ∈ t, g p) +
          ∑ t ∈ S.powerset, ((f a * g a) * (∏ p ∈ t, f p) +
            f a * ((∏ p ∈ t, f p) * ∑ p ∈ t, g p)) := by
        congr 1
        exact sum_congr rfl he
      _ = _ := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← prod_one_add, ih hS,
          prod_insert ha, sum_insert ha]
        field_simp
        ring

def subsetProduct (t : Finset ℕ) : ℕ := ∏ p ∈ t, p

noncomputable def primeSubsetMass (S : Finset ℕ) : ℝ := ∏ p ∈ S, (1 + (p : ℝ)⁻¹)

theorem primeSubsetMass_expansion (S : Finset ℕ) :
    primeSubsetMass S = ∑ t ∈ S.powerset, (subsetProduct t : ℝ)⁻¹ := by
  rw [primeSubsetMass, prod_one_add]
  apply sum_congr rfl
  intro t _
  simp [subsetProduct, Nat.cast_prod, prod_inv_distrib]

theorem subsetProduct_pos (S t : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (ht : t ⊆ S) :
    0 < subsetProduct t := by
  exact prod_pos (fun p hp => (hS p (ht hp)).pos)

/-- Distinct subsets of a set of primes have distinct integer products. -/
theorem subsetProduct_injective (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Set.InjOn subsetProduct (↑S.powerset : Set (Finset ℕ)) := by
  intro t ht u hu he
  have ht' : (subsetProduct t).primeFactors = t :=
    Nat.primeFactors_prod (fun p hp => hS p (mem_powerset.mp ht hp))
  have hu' : (subsetProduct u).primeFactors = u :=
    Nat.primeFactors_prod (fun p hp => hS p (mem_powerset.mp hu hp))
  rw [← ht', ← hu', he]

/-- The first logarithmic moment of the squarefree reciprocal mass. -/
theorem primeSubsetMass_log_moment (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ t ∈ S.powerset, Real.log (subsetProduct t : ℝ) / subsetProduct t) =
      primeSubsetMass S * ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) + 1) := by
  have he (t : Finset ℕ) (ht : t ∈ S.powerset) :
      Real.log (subsetProduct t : ℝ) / subsetProduct t =
        (∏ p ∈ t, (p : ℝ)⁻¹) * ∑ p ∈ t, Real.log (p : ℝ) := by
    rw [subsetProduct, Nat.cast_prod, Real.log_prod
      (fun p hp => by exact_mod_cast (hS p (mem_powerset.mp ht hp)).ne_zero)]
    rw [prod_inv_distrib]
    ring
  rw [sum_congr rfl he, weighted_powerset_moment]
  · congr 1
    apply sum_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hS p hp).ne_zero
    field_simp
  · intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
    positivity

/-- Small products of distinct primes contribute at most the harmonic sum. -/
theorem primeSubsetMass_small_le_harmonic (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (T : ℕ) :
    (∑ t ∈ S.powerset with subsetProduct t ≤ T, (subsetProduct t : ℝ)⁻¹) ≤
      (harmonic T : ℝ) := by
  classical
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_natCast]
  apply sum_le_sum_of_injOn subsetProduct
  · exact (subsetProduct_injective S hS).mono (filter_subset _ _)
  · intro d hd
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hd
    obtain ⟨ht, hT⟩ := mem_filter.mp ht
    exact mem_Icc.mpr ⟨subsetProduct_pos S t hS (mem_powerset.mp ht), hT⟩
  · intro t _
    exact le_rfl
  · intro d _ _
    positivity

/-- The mean logarithm is at most three times log(Q). -/
theorem primeSubsetMass_log_moment_le (S : Finset ℕ) (Q : ℕ) (hQ : 3 ≤ Q)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ Q) :
    (∑ t ∈ S.powerset, Real.log (subsetProduct t : ℝ) / subsetProduct t) ≤
      primeSubsetMass S * (3 * Real.log Q) := by
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have h4 : Real.log 4 ≤ 2 * Real.log Q := by
    calc
      _ ≤ Real.log ((Q : ℝ) ^ 2) := by
        apply Real.log_le_log (by norm_num)
        have hq : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
        nlinarith
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [primeSubsetMass_log_moment S hprime]
  apply mul_le_mul_of_nonneg_left _ (by unfold primeSubsetMass; positivity)
  calc
    _ ≤ ∑ p ∈ S, Real.log (p : ℝ) / p := by
      apply sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_left
        (Real.log_nonneg (by exact_mod_cast (hprime p hp).one_le))
        (by exact_mod_cast (hprime p hp).pos) (by linarith)
    _ ≤ Real.log Q + Real.log 4 := sum_log_div_prime_le S Q (by omega) hS
    _ ≤ _ := by linarith

/-- At least half the reciprocal subset mass is below Q^6. -/
theorem primeSubsetMass_le_affine_log (S : Finset ℕ) (Q : ℕ) (hQ : 3 ≤ Q)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ Q) :
    primeSubsetMass S ≤ 2 + 12 * Real.log Q := by
  classical
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have hL : 0 < Real.log (Q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  let A : ℝ := ∑ t ∈ S.powerset with subsetProduct t ≤ Q ^ 6, (subsetProduct t : ℝ)⁻¹
  let B : ℝ := ∑ t ∈ S.powerset with ¬subsetProduct t ≤ Q ^ 6, (subsetProduct t : ℝ)⁻¹
  have hsplit : A + B = primeSubsetMass S := by
    rw [primeSubsetMass_expansion]
    exact sum_filter_add_sum_filter_not _ _ _
  have hA : A ≤ 1 + 6 * Real.log Q := by
    calc
      _ ≤ (harmonic (Q ^ 6) : ℝ) := primeSubsetMass_small_le_harmonic S hprime _
      _ ≤ 1 + Real.log (Q ^ 6 : ℕ) := harmonic_le_one_add_log _
      _ = _ := by rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hB : B * (6 * Real.log Q) ≤
      ∑ t ∈ S.powerset, Real.log (subsetProduct t : ℝ) / subsetProduct t := by
    calc
      _ ≤ ∑ t ∈ S.powerset with ¬subsetProduct t ≤ Q ^ 6,
          Real.log (subsetProduct t : ℝ) / subsetProduct t := by
        dsimp only [B]
        rw [sum_mul]
        apply sum_le_sum
        intro t ht
        obtain ⟨ht, hlarge⟩ := mem_filter.mp ht
        have hlog : 6 * Real.log Q ≤ Real.log (subsetProduct t : ℝ) := by
          calc
            _ = Real.log (Q ^ 6 : ℕ) := by rw [Nat.cast_pow, Real.log_pow]; norm_num
            _ ≤ _ := Real.log_le_log (by positivity)
              (by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hlarge)))
        simpa only [div_eq_mul_inv, mul_comm] using
          mul_le_mul_of_nonneg_right hlog (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro t ht _
        have hd := subsetProduct_pos S t hprime (mem_powerset.mp ht)
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hd)) (Nat.cast_nonneg _)
  have hhalf : 2 * B ≤ primeSubsetMass S := by
    apply (mul_le_mul_iff_right₀ hL).mp
    have hm := hB.trans (primeSubsetMass_log_moment_le S Q hQ hS)
    nlinarith
  nlinarith

/-- A quantitative Mertens-type bound sufficient for the paper's logarithmic estimate. -/
theorem primeSubsetMass_le_log (S : Finset ℕ) (Q : ℕ) (hQ : 3 ≤ Q)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ Q) :
    primeSubsetMass S ≤ (12 + 2 / Real.log 3) * Real.log Q := by
  have h3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log (3 : ℝ) ≤ Real.log Q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hQ)
  have htwo : 2 ≤ (2 / Real.log 3) * Real.log Q := by
    calc
      _ = (2 / Real.log 3) * Real.log 3 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  nlinarith [primeSubsetMass_le_affine_log S Q hQ hS]

/-- A telescoping reciprocal sum bounds all correction factors uniformly. -/
theorem reciprocal_consecutive_sum (N : ℕ) :
    (∑ j ∈ range N, (1 : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) =
      1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring

theorem sum_inv_mul_pred_le_one (S : Finset ℕ) (Q : ℕ)
    (hS : ∀ p ∈ S, 2 ≤ p ∧ p ≤ Q) :
    (∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 1 := by
  have hs : (∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤
      ∑ j ∈ range Q, (1 : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
    apply sum_le_sum_of_injOn (fun p => p - 2)
    · intro p hp r hr he
      change p - 2 = r - 2 at he
      have := (hS p hp).1
      have := (hS r hr).1
      omega
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
      have := hS p hp
      exact mem_range.mpr (by omega)
    · intro p hp
      have hc : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := Nat.cast_sub (hS p hp).1
      rw [hc]
      apply le_of_eq
      congr 1
      ring
    · intro j _ _
      positivity
  rw [reciprocal_consecutive_sum] at hs
  have : 0 ≤ (1 : ℝ) / ((Q : ℝ) + 1) := by positivity
  linarith

/-- Separate the leading 1+1/p factor from a summable correction. -/
theorem local_prime_product_majorant (p : ℕ) (hp : 2 ≤ p) :
    1 + ((p : ℝ) + 1) / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      (1 + (p : ℝ)⁻¹) * (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1))) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have he : ((p : ℝ) + 1) / ((p : ℝ) * ((p : ℝ) - 1)) =
      (p : ℝ)⁻¹ + 2 / ((p : ℝ) * ((p : ℝ) - 1)) := by field_simp; ring
  rw [he]
  have ha : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hb : 0 ≤ 2 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    have hsub : 0 ≤ (p : ℝ) - 1 := by linarith
    positivity
  nlinarith [mul_nonneg ha hb]

/-- A uniform logarithmic bound for exactly the product in Lemma 3.20. -/
theorem cohen_prime_product_le_log (S : Finset ℕ) (Q : ℕ) (hQ : 3 ≤ Q)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ Q) :
    (∏ p ∈ S, (1 + ((p : ℝ) + 1) / ((p : ℝ) * ((p : ℝ) - 1)))) ≤
      Real.exp 2 * (12 + 2 / Real.log 3) * Real.log Q := by
  have h2 : ∀ p ∈ S, 2 ≤ p ∧ p ≤ Q := fun p hp => ⟨(hS p hp).1.two_le, (hS p hp).2⟩
  have hf (p : ℕ) : 0 ≤ (2 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    by_cases hp : p = 0
    · simp [hp]
    · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hp)
      have hsub : 0 ≤ (p : ℝ) - 1 := by linarith
      positivity
  have hextra : (∏ p ∈ S, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1)))) ≤ Real.exp 2 := by
    have hs := mul_le_mul_of_nonneg_left (sum_inv_mul_pred_le_one S Q h2) (by norm_num : (0 : ℝ) ≤ 2)
    have hs' : (∑ p ∈ S, (2 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 2 := by
      simpa only [mul_sum, mul_one_div, mul_one] using hs
    exact (Real.prod_one_add_le_exp_sum S hf).trans (Real.exp_le_exp.mpr hs')
  calc
    _ ≤ ∏ p ∈ S, ((1 + (p : ℝ)⁻¹) *
        (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1)))) := by
      apply prod_le_prod₀
      · intro p hp
        have hp' : (2 : ℝ) ≤ p := by exact_mod_cast (h2 p hp).1
        have hsub : 0 ≤ (p : ℝ) - 1 := by linarith
        positivity
      · intro p hp
        exact local_prime_product_majorant p (h2 p hp).1
    _ = primeSubsetMass S * ∏ p ∈ S, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      rw [prod_mul_distrib]
      rfl
    _ ≤ primeSubsetMass S * Real.exp 2 :=
      mul_le_mul_of_nonneg_left hextra (by unfold primeSubsetMass; positivity)
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_right (primeSubsetMass_le_log S Q hQ hS)
        (le_of_lt (Real.exp_pos 2))
      nlinarith

end PrimeSquares
