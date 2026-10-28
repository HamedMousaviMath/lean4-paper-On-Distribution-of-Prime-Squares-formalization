import PrimeSquares.PrimeMangoldtSumComparison
import PrimeSquares.RestrictedToModular
import PrimeSquares.NearOneGaugeComparison

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem mangoldt_indicator_partial_sum_bound (m : ℕ) (F : Finset ℤ) (x : ℤ) :
    (∑ n ∈ Ioc 0 m, ArithmeticFunction.vonMangoldt n*(if x-(n : ℤ)^2 ∈ F then 1 else 0)) ≤
      (m : ℝ)*positiveMaximal mangoldtPositiveFamily (finiteIndicator F) x := by
  classical
  have hB := (positiveMaximal_indicator_bound mangoldtPositiveFamily F x).1
  by_cases hm : 2 ≤ m
  · have he : m-2+2 = m := Nat.sub_add_cancel hm
    have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hdom := positiveMaximal_dominates mangoldtPositiveFamily (by norm_num : (0 : ℝ) ≤ 1)
      (finiteIndicator_norm_le_one F) (m-2) x
    rw [positiveAverage_indicator_real] at hdom
    change (∑ n ∈ Ioc 0 (m-2+2), (((m-2+2 : ℕ) : ℝ)⁻¹*ArithmeticFunction.vonMangoldt n)*
      (if x-(n : ℤ)^2 ∈ F then 1 else 0)) ≤ positiveMaximal mangoldtPositiveFamily (finiteIndicator F) x at hdom
    rw [he] at hdom
    have hdom' : (m : ℝ)⁻¹*(∑ n ∈ Ioc 0 m, ArithmeticFunction.vonMangoldt n*
        (if x-(n : ℤ)^2 ∈ F then 1 else 0)) ≤ positiveMaximal mangoldtPositiveFamily (finiteIndicator F) x := by
      simpa only [mul_assoc, ←mul_sum] using hdom
    have h := mul_le_mul_of_nonneg_left hdom' hmp.le
    rw [←mul_assoc, mul_inv_cancel₀ hmp.ne', one_mul] at h
    exact h
  · have he : m = 0 ∨ m = 1 := by omega
    rcases he with rfl | rfl
    · simp
    · simp only [show (Ioc 0 1 : Finset ℕ) = {1} by decide, sum_singleton,
        ArithmeticFunction.vonMangoldt_apply_one, zero_mul, Nat.cast_one, one_mul]
      exact hB

theorem prime_mangoldt_indicator_maximal_bound (F : Finset ℤ) (x : ℤ) :
    positiveMaximal primePositiveFamily (finiteIndicator F) x ≤
      3072*positiveMaximal mangoldtPositiveFamily (finiteIndicator F) x := by
  classical
  apply ciSup_le
  intro n
  rw [positiveAverage_indicator_real]
  change (∑ p ∈ Nat.primesLE (n+2), (Nat.primeCounting (n+2) : ℝ)⁻¹*
      (if x-(p : ℤ)^2 ∈ F then 1 else 0)) ≤ _
  rw [←mul_sum]
  exact normalized_prime_sum_le_mangoldt_bound (by omega)
    (fun p => if x-(p : ℤ)^2 ∈ F then 1 else 0) (fun _ => by split_ifs <;> norm_num)
    (positiveMaximal_indicator_bound mangoldtPositiveFamily F x).1
    (fun m => mangoldt_indicator_partial_sum_bound m F x)

theorem nearOnePsi_rescale_bound {C a t : ℝ} (hC : 0 ≤ C) (ha : 1 ≤ a) (ht : 0 ≤ t) :
    nearOnePsi C (a*t) ≤
      (a*Real.exp (2*C*Real.log a)*(2*Real.exp (2*C*Real.log 2)))*nearOnePsi C t := by
  have ha0 : 0 ≤ a := by linarith
  have h1 := nearOnePsi_le_density hC (mul_nonneg ha0 ht)
  have h2 := mul_le_mul_of_nonneg_left (nearOneDensity_rescale hC ha ht) (mul_nonneg ha0 ht)
  have h3 := mul_le_mul_of_nonneg_left (nearOnePsi_comparison hC ht)
    (show 0 ≤ a*Real.exp (2*C*Real.log a) by positivity)
  nlinarith

theorem positiveRestrictedGauge_mangoldt_to_prime {Cg Rg : ℝ} (hC : 0 ≤ Cg) (hR : 0 ≤ Rg)
    (H : PositiveRestrictedGauge mangoldtPositiveFamily Cg Rg) :
    PositiveRestrictedGauge primePositiveFamily Cg
      (Rg*(3072*Real.exp (2*Cg*Real.log 3072)*(2*Real.exp (2*Cg*Real.log 2)))) := by
  intro F t ht D
  have ht0 : 0 < t := by linarith
  have hdist := H F (3072*t) (by linarith) D
  have hpsi := nearOnePsi_rescale_bound hC (by norm_num : (1 : ℝ) ≤ 3072) (show 0 ≤ t by linarith)
  have hsub : finiteDistribution D (positiveMaximal primePositiveFamily (finiteIndicator F)) (1/t) ≤
      finiteDistribution D (positiveMaximal mangoldtPositiveFamily (finiteIndicator F)) (1/(3072*t)) := by
    classical
    apply Nat.cast_le.mpr
    apply card_le_card
    intro x hx
    obtain ⟨hx, hval⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨hx, ?_⟩
    have hbound := prime_mangoldt_indicator_maximal_bound F x
    have he : 3072*(1/(3072*t)) = 1/t := by ring
    nlinarith
  calc
    _ ≤ Rg*(F.card : ℝ)*nearOnePsi Cg (3072*t) := hsub.trans hdist
    _ ≤ Rg*(F.card : ℝ)*((3072*Real.exp (2*Cg*Real.log 3072)*(2*Real.exp (2*Cg*Real.log 2)))*nearOnePsi Cg t) :=
      mul_le_mul_of_nonneg_left hpsi (mul_nonneg hR (Nat.cast_nonneg F.card))
    _ = _ := by ring

end PrimeSquares
