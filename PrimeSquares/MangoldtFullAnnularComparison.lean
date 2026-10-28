import PrimeSquares.MangoldtAnnularPositiveFamily
import PrimeSquares.PrimeFullMaximalComparison
import PrimeSquares.RestrictedToModular
import PrimeSquares.NearOneGaugeComparison

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem mangoldt_annular_indicator_kernel (j : ℕ) (F : Finset ℤ) (x : ℤ) :
    positiveAverage mangoldtAnnularDyadicFamily j (finiteIndicator F) x =
      indicatorConvolution (annularWeightedSquareAverageKernel ((2 : ℕ)^j)
        ArithmeticFunction.vonMangoldt) F x := by
  have h := annularWeightedSquareAverage_finiteInput (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    ((2 : ℕ)^j) ArithmeticFunction.vonMangoldt F (fun _ => 1) x
  rw [finiteConvolution_indicator, finiteInputLp_one] at h
  rw [h]
  exact mangoldtAnnularDyadicFamily_apply j (finiteIndicatorLp F 2) x

theorem mangoldt_full_dyadic_annular_bound (F : Finset ℤ) (x : ℤ) (k : ℕ) :
    ‖indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^k)
      ArithmeticFunction.vonMangoldt) F x‖ ≤
      2*positiveMaximal mangoldtAnnularDyadicFamily (finiteIndicator F) x := by
  let B := positiveMaximal mangoldtAnnularDyadicFamily (finiteIndicator F) x
  have hB : 0 ≤ B := (positiveMaximal_indicator_bound mangoldtAnnularDyadicFamily F x).1
  induction k with
  | zero =>
    have he : indicatorConvolution (weightedSquareAverageKernel 1 ArithmeticFunction.vonMangoldt) F x = 0 := by
      simp [indicatorConvolution, weightedSquareAverageKernel, finiteSquareKernel,
        show (Ioc 0 1 : Finset ℕ) = {1} by decide]
    simp only [pow_zero, he, norm_zero]
    positivity
  | succ k ih =>
    have hd := annular_indicator_two_mul ((2 : ℕ)^k) ArithmeticFunction.vonMangoldt F x
    rw [Nat.mul_comm 2 ((2 : ℕ)^k)] at hd
    have he : indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^k*2)
        ArithmeticFunction.vonMangoldt) F x =
      indicatorConvolution (annularWeightedSquareAverageKernel ((2 : ℕ)^k*2)
        ArithmeticFunction.vonMangoldt) F x+(1/2 : ℂ)*
          indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^k) ArithmeticFunction.vonMangoldt) F x := by
      rw [hd]; ring
    have hann := positiveMaximal_dominates mangoldtAnnularDyadicFamily (by norm_num : (0 : ℝ) ≤ 1)
      (finiteIndicator_norm_le_one F) (k+1) x
    rw [mangoldt_annular_indicator_kernel, pow_succ] at hann
    rw [pow_succ, he]
    calc
      _ ≤ ‖indicatorConvolution (annularWeightedSquareAverageKernel ((2 : ℕ)^k*2)
          ArithmeticFunction.vonMangoldt) F x‖+(1/2 : ℝ)*
          ‖indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^k) ArithmeticFunction.vonMangoldt) F x‖ := by
        simpa only [norm_mul, show ‖(1/2 : ℂ)‖ = (1/2 : ℝ) by norm_num] using norm_add_le
          (indicatorConvolution (annularWeightedSquareAverageKernel ((2 : ℕ)^k*2) ArithmeticFunction.vonMangoldt) F x)
          ((1/2 : ℂ)*indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^k) ArithmeticFunction.vonMangoldt) F x)
      _ ≤ B+(1/2 : ℝ)*(2*B) := add_le_add hann (mul_le_mul_of_nonneg_left ih (by norm_num))
      _ = _ := by ring

theorem mangoldt_full_annular_maximal_bound (F : Finset ℤ) (x : ℤ) :
    positiveMaximal mangoldtPositiveFamily (finiteIndicator F) x ≤
      4*positiveMaximal mangoldtAnnularDyadicFamily (finiteIndicator F) x := by
  apply ciSup_le
  intro n
  rw [mangoldtPositiveFamily_apply, primeSquareAverageValue_indicator_kernel]
  let N := n+2
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by dsimp [N]; omega)
  obtain ⟨k, _hk, hkN, hNk⟩ := exists_dyadic_below (show (2 : ℝ) ≤ 2*(N : ℝ) by linarith)
  have hNM : N ≤ (2 : ℕ)^k := by exact_mod_cast (show (N : ℝ) ≤ (2 : ℝ)^k by linarith)
  have hMN : (2 : ℕ)^k ≤ 2*N := by exact_mod_cast hkN
  exact (fullPrimeIndicator_cutoff_bound (by dsimp [N]; omega) hNM hMN F x).trans
    (by nlinarith [mangoldt_full_dyadic_annular_bound F x k])

theorem positiveRestrictedGauge_mangoldt_full {Cg Rg : ℝ} (hC : 0 ≤ Cg) (hR : 0 ≤ Rg)
    (H : PositiveRestrictedGauge mangoldtAnnularDyadicFamily Cg Rg) :
    PositiveRestrictedGauge mangoldtPositiveFamily Cg
      (Rg*(4*Real.exp (4*Cg*Real.log 2))^2) := by
  intro F t ht D
  have ht0 : 0 < t := by linarith
  have hdist := H F (4*t) (by linarith) D
  have hpsi2 := nearOnePsi_doubling hC (show 0 ≤ t by linarith)
  have hpsi4 := nearOnePsi_doubling hC (show 0 ≤ 2*t by linarith)
  rw [show 2*(2*t) = 4*t by ring] at hpsi4
  have hpsi : nearOnePsi Cg (4*t) ≤ (4*Real.exp (4*Cg*Real.log 2))^2*nearOnePsi Cg t := by
    have h := mul_le_mul_of_nonneg_left hpsi2 (show 0 ≤ 4*Real.exp (4*Cg*Real.log 2) by positivity)
    nlinarith
  have hsub : finiteDistribution D (positiveMaximal mangoldtPositiveFamily (finiteIndicator F)) (1/t) ≤
      finiteDistribution D (positiveMaximal mangoldtAnnularDyadicFamily (finiteIndicator F)) (1/(4*t)) := by
    classical
    apply Nat.cast_le.mpr
    apply card_le_card
    intro x hx
    obtain ⟨hx, hval⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨hx, ?_⟩
    have hbound := mangoldt_full_annular_maximal_bound F x
    have he : 4*(1/(4*t)) = 1/t := by ring
    nlinarith
  calc
    _ ≤ Rg*(F.card : ℝ)*nearOnePsi Cg (4*t) := hsub.trans hdist
    _ ≤ Rg*(F.card : ℝ)*((4*Real.exp (4*Cg*Real.log 2))^2*nearOnePsi Cg t) :=
      mul_le_mul_of_nonneg_left hpsi (mul_nonneg hR (Nat.cast_nonneg F.card))
    _ = _ := by ring

end PrimeSquares
