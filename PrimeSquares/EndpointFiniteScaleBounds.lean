import PrimeSquares.PrimeSquareAverages
import PrimeSquares.HighLowNotation

open Finset
namespace PrimeSquares

theorem mangoldtSquareKernel_point_bound {N : ℕ} (hN : 0 < N) (z : ℤ) :
    ‖annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt z‖ ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log (N : ℝ) ≤ N := (Real.log_le_sub_one_of_pos hNr).trans (by linarith)
  have hb := finiteSquareKernel_norm_le (Ioc (N/2) N) (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)
    (Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt hN)) ArithmeticFunction.vonMangoldt
    (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    (fun n hn => mangoldt_weight_le_log (annularIndices_subset N hn)) z
  exact hb.trans (by
    calc
      _ ≤ (N : ℝ)⁻¹*(N : ℝ) := mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hNr.le)
      _ = 1 := inv_mul_cancel₀ hNr.ne')

theorem restricted_pairing_card_bound {K : ℤ → ℂ} {B : ℝ}
    (hK : ∀ z,‖K z‖ ≤ B) (F G : Finset ℤ) :
    ‖restrictedKernelPairing K F G‖ ≤ B*(F.card : ℝ)*(G.card : ℝ) := by
  calc
    _ ≤ ∑ x ∈ G,‖indicatorConvolution K F x‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ G,(F.card : ℝ)*B := sum_le_sum (fun x _ => indicatorConvolution_norm_le K F B hK x)
    _ = _ := by simp;ring

theorem annular_endpoint_finite_scale {N T : ℕ} (hN : 0 < N) (hNT : N ≤ T)
    {c : ℝ} (hc : 0 ≤ c) (F G : Finset ℤ)
    (hFG : (F.card : ℝ)*(G.card : ℝ) ≤ ((N : ℝ)^2)^2) :
    ‖restrictedKernelPairing (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F G‖/
      ((N : ℝ)^2) ≤ (T : ℝ)^2*(finiteSetDensity ((N : ℝ)^2) F G)^(2/3 : ℝ)*
        paperPhi c (1/2) (finiteSetDensity ((N : ℝ)^2) F G) := by
  have hS : 0 < (N : ℝ)^2 := by positivity
  have hδ : 0 ≤ finiteSetDensity ((N : ℝ)^2) F G := by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)
  have hδ1 : finiteSetDensity ((N : ℝ)^2) F G ≤ 1 := (div_le_one (sq_pos_of_pos hS)).mpr hFG
  have hpow : finiteSetDensity ((N : ℝ)^2) F G ≤ (finiteSetDensity ((N : ℝ)^2) F G)^(2/3 : ℝ) := by
    by_cases hz : finiteSetDensity ((N : ℝ)^2) F G=0
    · rw [hz,Real.zero_rpow (by norm_num : (2/3 : ℝ) ≠ 0)]
    · have h := Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne hδ (Ne.symm hz)) hδ1 (by norm_num : (2/3 : ℝ) ≤ 1)
      simpa only [Real.rpow_one] using h
  have hb := restricted_pairing_card_bound (mangoldtSquareKernel_point_bound hN) F G
  have hST : (N : ℝ)^2 ≤ (T : ℝ)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg N) (by exact_mod_cast hNT) 2
  calc
    _ ≤ ((F.card : ℝ)*(G.card : ℝ))/((N : ℝ)^2) :=
      div_le_div_of_nonneg_right (by simpa only [one_mul] using hb) hS.le
    _ = ((N : ℝ)^2)*finiteSetDensity ((N : ℝ)^2) F G := by dsimp [finiteSetDensity];field_simp
    _ ≤ (T : ℝ)^2*(finiteSetDensity ((N : ℝ)^2) F G)^(2/3 : ℝ) :=
      mul_le_mul hST hpow hδ (sq_nonneg _)
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (paperPhi_one_le hc _ _)

end PrimeSquares
