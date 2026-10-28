import PrimeSquares.SelectedPrimeSquareOperators
import PrimeSquares.CircleModelOperatorBounds

/-!
# Uniform bounds on every finite range of arithmetic scales

This elementary envelope is used only to include the finite scales below
the error-decay threshold. It is uniform over the real cutoff Q and every
permitted optional Page datum, and assumes no asymptotic estimate.
-/

open Finset
open scoped lp

namespace PrimeSquares

theorem sourceRadius_le_scale {N : ℕ} {Q : ℝ} (hQ : 2 ≤ Q)
    (hb : 2 * (sourceMajorArcScale N Q)^8 ≤ (N : ℝ)^2) :
    sourceMajorArcScale N Q ≤ N := by
  have hR : 1 ≤ sourceMajorArcScale N Q :=
    (by linarith : (1 : ℝ) ≤ Q).trans (sourceMajorArcScale_cutoff_le (by linarith) N)
  have hpow : (sourceMajorArcScale N Q)^2 ≤ (sourceMajorArcScale N Q)^8 :=
    pow_le_pow_right₀ hR (by norm_num)
  apply (sq_le_sq₀ (by linarith : 0 ≤ sourceMajorArcScale N Q) (Nat.cast_nonneg N)).mp
  have h0 : 0 ≤ (sourceMajorArcScale N Q)^8 := by positivity
  linarith

noncomputable def finitePageErrorEnvelope (T : ℕ) : ℝ :=
  1 + (∑ n ∈ range (T+1),
    ‖annularWeightedSquareAverage (P := 2) (by norm_num) n ArithmeticFunction.vonMangoldt‖) +
    ∑ r ∈ sourceRationalCenters T, 3 * (gaussModelConstant * (r.den : ℝ)^(-(5/12 : ℝ)))

theorem finitePageErrorEnvelope_pos (T : ℕ) : 0 < finitePageErrorEnvelope T := by
  have hA : 0 ≤ ∑ n ∈ range (T+1),
      ‖annularWeightedSquareAverage (P := 2) (by norm_num) n ArithmeticFunction.vonMangoldt‖ :=
    sum_nonneg (fun n _ => norm_nonneg _)
  have hM : 0 ≤ ∑ r ∈ sourceRationalCenters T,
      3 * (gaussModelConstant * (r.den : ℝ)^(-(5/12 : ℝ))) := by
    apply sum_nonneg
    intro r _
    have hc := gaussModelConstant_pos
    positivity
  dsimp [finitePageErrorEnvelope]
  linarith

set_option maxHeartbeats 1500000 in
theorem finitePageError_bound {N T : ℕ} (hN : 2 ≤ N) (hNT : N ≤ T)
    {Q : ℝ} (hQ : 2 ≤ Q) (hb : 2 * (sourceMajorArcScale N Q)^8 ≤ (N : ℝ)^2)
    (E : Option PageZeroDatum) :
    ‖circleMajorArcErrorOperator (sourceRationalCenters (sourceMajorArcScale N Q)) N (by omega)
      (sourceInducedCharacter (optionPageConductor 1 E) (optionPageCharacter 1 E))
      (sourceExceptionalSelector (optionPageConductor 1 E) E.isSome) (optionPageBeta E)‖ ≤
      finitePageErrorEnvelope T := by
  let Γ := sourceRationalCenters (sourceMajorArcScale N Q)
  let χ := sourceInducedCharacter (optionPageConductor 1 E) (optionPageCharacter 1 E)
  let κ := sourceExceptionalSelector (optionPageConductor 1 E) E.isSome
  let β := optionPageBeta E
  have hR := sourceRadius_le_scale hQ hb
  have hR0 : 0 ≤ sourceMajorArcScale N Q :=
    (by linarith : (0 : ℝ) ≤ Q).trans (sourceMajorArcScale_cutoff_le (by linarith) N)
  have hΓ : Γ ⊆ sourceRationalCenters T := by
    intro r hr
    obtain ⟨hc, hd⟩ := (mem_sourceRationalCenters hR0 r).mp hr
    exact (mem_sourceRationalCenters (Nat.cast_nonneg T) r).mpr
      ⟨hc, hd.trans (hR.trans (by exact_mod_cast hNT))⟩
  have hModel := circleMajorArcOperator_bound hN Γ χ κ (optionPageBeta_nonneg E)
    (optionPageBeta_le_one E) (fun r _ => sourceExceptionalSelector_norm _ _ r)
  have hModelT : ‖circleMajorArcOperator Γ N (by omega) χ κ β‖ ≤
      ∑ r ∈ sourceRationalCenters T, 3 * (gaussModelConstant * (r.den : ℝ)^(-(5/12 : ℝ))) := by
    apply hModel.trans
    apply sum_le_sum_of_subset_of_nonneg hΓ
    intro r _ _
    have hc := gaussModelConstant_pos
    positivity
  have hAverage : ‖annularWeightedSquareAverage (P := 2) (by norm_num) N ArithmeticFunction.vonMangoldt‖ ≤
      ∑ n ∈ range (T+1), ‖annularWeightedSquareAverage (P := 2) (by norm_num) n ArithmeticFunction.vonMangoldt‖ :=
    single_le_sum (f := fun n : ℕ =>
      ‖annularWeightedSquareAverage (P := 2) (by norm_num) n ArithmeticFunction.vonMangoldt‖)
      (s := range (T+1)) (a := N)
      (fun n _ => norm_nonneg _) (mem_range.mpr (by omega))
  have he : circleMajorArcErrorOperator Γ N (by omega) χ κ β =
      annularWeightedSquareAverage (P := 2) (by norm_num) N ArithmeticFunction.vonMangoldt -
        circleMajorArcOperator Γ N (by omega) χ κ β := by
    rw [eq_sub_iff_add_eq]
    simpa only [add_comm] using (circleModel_operator_decomposition Γ N (by omega) χ κ β).symm
  change ‖circleMajorArcErrorOperator Γ N (by omega) χ κ β‖ ≤ _
  rw [he]
  apply (norm_sub_le _ _).trans
  dsimp [finitePageErrorEnvelope]
  linarith

end PrimeSquares
