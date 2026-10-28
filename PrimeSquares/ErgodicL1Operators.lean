import PrimeSquares.OrliczTruncation
import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option autoImplicit false
open MeasureTheory Filter Finset
open scoped ENNReal Topology
namespace PrimeSquares

noncomputable def ergodicSquareL1Operator {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) (A : PositiveAverageFamily) (n : ℕ) :
    Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ :=
  ∑ j ∈ A.indices n, (A.weight n j : ℂ) •
    (Lp.compMeasurePreservingₗᵢ ℂ (p := 1) (T^[j^2]) (hT.iterate (j^2))).toContinuousLinearMap

theorem ergodicSquareL1Operator_apply {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) (A : PositiveAverageFamily)
    (hA : IsSectionSevenFamily A) (n : ℕ) (f : Lp ℂ 1 μ) :
    (ergodicSquareL1Operator μ T hT A n f : X → ℂ) =ᵐ[μ]
      ergodicPositiveAverage A T n (f : X → ℂ) := by
  let v := fun j => Lp.compMeasurePreserving (E := ℂ) (p := 1) (T^[j^2]) (hT.iterate (j^2)) f
  have he : ergodicSquareL1Operator μ T hT A n f = ∑ j ∈ A.indices n, (A.weight n j : ℂ) • v j := by
    simp only [ergodicSquareL1Operator, _root_.sum_apply, _root_.smul_apply]
    rfl
  rw [he]
  have hj (j : ℕ) : ∀ᵐ x ∂μ, ((A.weight n j : ℂ) • v j) x =
      (A.weight n j : ℂ)*f (T^[j^2] x) := by
    filter_upwards [Lp.coeFn_smul (A.weight n j : ℂ) (v j),
      Lp.coeFn_compMeasurePreserving f (hT.iterate (j^2))] with x hx hc
    rw [hx]
    change (A.weight n j : ℂ)*(v j) x = _
    rw [hc]
    rfl
  filter_upwards [Lp.coeFn_finsetSum (A.indices n) (fun j => (A.weight n j : ℂ) • v j),
    ae_all_iff.mpr hj] with x hx hxs
  rw [hx, ergodicPositiveAverage_square A hA T n]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact hxs j

theorem ergodicPositiveAverage_congr_ae {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) (A : PositiveAverageFamily)
    (hA : IsSectionSevenFamily A) (n : ℕ) {f g : X → ℂ} (hfg : f =ᵐ[μ] g) :
    ergodicPositiveAverage A T n f =ᵐ[μ] ergodicPositiveAverage A T n g := by
  have hj (j : ℕ) : ∀ᵐ x ∂μ, f (T^[j^2] x) = g (T^[j^2] x) :=
    (hT.iterate (j^2)).quasiMeasurePreserving.ae_eq_comp hfg
  filter_upwards [ae_all_iff.mpr hj] with x hx
  rw [ergodicPositiveAverage_square A hA T n, ergodicPositiveAverage_square A hA T n]
  apply Finset.sum_congr rfl
  intro j _
  rw [hx j]

theorem ergodicSquareL1Operator_apply_toLp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) (A : PositiveAverageFamily)
    (hA : IsSectionSevenFamily A) (n : ℕ) {f : X → ℂ} (hf : MemLp f 1 μ) :
    (ergodicSquareL1Operator μ T hT A n (hf.toLp f) : X → ℂ) =ᵐ[μ]
      ergodicPositiveAverage A T n f :=
  (ergodicSquareL1Operator_apply μ T hT A hA n (hf.toLp f)).trans
    (ergodicPositiveAverage_congr_ae μ T hT A hA n hf.coeFn_toLp)

theorem ergodicSquareL1Operator_norm_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) (A : PositiveAverageFamily) (n : ℕ) :
    ‖ergodicSquareL1Operator μ T hT A n‖ ≤ A.mass := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by have h := A.mass_one_le; linarith)
  intro f
  simp only [ergodicSquareL1Operator, _root_.sum_apply, _root_.smul_apply]
  calc
    _ ≤ ∑ j ∈ A.indices n, ‖(A.weight n j : ℂ) •
        Lp.compMeasurePreserving (E := ℂ) (p := 1) (T^[j^2]) (hT.iterate (j^2)) f‖ := norm_sum_le _ _
    _ = ∑ j ∈ A.indices n, A.weight n j*‖f‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (A.nonnegative n j hj),
        Lp.norm_compMeasurePreserving]
    _ = (∑ j ∈ A.indices n, A.weight n j)*‖f‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (A.mass_bound n) (norm_nonneg _)

end PrimeSquares
