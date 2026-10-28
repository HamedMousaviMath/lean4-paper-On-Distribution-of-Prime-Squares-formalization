import PrimeSquares.ActualPositiveSquareFamilies
import PrimeSquares.IWThreeFamilyRestrictedGauge
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
open MeasureTheory Set Finset
open scoped ENNReal Topology
namespace PrimeSquares

noncomputable def integerSystemIterate {X : Type*} [MeasurableSpace X] (T : X ≃ᵐ X) (z : ℤ) : X → X :=
  if 0 ≤ z then (T : X → X)^[z.toNat] else (T.symm : X → X)^[(-z).toNat]

@[fun_prop]
theorem integerSystemIterate_measurable {X : Type*} [MeasurableSpace X] (T : X ≃ᵐ X) (z : ℤ) :
    Measurable (integerSystemIterate T z) := by
  unfold integerSystemIterate
  split_ifs
  · exact T.measurable.iterate _
  · exact T.symm.measurable.iterate _

theorem integerSystemIterate_square {X : Type*} [MeasurableSpace X] (T : X ≃ᵐ X) (j : ℕ) :
    integerSystemIterate T ((j : ℤ)^2) = (T : X → X)^[j^2] := by
  unfold integerSystemIterate
  rw [ite_eq_left (sq_nonneg (j : ℤ))]
  have he : ((j : ℤ)^2).toNat = j^2 := by norm_cast
  rw [he]

noncomputable def ergodicPositiveAverage {X : Type*} [MeasurableSpace X]
    (A : PositiveAverageFamily) (T : X ≃ᵐ X) (n : ℕ) (f : X → ℂ) (x : X) : ℂ :=
  ∑ j ∈ A.indices n, (A.weight n j : ℂ)*f (integerSystemIterate T (A.shift j) x)

noncomputable def ergodicMaximalENorm {X : Type*} [MeasurableSpace X]
    (A : PositiveAverageFamily) (T : X ≃ᵐ X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ n : ℕ, ‖ergodicPositiveAverage A T n f x‖ₑ

noncomputable def ergodicMaximalValue {X : Type*} [MeasurableSpace X]
    (A : PositiveAverageFamily) (T : X ≃ᵐ X) (f : X → ℂ) (x : X) : ℝ :=
  (ergodicMaximalENorm A T f x).toReal

theorem sectionSevenFamily_shift (A : PositiveAverageFamily) (hA : IsSectionSevenFamily A) (j : ℕ) :
    A.shift j = (j : ℤ)^2 := by
  rcases hA with rfl | rfl | rfl <;> rfl

theorem ergodicPositiveAverage_square {X : Type*} [MeasurableSpace X]
    (A : PositiveAverageFamily) (hA : IsSectionSevenFamily A) (T : X ≃ᵐ X)
    (n : ℕ) (f : X → ℂ) (x : X) :
    ergodicPositiveAverage A T n f x = ∑ j ∈ A.indices n, (A.weight n j : ℂ)*f (T^[j^2] x) := by
  unfold ergodicPositiveAverage
  simp_rw [sectionSevenFamily_shift A hA, integerSystemIterate_square]

theorem ergodicPositiveAverage_measurable {X : Type*} [MeasurableSpace X]
    (A : PositiveAverageFamily) (T : X ≃ᵐ X) (n : ℕ) {f : X → ℂ} (hf : Measurable f) :
    Measurable (ergodicPositiveAverage A T n f) := by
  unfold ergodicPositiveAverage
  fun_prop

theorem ergodicMaximalENorm_measurable {X : Type*} [MeasurableSpace X]
    (A : PositiveAverageFamily) (T : X ≃ᵐ X) {f : X → ℂ} (hf : Measurable f) :
    Measurable (ergodicMaximalENorm A T f) :=
  Measurable.iSup (fun n => (ergodicPositiveAverage_measurable A T n hf).enorm)

theorem ergodicPositiveAverage_sub {X : Type*} [MeasurableSpace X]
    (A : PositiveAverageFamily) (T : X ≃ᵐ X) (n : ℕ) (f g : X → ℂ) (x : X) :
    ergodicPositiveAverage A T n (f-g) x =
      ergodicPositiveAverage A T n f x-ergodicPositiveAverage A T n g x := by
  simp only [ergodicPositiveAverage, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem ergodicPositiveAverage_norm_bound {X : Type*} [MeasurableSpace X]
    (A : PositiveAverageFamily) (T : X ≃ᵐ X) {f : X → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ x, ‖f x‖ ≤ B) (n : ℕ) (x : X) :
    ‖ergodicPositiveAverage A T n f x‖ ≤ A.mass*B := by
  calc
    _ ≤ ∑ j ∈ A.indices n, ‖(A.weight n j : ℂ)*f (integerSystemIterate T (A.shift j) x)‖ := norm_sum_le _ _
    _ = ∑ j ∈ A.indices n, A.weight n j*‖f (integerSystemIterate T (A.shift j) x)‖ := by
      apply sum_congr rfl
      intro j hj
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (A.nonnegative n j hj)]
    _ ≤ ∑ j ∈ A.indices n, A.weight n j*B :=
      sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hf _) (A.nonnegative n j hj))
    _ = (∑ j ∈ A.indices n, A.weight n j)*B := (sum_mul _ _ _).symm
    _ ≤ A.mass*B := mul_le_mul_of_nonneg_right (A.mass_bound n) hB

theorem ergodicMaximalENorm_dominates {X : Type*} [MeasurableSpace X]
    (A : PositiveAverageFamily) (T : X ≃ᵐ X) (f : X → ℂ) (n : ℕ) (x : X) :
    ‖ergodicPositiveAverage A T n f x‖ₑ ≤ ergodicMaximalENorm A T f x :=
  le_iSup (fun j : ℕ => ‖ergodicPositiveAverage A T j f x‖ₑ) n

theorem ergodicMaximalENorm_bounded {X : Type*} [MeasurableSpace X]
    (A : PositiveAverageFamily) (T : X ≃ᵐ X) {f : X → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ x, ‖f x‖ ≤ B) (x : X) :
    ergodicMaximalENorm A T f x ≤ ENNReal.ofReal (A.mass*B) := by
  apply iSup_le
  intro n
  rw [←ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (ergodicPositiveAverage_norm_bound A T hB hf n x)

end PrimeSquares
