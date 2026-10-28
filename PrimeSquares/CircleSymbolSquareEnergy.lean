import PrimeSquares.OperatorSquareMaximal
import PrimeSquares.CircleMultipliers

open Finset MeasureTheory
open scoped lp
namespace PrimeSquares

theorem circleL2_square_integrable (f : PrimeCircleL2) :
    Integrable (fun θ : PrimeCircle => ‖f θ‖^2) AddCircle.haarAddCircle :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

theorem circleL2_norm_square (f : PrimeCircleL2) :
    ‖f‖^2=∫ θ : PrimeCircle,‖f θ‖^2 ∂AddCircle.haarAddCircle := by
  rw [←real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem circleMultiply_norm_square (m : C(PrimeCircle, ℂ)) (f : PrimeCircleL2) :
    ‖circleMultiply m f‖^2=∫ θ : PrimeCircle,‖m θ‖^2*‖f θ‖^2 ∂AddCircle.haarAddCircle := by
  rw [circleL2_norm_square]
  apply integral_congr_ae
  filter_upwards [circleMultiply_ae m f] with θ hθ
  rw [hθ,norm_mul,mul_pow]

theorem circleMultiply_finite_square_energy {ι : Type*} (J : Finset ι) (m : ι → C(PrimeCircle, ℂ))
    {B : ℝ} (hm : ∀ θ : PrimeCircle,(∑ j ∈ J,‖m j θ‖^2) ≤ B^2) (f : PrimeCircleL2) :
    (∑ j ∈ J,‖circleMultiply (m j) f‖^2) ≤ B^2*‖f‖^2 := by
  have hi (j : ι) : Integrable (fun θ : PrimeCircle => ‖m j θ‖^2*‖f θ‖^2) AddCircle.haarAddCircle := by
    apply (circleL2_square_integrable (circleMultiply (m j) f)).congr
    filter_upwards [circleMultiply_ae (m j) f] with θ hθ
    rw [hθ,norm_mul,mul_pow]
  calc
    _ = ∫ θ : PrimeCircle,∑ j ∈ J,‖m j θ‖^2*‖f θ‖^2 ∂AddCircle.haarAddCircle := by
      simp_rw [circleMultiply_norm_square]
      rw [integral_finsetSum J (fun j _ => hi j)]
    _ ≤ ∫ θ : PrimeCircle,B^2*‖f θ‖^2 ∂AddCircle.haarAddCircle := by
      apply integral_mono (integrable_finsetSum J (fun j _ => hi j)) ((circleL2_square_integrable f).const_mul (B^2))
      intro θ
      change (∑ j ∈ J,‖m j θ‖^2*‖f θ‖^2) ≤ B^2*‖f θ‖^2
      rw [←sum_mul]
      exact mul_le_mul_of_nonneg_right (hm θ) (sq_nonneg _)
    _ = _ := by rw [integral_const_mul,←circleL2_norm_square]

theorem circleSymbols_operator_square_energy (m : ℕ → C(PrimeCircle, ℂ)) {B : ℝ}
    (hm : ∀ J : Finset ℕ,∀ θ : PrimeCircle,(∑ j ∈ J,‖m j θ‖^2) ≤ B^2) :
    OperatorSquareEnergyBound (fun j => integerMultiplier (m j)) B := by
  intro f J
  calc
    _ = ∑ j ∈ J,‖circleMultiply (m j) (integerFourier f)‖^2 := by
      apply sum_congr rfl
      intro j _
      rw [integerMultiplier_apply,integerFourier.symm.norm_map]
    _ ≤ B^2*‖integerFourier f‖^2 := circleMultiply_finite_square_energy J m (hm J) _
    _ = _ := by rw [integerFourier_norm]

end PrimeSquares
