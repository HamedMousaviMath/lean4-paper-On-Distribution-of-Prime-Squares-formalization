import PrimeSquares.CyclicSquareMeasures

set_option autoImplicit false
open Finset
namespace PrimeSquares

/-- The probability measure obtained by squaring every residue, including
    nonunits. Its normalization is the group order. -/
noncomputable def cyclicFullSquareMeasure (P : ℕ) [NeZero P] (z : ZMod P) : ℂ :=
  (P : ℂ)⁻¹*∑ u : ZMod P, if u^2 = z then 1 else 0

theorem cyclicFullSquareMeasure_test (P : ℕ) [NeZero P] (F : ZMod P → ℂ) :
    ∑ z : ZMod P, cyclicFullSquareMeasure P z*F z =
      (P : ℂ)⁻¹*∑ u : ZMod P, F (u^2) := by
  classical
  simp only [cyclicFullSquareMeasure, mul_assoc]
  rw [←mul_sum]
  congr 1
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  simp [ite_mul]

theorem cyclicFullSquareMeasure_variation_le_one (P : ℕ) [NeZero P] :
    cyclicVariation P (cyclicFullSquareMeasure P) ≤ 1 := by
  classical
  have hP : (0 : ℝ) < P := by exact_mod_cast NeZero.pos P
  calc
    _ = (P : ℝ)⁻¹*∑ z : ZMod P, ‖∑ u : ZMod P, if u^2 = z then (1 : ℂ) else 0‖ := by
      simp only [cyclicVariation, cyclicFullSquareMeasure, norm_mul, norm_inv, norm_natCast]
      rw [mul_sum]
    _ ≤ (P : ℝ)⁻¹*∑ z : ZMod P, ∑ u : ZMod P, ‖if u^2 = z then (1 : ℂ) else 0‖ := by
      apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hP).le
      exact sum_le_sum (fun z _ => norm_sum_le _ _)
    _ = (P : ℝ)⁻¹*∑ _u : ZMod P, (1 : ℝ) := by
      rw [sum_comm]
      congr 1
      apply sum_congr rfl
      intro u _
      simp_rw [apply_ite norm]
      simp
    _ = 1 := by simp [hP.ne']

theorem cyclicFullSquareMeasure_fourier (P : ℕ) [NeZero P] (a : ZMod P) :
    cyclicFourier P (cyclicFullSquareMeasure P) a =
      (P : ℂ)⁻¹*completeQuadraticGaussSum P (-a) := by
  rw [cyclicFourier, cyclicFullSquareMeasure_test]
  simp only [completeQuadraticGaussSum, neg_mul]

theorem cyclicFullSquareMeasure_fourier_norm_le_one (P : ℕ) [NeZero P] (a : ZMod P) :
    ‖cyclicFourier P (cyclicFullSquareMeasure P) a‖ ≤ 1 :=
  (cyclicFourier_norm_le_variation P _ a).trans (cyclicFullSquareMeasure_variation_le_one P)

end PrimeSquares
