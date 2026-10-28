import PrimeSquares.FourierGaussCompatibility

set_option autoImplicit false
open Finset
namespace PrimeSquares

/-- Coefficients of an actual complex measure on the finite cyclic group.
The normalization is by the number of units, not by the group order. -/
noncomputable def cyclicSquareMeasure (P : ℕ) [NeZero P]
    (χ : DirichletCharacter ℂ P) (z : ZMod P) : ℂ :=
  (P.totient : ℂ)⁻¹ * ∑ u : (ZMod P)ˣ, if (u : ZMod P)^2=z then χ u else 0

noncomputable def cyclicVariation (P : ℕ) [NeZero P] (ν : ZMod P → ℂ) : ℝ :=
  ∑ z : ZMod P, ‖ν z‖

noncomputable def cyclicFourier (P : ℕ) [NeZero P] (ν : ZMod P → ℂ) (a : ZMod P) : ℂ :=
  ∑ z : ZMod P, ν z * ZMod.stdAddChar (-a*z)

theorem cyclicSquareMeasure_test (P : ℕ) [NeZero P]
    (χ : DirichletCharacter ℂ P) (F : ZMod P → ℂ) :
    ∑ z : ZMod P, cyclicSquareMeasure P χ z * F z =
      (P.totient : ℂ)⁻¹ * ∑ u : (ZMod P)ˣ, χ u * F ((u : ZMod P)^2) := by
  classical
  simp only [cyclicSquareMeasure, mul_assoc]
  rw [←mul_sum]
  congr 1
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  simp [ite_mul]

theorem cyclicVariation_nonneg (P : ℕ) [NeZero P] (ν : ZMod P → ℂ) :
    0 ≤ cyclicVariation P ν := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem cyclicSquareMeasure_variation_le_one (P : ℕ) [NeZero P]
    (χ : DirichletCharacter ℂ P) : cyclicVariation P (cyclicSquareMeasure P χ) ≤ 1 := by
  classical
  have hφ : (0 : ℝ) < P.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos P)
  calc
    _ = (P.totient : ℝ)⁻¹ *
        ∑ z : ZMod P, ‖∑ u : (ZMod P)ˣ, if (u : ZMod P)^2=z then χ u else 0‖ := by
      simp only [cyclicVariation, cyclicSquareMeasure, norm_mul, norm_inv, norm_natCast]
      rw [mul_sum]
    _ ≤ (P.totient : ℝ)⁻¹ *
        ∑ z : ZMod P, ∑ u : (ZMod P)ˣ, ‖if (u : ZMod P)^2=z then χ u else 0‖ := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr hφ))
      exact sum_le_sum (fun z _ => norm_sum_le _ _)
    _ = (P.totient : ℝ)⁻¹ * ∑ u : (ZMod P)ˣ, ‖χ u‖ := by
      rw [sum_comm]
      congr 1
      apply sum_congr rfl
      intro u _
      simp_rw [apply_ite norm]
      simp
    _ = 1 := by simp [ZMod.card_units_eq_totient, hφ.ne']

theorem cyclicFourier_norm_le_variation (P : ℕ) [NeZero P] (ν : ZMod P → ℂ) (a : ZMod P) :
    ‖cyclicFourier P ν a‖ ≤ cyclicVariation P ν := by
  calc
    _ ≤ ∑ z : ZMod P, ‖ν z * ZMod.stdAddChar (-a*z)‖ := norm_sum_le _ _
    _ = _ := by simp [cyclicVariation]

theorem cyclicSquareMeasure_fourier (P : ℕ) [NeZero P]
    (χ : DirichletCharacter ℂ P) (a : ZMod P) :
    cyclicFourier P (cyclicSquareMeasure P χ) a = twistedSquareSum P χ a := by
  rw [cyclicFourier, cyclicSquareMeasure_test]
  simp only [twistedSquareSum, twistedUnitQuadraticGaussSum]

theorem cyclicPrincipalSquareMeasure_fourier (P : ℕ) [NeZero P] (a : ZMod P) :
    cyclicFourier P (cyclicSquareMeasure P 1) a = principalSquareSum P a := by
  rw [cyclicSquareMeasure_fourier, twistedSquareSum_principal]

end PrimeSquares
