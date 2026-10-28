import PrimeSquares.ProgressionAbel

/-! Quantitative transport of a uniform prefix error through the quadratic phase. -/

open MeasureTheory

namespace PrimeSquares

theorem quadratic_prefix_error_bound (θ : ℝ) {a b N B : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbN : b ≤ N)
    (R : ℝ → ℂ) (hR : ∀ t ∈ Set.Icc a b, ‖R t‖ ≤ B) :
    ‖quadraticOscillation θ b * R b - quadraticOscillation θ a * R a -
      ∫ t in Set.Ioc a b, quadraticOscillationDerivative θ t * R t‖ ≤
      B * (2 + (4 * Real.pi * |θ| * N) * (b-a)) := by
  have hN : 0 ≤ N := ha.trans (hab.trans hbN)
  have hD : 0 ≤ 4 * Real.pi * |θ| * N := by positivity
  have hi : ‖∫ t in Set.Ioc a b, quadraticOscillationDerivative θ t * R t‖ ≤
      (4 * Real.pi * |θ| * N * B) * (b-a) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun t => quadraticOscillationDerivative θ t * R t)
      (C := 4 * Real.pi * |θ| * N * B) (fun t ht => by
        have ht' : t ∈ Set.Ioc a b := by simpa only [Set.uIoc_of_le hab] using ht
        rw [norm_mul]
        exact mul_le_mul (quadraticOscillationDerivative_bound θ (ha.trans ht'.1.le)
          (ht'.2.trans hbN)) (hR t ⟨ht'.1.le, ht'.2⟩) (norm_nonneg _) hD)
    simpa only [intervalIntegral.integral_of_le hab, abs_of_nonneg (sub_nonneg.mpr hab)] using h
  have hpa : ‖quadraticOscillation θ a * R a‖ ≤ B := by
    simpa only [norm_mul, quadraticOscillation_norm, one_mul] using hR a ⟨le_rfl, hab⟩
  have hpb : ‖quadraticOscillation θ b * R b‖ ≤ B := by
    simpa only [norm_mul, quadraticOscillation_norm, one_mul] using hR b ⟨hab, le_rfl⟩
  calc
    _ ≤ ‖quadraticOscillation θ b * R b - quadraticOscillation θ a * R a‖ +
        ‖∫ t in Set.Ioc a b, quadraticOscillationDerivative θ t * R t‖ := norm_sub_le _ _
    _ ≤ (‖quadraticOscillation θ b * R b‖ + ‖quadraticOscillation θ a * R a‖) +
        (4 * Real.pi * |θ| * N * B) * (b-a) := add_le_add (norm_sub_le _ _) hi
    _ ≤ (B+B) + (4 * Real.pi * |θ| * N * B) * (b-a) :=
      add_le_add (add_le_add hpb hpa) le_rfl
    _ = _ := by ring

theorem quadratic_prefix_error_bound_square (θ : ℝ) {a b N B : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbN : b ≤ N) (hB : 0 ≤ B)
    (R : ℝ → ℂ) (hR : ∀ t ∈ Set.Icc a b, ‖R t‖ ≤ B) :
    ‖quadraticOscillation θ b * R b - quadraticOscillation θ a * R a -
      ∫ t in Set.Ioc a b, quadraticOscillationDerivative θ t * R t‖ ≤
      B * (2 + 4 * Real.pi * |θ| * N^2) := by
  have hN : 0 ≤ N := ha.trans (hab.trans hbN)
  apply (quadratic_prefix_error_bound θ ha hab hbN R hR).trans
  apply mul_le_mul_of_nonneg_left _ hB
  apply add_le_add le_rfl
  calc
    (4 * Real.pi * |θ| * N) * (b-a) ≤ (4 * Real.pi * |θ| * N) * N :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

end PrimeSquares
