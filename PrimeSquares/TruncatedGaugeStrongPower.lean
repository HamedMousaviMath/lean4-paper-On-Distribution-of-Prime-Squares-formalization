import PrimeSquares.TruncatedDistributionStrongPower
import PrimeSquares.SectionSevenThreeFamilyAssembly

set_option autoImplicit false
open MeasureTheory Set Finset
open scoped ENNReal
namespace PrimeSquares

theorem truncated_gauge_strong_power (A : PositiveAverageFamily) {C C₀ K : ℝ}
    (hC : 1 ≤ C) (hC₀ : 1 ≤ C₀) (hK : 0 ≤ K)
    (H : ∀ (F : Finset ℤ) (f : ℤ → ℂ), (∀ x, x ∉ F → f x = 0) →
      ∀ t : ℝ, 0 < t → {x | t < positiveMaximal A f x}.Finite ∧
      ({x | t < positiveMaximal A f x}.ncard : ℝ) ≤
        K*∑ x ∈ F.filter (fun x => t/C₀ < ‖f x‖), nearOnePsi C (‖f x‖/t))
    (F : Finset ℤ) (f : ℤ → ℂ) (hf : ∀ x, x ∉ F → f x = 0)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    (∫⁻ x : ℤ, ENNReal.ofReal ((positiveMaximal A f x)^p) ∂Measure.count) ≤
      ENNReal.ofReal (K*nearOnePowerConstant C (1/C₀) (p-1)*p*
        (C₀^(p-(1+(p-1)/2))/(p-(1+(p-1)/2))))*
        ∑ x ∈ F, ENNReal.ofReal (‖f x‖^p) := by
  classical
  have hC₀0 : 0 < C₀ := by linarith
  have he : 0 < p-1 := by linarith
  have he1 : p-1 ≤ 1 := by linarith
  have ha : 0 < 1/C₀ := by positivity
  have hP := (nearOnePowerConstant_pos ha C (p-1)).le
  apply truncated_distribution_strong_power F (fun x => ‖f x‖) (positiveMaximal A f)
    (fun _ _ => norm_nonneg _) (positiveMaximal_nonneg A
      (sum_nonneg (fun x _ => norm_nonneg (f x))) (finiteFunction_norm_bound F f hf))
    hK hP hC₀0 (by linarith : 0 < 1+(p-1)/2) (by linarith : 1+(p-1)/2 < p)
  intro t ht
  obtain ⟨hfinite, hcard⟩ := H F f hf t ht
  have hcount : Measure.count {x | t < positiveMaximal A f x} =
      ENNReal.ofReal ({x | t < positiveMaximal A f x}.ncard : ℝ) := by
    rw [Measure.count_apply_finite _ hfinite, Set.ncard_eq_toFinset_card _ hfinite]
    simp only [ENNReal.ofReal_natCast]
  calc
    _ = _ := hcount
    _ ≤ ENNReal.ofReal (K*∑ x ∈ F.filter (fun x => t/C₀ < ‖f x‖), nearOnePsi C (‖f x‖/t)) :=
      ENNReal.ofReal_le_ofReal hcard
    _ = ENNReal.ofReal K*∑ x ∈ F.filter (fun x => t/C₀ < ‖f x‖),
        ENNReal.ofReal (nearOnePsi C (‖f x‖/t)) := by
      rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_sum_of_nonneg
        (fun x _ => nearOnePsi_nonneg _ (div_nonneg (norm_nonneg _) ht.le))]
    _ ≤ ENNReal.ofReal K*∑ x ∈ F.filter (fun x => t/C₀ < ‖f x‖),
        (ENNReal.ofReal (nearOnePowerConstant C (1/C₀) (p-1))*
          ENNReal.ofReal ((‖f x‖/t)^(1+(p-1)/2))) := by
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro x hx
      have hcut := (Finset.mem_filter.mp hx).2
      have hu : 1/C₀ ≤ ‖f x‖/t :=
        (div_le_div_iff₀ hC₀0 ht).mpr (by
          have h := (div_lt_iff₀ hC₀0).mp hcut
          linarith)
      rw [←ENNReal.ofReal_mul hP]
      exact ENNReal.ofReal_le_ofReal (nearOnePsi_power_majorant hC ha he he1 hu)
    _ = _ := by
      rw [←Finset.mul_sum, ←mul_assoc, ←ENNReal.ofReal_mul hK, Finset.sum_filter]

end PrimeSquares
