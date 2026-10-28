import PrimeSquares.AnnularZeroFrequencyDifference
namespace PrimeSquares
theorem annularOscillatoryModel_small_frequency {N : ℕ} (hN : 2 ≤ N) {β : ℝ}
    (hβ : β ≤ 1) (θ : ℝ) :
    ‖annularOscillatoryModel N β θ-annularOscillatoryModel N β 0‖ ≤ Real.pi*(N : ℝ)^2*|θ| := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (N : ℝ)/2) (b := (N : ℝ))
    (f := fun t => Complex.ofReal (t^(β-1))*(quadraticOscillation θ t-1))
    (C := 2*Real.pi*|θ| *(N : ℝ)^2) (by
      intro t ht
      rw [Set.uIoc_of_le (by linarith : (N : ℝ)/2 ≤ N)] at ht
      exact annularDifference_integrand_bound hN hβ θ ⟨ht.1.le,ht.2⟩)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ)-(N : ℝ)/2)] at hi
  rw [annularOscillatoryModel_sub_zero (by omega : 1 ≤ N),norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)]
  calc
    _ ≤ (N : ℝ)⁻¹*((2*Real.pi*|θ| *(N : ℝ)^2)*((N : ℝ)-(N : ℝ)/2)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by field_simp;ring
end PrimeSquares
