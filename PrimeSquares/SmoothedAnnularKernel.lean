import PrimeSquares.DecayScaleComparison
import PrimeSquares.ShiftedDecayProfile
import PrimeSquares.AnnularModelSize

open MeasureTheory
namespace PrimeSquares

noncomputable def smoothedAnnularKernel (N : ℕ) (β a x : ℝ) : ℂ :=
  Complex.ofReal (N : ℝ)⁻¹*
    ∫ t in (N : ℝ)/2..N, Complex.ofReal (t^(β-1))*scaledCutoffKernel a (x-t^2)

theorem annular_square_support {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc ((N : ℝ)/2) N) : |t^2| ≤ (N : ℝ)^2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_of_nonneg (sq_nonneg t)]
  have ht0 : 0 ≤ t := by linarith [ht.1]
  exact pow_le_pow_left₀ ht0 ht.2 2

theorem annular_density_le_one {N : ℕ} (hN : 2 ≤ N) {β t : ℝ}
    (hβ : β ≤ 1) (ht : t ∈ Set.Icc ((N : ℝ)/2) N) : t^(β-1) ≤ 1 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [ht.1]) (by linarith)

theorem smoothedAnnularKernel_integrable {N : ℕ} (hN : 1 ≤ N) (β a x : ℝ) :
    IntervalIntegrable (fun t : ℝ => Complex.ofReal (t^(β-1))*scaledCutoffKernel a (x-t^2))
      volume ((N : ℝ)/2) N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  apply ContinuousOn.intervalIntegrable_of_Icc (by linarith : (N : ℝ)/2 ≤ N)
  exact (Complex.continuous_ofReal.comp_continuousOn
    (exceptionalDensity_continuousOn β (by positivity))).mul
    ((scaledCutoffKernel_continuous a).comp (continuous_const.sub (continuous_id.pow 2))).continuousOn

end PrimeSquares
