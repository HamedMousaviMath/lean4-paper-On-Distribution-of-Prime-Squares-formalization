import PrimeSquares.AnnularFrequencyContinuity
import PrimeSquares.FiniteMajorArcModels

namespace PrimeSquares

theorem annularGaussModel_continuous {N : ℕ} (hN : 1 ≤ N) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (κ : ℂ) (β : ℝ) (a : ZMod q) :
    Continuous (annularGaussModel N q χ κ β a) := by
  exact (continuous_const.mul (annularOscillatoryModel_continuous hN 1)).sub
    (continuous_const.mul (continuous_const.mul (annularOscillatoryModel_continuous hN β)))

theorem localizedAnnularGaussModel_continuous {N : ℕ} (hN : 1 ≤ N) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (κ : ℂ) (β : ℝ) (a : ZMod q) (s : ℕ) :
    Continuous (localizedAnnularGaussModel N q χ κ β a s) := by
  apply (annularGaussModel_continuous hN q χ κ β a).mul
  apply Complex.continuous_ofReal.comp
  change Continuous (fun θ : ℝ => sourceArcCutoff ((16 : ℝ)^s*θ))
  exact sourceArcCutoff_contDiff.continuous.comp (continuous_const.mul continuous_id)

end PrimeSquares
