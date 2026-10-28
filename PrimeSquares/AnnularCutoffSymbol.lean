import PrimeSquares.NarrowFourierIntegral
import PrimeSquares.AnnularFrequencyContinuity

namespace PrimeSquares

noncomputable def annularCutoffSymbol (N : ℕ) (hN : 1 ≤ N) (β a : ℝ) : C(ℝ, ℂ) :=
  ⟨fun ξ => annularOscillatoryModel N β ξ*Complex.ofReal (sourceArcCutoff (a*ξ)),
    (annularOscillatoryModel_continuous hN β).mul
      (Complex.continuous_ofReal.comp (sourceArcCutoff_contDiff.continuous.comp (continuous_const.mul continuous_id)))⟩

theorem annularCutoffSymbol_narrow (N : ℕ) (hN : 1 ≤ N) (β : ℝ) {a : ℝ} (ha : 2 ≤ a)
    {ξ : ℝ} (hξ : 1/2 ≤ |ξ|) : annularCutoffSymbol N hN β a ξ=0 := by
  change annularOscillatoryModel N β ξ*Complex.ofReal (sourceArcCutoff (a*ξ))=0
  rw [scaled_source_cutoff_narrow ha hξ,Complex.ofReal_zero,mul_zero]

theorem annularCutoffSymbol_support (N : ℕ) (hN : 1 ≤ N) (β : ℝ) {a : ℝ} (ha : 2 ≤ a)
    (ξ : ℝ) (hξ : 1 ≤ |ξ|) : annularCutoffSymbol N hN β a ξ=0 :=
  annularCutoffSymbol_narrow N hN β ha (by linarith)

end PrimeSquares
