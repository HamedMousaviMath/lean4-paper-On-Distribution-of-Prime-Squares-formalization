import PrimeSquares.AnnularCutoffSymbol
import PrimeSquares.SourceCutoffContinuousMap
namespace PrimeSquares
noncomputable def localizedAnnularSource (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (s : ℕ) : C(ℝ,ℂ) :=
  annularCutoffSymbol N hN β ((16 : ℝ)^s)
theorem localizedAnnularSource_support (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (s : ℕ)
    (x : ℝ) (hx : 1 ≤ |x|) : localizedAnnularSource N hN β s x=0 := by
  change annularOscillatoryModel N β x*sourceCutoffContinuousMap s x=0
  rw [sourceCutoffContinuousMap_support s x hx,mul_zero]
end PrimeSquares
