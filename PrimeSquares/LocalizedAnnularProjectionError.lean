import PrimeSquares.AnnularProjectionErrorContinuity
import PrimeSquares.SourceCutoffContinuousMap
namespace PrimeSquares
noncomputable def localizedAnnularProjectionError (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (s : ℕ) : C(ℝ,ℂ) :=
  ⟨fun x => annularProjectionError N β x*sourceCutoffContinuousMap s x,
    (annularProjectionError_continuous hN β).mul (sourceCutoffContinuousMap s).continuous⟩
theorem localizedAnnularProjectionError_support (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (s : ℕ)
    (x : ℝ) (hx : 1 ≤ |x|) : localizedAnnularProjectionError N hN β s x=0 := by
  simp only [localizedAnnularProjectionError,ContinuousMap.coe_mk,
    sourceCutoffContinuousMap_support s x hx,mul_zero]
end PrimeSquares
