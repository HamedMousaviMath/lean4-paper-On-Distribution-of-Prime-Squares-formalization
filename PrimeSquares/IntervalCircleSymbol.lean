import PrimeSquares.DisjointMultiplierPrefix
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
noncomputable def intervalCircleSymbol (a K : ℕ) (m : ℕ → C(PrimeCircle,ℂ)) :
    C(PrimeCircle,ℂ) := ∑ i ∈ range K,m (a+i)
theorem intervalCircleSymbol_apply (a K : ℕ) (m : ℕ → C(PrimeCircle,ℂ)) (θ : PrimeCircle) :
    intervalCircleSymbol a K m θ=intervalComplexSum a K (fun i => m i θ) := by
  simp only [intervalCircleSymbol,intervalComplexSum,ContinuousMap.sum_apply]
end PrimeSquares
