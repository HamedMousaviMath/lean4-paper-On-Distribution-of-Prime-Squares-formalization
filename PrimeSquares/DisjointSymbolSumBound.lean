import PrimeSquares.LogarithmicDisjointMaximum
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem disjointSymbol_sum_bound (S : Finset ℕ) (m : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ i j,i ≠ j → ∀ θ,m i θ=0 ∨ m j θ=0) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ i ∈ S,∀ θ,‖m i θ‖ ≤ A) (θ : PrimeCircle) :
    ‖(∑ i ∈ S,m i) θ‖ ≤ A := by
  classical
  simp only [ContinuousMap.sum_apply]
  by_cases hz : ∀ i ∈ S,m i θ=0
  · simp only [sum_eq_zero hz,norm_zero]
    exact hA
  · push Not at hz
    obtain ⟨i,hi,hiz⟩ := hz
    have he : (∑ j ∈ S,m j θ)=m i θ := by
      apply sum_eq_single i
      · intro j _ hji
        exact (hm j i hji θ).resolve_right hiz
      · exact fun h => (h hi).elim
    rw [he]
    exact hbound i hi θ
end PrimeSquares
