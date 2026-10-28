import PrimeSquares.DisjointSymbolSumBound
open Finset
namespace PrimeSquares
theorem finite_disjoint_symbol_bound {ι : Type*} (S : Finset ι) (m : ι → C(PrimeCircle,ℂ))
    (hm : ∀ i ∈ S,∀ j ∈ S,i ≠ j → ∀ θ,m i θ=0 ∨ m j θ=0)
    {A : ℝ} (hA : 0 ≤ A) (hb : ∀ i ∈ S,∀ θ,‖m i θ‖ ≤ A) (θ : PrimeCircle) :
    ‖(∑ i ∈ S,m i) θ‖ ≤ A := by
  classical
  simp only [ContinuousMap.sum_apply]
  by_cases hz : ∀ i ∈ S,m i θ=0
  · simpa only [sum_eq_zero hz,norm_zero] using hA
  · push Not at hz
    obtain ⟨i,hi,hiz⟩ := hz
    have he : (∑ j ∈ S,m j θ)=m i θ := by
      apply sum_eq_single i
      · intro j hj hji
        exact (hm j hj i hi hji θ).resolve_right hiz
      · exact fun h => (h hi).elim
    rw [he]
    exact hb i hi θ
end PrimeSquares
