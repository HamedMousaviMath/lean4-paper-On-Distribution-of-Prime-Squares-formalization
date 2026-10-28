import PrimeSquares.WeightedDisjointSymbols
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem weightedDisjoint_prefix_majorant (h a : ℕ) (m : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ i j,i ≠ j → ∀ θ,m i θ=0 ∨ m j θ=0) (c : ℕ → ℂ) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ K,K ≤ 2^h → ∀ x,‖integerMultiplier
        (intervalCircleSymbol a K (fun i => c i • m i)) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (h+1 : ℝ)*Real.sqrt (intervalRealBudget a (2^h)
        (fun i => ‖integerMultiplier (c i • m i) f‖^2)) := by
  obtain ⟨g,hg,hp,hn⟩ := disjointMultiplier_prefix_majorant h a (fun i => c i • m i)
    (weighted_symbols_disjoint m hm c) (fun _ => f)
  refine ⟨g,hg,?_,hn⟩
  intro K hK x
  rw [integerMultiplier_interval]
  exact hp K hK x
end PrimeSquares
