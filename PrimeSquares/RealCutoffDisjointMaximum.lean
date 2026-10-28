import PrimeSquares.RealTruncatedCirclePrefix
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem finiteDisjoint_real_cutoff_maximum (L h : ℕ) (hL : L ≤ 2^h)
    (m : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ i<L,∀ j<L,i ≠ j → ∀ θ,m i θ=0 ∨ m j θ=0) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ R,0 ≤ R → ∀ x,‖integerMultiplier (realTruncatedCircleSymbol L R m) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (h+1 : ℝ)*Real.sqrt (∑ i ∈ range L,‖integerMultiplier (m i) f‖^2) := by
  obtain ⟨g,hg,hp,hn⟩ := finiteDisjoint_prefix_maximum L h hL m hm f
  refine ⟨g,hg,?_,hn⟩
  intro R hR x
  rw [realTruncatedCircleSymbol_prefix L hR m]
  exact hp _ (min_le_left _ _) x
end PrimeSquares
