import PrimeSquares.PaddedMultiplierEnergy
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem finiteDisjoint_prefix_maximum (L h : ℕ) (hL : L ≤ 2^h)
    (m : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ i<L,∀ j<L,i ≠ j → ∀ θ,m i θ=0 ∨ m j θ=0) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ K,K ≤ L → ∀ x,‖integerMultiplier (intervalCircleSymbol 0 K m) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (h+1 : ℝ)*Real.sqrt (∑ i ∈ range L,‖integerMultiplier (m i) f‖^2) := by
  obtain ⟨g,hg,hp,hn⟩ := disjointMultiplier_prefix_majorant h 0 (paddedCircleSymbols L m)
    (paddedCircleSymbols_disjoint L m hm) (fun _ => f)
  refine ⟨g,hg,?_,?_⟩
  · intro K hK x
    have he := integerMultiplier_interval 0 K (paddedCircleSymbols L m) f
    rw [paddedCircleSymbols_prefix L K hK m] at he
    rw [he]
    exact hp K (hK.trans hL) x
  · simpa only [paddedMultiplier_square_budget L (2^h) hL m f] using hn
end PrimeSquares
