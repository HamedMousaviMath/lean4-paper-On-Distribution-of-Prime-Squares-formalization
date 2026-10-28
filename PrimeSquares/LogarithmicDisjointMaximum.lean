import PrimeSquares.BinaryDepthLogarithm
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem logarithmicDisjoint_real_cutoff_maximum (L : ℕ) (m : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ i<L,∀ j<L,i ≠ j → ∀ θ,m i θ=0 ∨ m j θ=0) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ R,0 ≤ R → ∀ x,‖integerMultiplier (realTruncatedCircleSymbol L R m) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (Nat.log2 L+2 : ℝ)*Real.sqrt (∑ i ∈ range L,‖integerMultiplier (m i) f‖^2) := by
  obtain ⟨g,hg,hp,hn⟩ := finiteDisjoint_real_cutoff_maximum L (finiteBinaryDepth L)
    (finiteBinaryDepth_capacity L) m hm f
  exact ⟨g,hg,hp,hn.trans (mul_le_mul_of_nonneg_right (finiteBinaryDepth_factor_le L) (Real.sqrt_nonneg _))⟩
end PrimeSquares
