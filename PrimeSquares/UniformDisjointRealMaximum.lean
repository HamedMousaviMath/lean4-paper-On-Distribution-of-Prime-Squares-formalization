import PrimeSquares.DisjointMultiplierBessel
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem uniformDisjoint_real_maximum (L : ℕ) (m : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ i j,i ≠ j → ∀ θ,m i θ=0 ∨ m j θ=0) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ i<L,∀ θ,‖m i θ‖ ≤ A) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ R,0 ≤ R → ∀ x,‖integerMultiplier (realTruncatedCircleSymbol L R m) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (Nat.log2 L+2 : ℝ)*A*‖f‖ := by
  obtain ⟨g,hg,hp,hn⟩ := logarithmicDisjoint_real_cutoff_maximum L m (fun i _ j _ hij => hm i j hij) f
  have he := disjointMultiplier_bessel (range L) m hm hA (fun i hi => hbound i (mem_range.mp hi)) f
  have hs : Real.sqrt (∑ i ∈ range L,‖integerMultiplier (m i) f‖^2) ≤ A*‖f‖ := by
    have hh := Real.sqrt_le_sqrt he
    rw [←mul_pow,Real.sqrt_sq (mul_nonneg hA (norm_nonneg f))] at hh
    exact hh
  refine ⟨g,hg,hp,?_⟩
  calc
    _ ≤ (Nat.log2 L+2 : ℝ)*Real.sqrt (∑ i ∈ range L,‖integerMultiplier (m i) f‖^2) := hn
    _ ≤ (Nat.log2 L+2 : ℝ)*(A*‖f‖) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring
end PrimeSquares
