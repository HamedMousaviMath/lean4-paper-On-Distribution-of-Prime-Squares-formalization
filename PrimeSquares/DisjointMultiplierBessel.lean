import PrimeSquares.DisjointSymbolSumBound
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem disjointMultiplier_bessel (S : Finset ℕ) (m : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ i j,i ≠ j → ∀ θ,m i θ=0 ∨ m j θ=0) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ i ∈ S,∀ θ,‖m i θ‖ ≤ A) (f : ℓ²(ℤ,ℂ)) :
    (∑ i ∈ S,‖integerMultiplier (m i) f‖^2) ≤ A^2*‖f‖^2 := by
  rw [←disjointMultiplier_finset_energy m hm (fun _ => f) S]
  have he : (∑ i ∈ S,integerMultiplier (m i) f)=integerMultiplier (∑ i ∈ S,m i) f := by
    rw [integerMultiplier_finset_sum,_root_.sum_apply]
  rw [he,←mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  exact ((integerMultiplier (∑ i ∈ S,m i)).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right
      (integerMultiplier_opNorm_le_of_bound _ hA (disjointSymbol_sum_bound S m hm hA hbound)) (norm_nonneg _))
end PrimeSquares
