import PrimeSquares.FiniteOrthogonalEnergy
import PrimeSquares.FiniteDisjointSymbolBound
import PrimeSquares.DisjointIntegerMultipliers
open Finset
open scoped lp
namespace PrimeSquares
theorem finite_disjoint_multiplier_bessel {ι : Type*} (S : Finset ι)
    (m : ι → C(PrimeCircle,ℂ))
    (hm : ∀ i ∈ S,∀ j ∈ S,i ≠ j → ∀ θ,m i θ=0 ∨ m j θ=0)
    {A : ℝ} (hA : 0 ≤ A) (hb : ∀ i ∈ S,∀ θ,‖m i θ‖ ≤ A) (f : ℓ²(ℤ,ℂ)) :
    (∑ i ∈ S,‖integerMultiplier (m i) f‖^2) ≤ A^2*‖f‖^2 := by
  rw [←finite_orthogonal_energy S (fun i => integerMultiplier (m i) f)
    (fun i hi j hj hij => integerMultiplier_disjoint_inner _ _ (hm i hi j hj hij) f f)]
  have he : (∑ i ∈ S,integerMultiplier (m i) f)=integerMultiplier (∑ i ∈ S,m i) f := by
    rw [integerMultiplier_finset_sum,_root_.sum_apply]
  rw [he,←mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  exact ((integerMultiplier (∑ i ∈ S,m i)).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right
      (integerMultiplier_opNorm_le_of_bound _ hA (finite_disjoint_symbol_bound S m hm hA hb))
      (norm_nonneg _))
end PrimeSquares
