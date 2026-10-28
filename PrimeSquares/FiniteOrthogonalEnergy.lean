import PrimeSquares.OrthogonalFiniteSumEnergy
open Finset
namespace PrimeSquares
theorem finite_orthogonal_energy {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Finset ι) (F : ι → E)
    (hF : ∀ i ∈ S,∀ j ∈ S,i ≠ j → inner ℂ (F i) (F j)=0) :
    ‖∑ i ∈ S,F i‖^2=∑ i ∈ S,‖F i‖^2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [sum_insert hi,sum_insert hi]
    have ho : inner ℂ (F i) (∑ j ∈ S,F j)=0 := by
      rw [inner_sum]
      exact sum_eq_zero (fun j hj => hF i (mem_insert_self _ _) j
        (mem_insert_of_mem hj) (by intro he;exact hi (he ▸ hj)))
    have hS : ∀ j ∈ S,∀ k ∈ S,j ≠ k → inner ℂ (F j) (F k)=0 :=
      fun j hj k hk h => hF j (mem_insert_of_mem hj) k (mem_insert_of_mem hk) h
    simpa only [←pow_two,ih hS] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (F i) (∑ j ∈ S,F j) ho
end PrimeSquares
