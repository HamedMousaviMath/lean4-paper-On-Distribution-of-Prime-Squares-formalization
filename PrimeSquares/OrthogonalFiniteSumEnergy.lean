import PrimeSquares.RademacherMenshovMajorant
import Mathlib.Analysis.InnerProductSpace.Basic
open Finset
namespace PrimeSquares
theorem orthogonal_finset_sum_energy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (F : ℕ → E) (hF : ∀ i j,i ≠ j → inner ℂ (F i) (F j)=0) (S : Finset ℕ) :
    ‖∑ i ∈ S,F i‖^2=∑ i ∈ S,‖F i‖^2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [sum_insert hi,sum_insert hi]
    have ho : inner ℂ (F i) (∑ j ∈ S,F j)=0 := by
      rw [inner_sum]
      exact sum_eq_zero (fun j hj => hF i j (by intro he;exact hi (he ▸ hj)))
    simpa only [←pow_two,ih] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (F i) (∑ j ∈ S,F j) ho
end PrimeSquares
