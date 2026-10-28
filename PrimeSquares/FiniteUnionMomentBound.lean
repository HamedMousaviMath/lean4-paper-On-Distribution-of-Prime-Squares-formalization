import PrimeSquares.FiniteAdditiveResidueCounts

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem finite_union_uniform_lower {I X : Type*} [DecidableEq I] [DecidableEq X]
    (S : Finset I) (F : I → Finset X) (m B : ℝ)
    (hsize : ∀ i ∈ S, ((F i).card:ℝ)=m)
    (hinter : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((F i ∩ F j).card:ℝ) ≤ B) :
    (S.card:ℝ)*m-((S.card:ℝ)*((S.card:ℝ)-1)/2)*B ≤ (S.biUnion F).card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hsizeS : ∀ i ∈ S, ((F i).card:ℝ)=m :=
      fun i hi => hsize i (Finset.mem_insert_of_mem hi)
    have hinterS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((F i ∩ F j).card:ℝ) ≤ B :=
      fun i hi j hj hij => hinter i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have ih' := ih hsizeS hinterS
    have heq : F a ∩ S.biUnion F = S.biUnion (fun j => F a ∩ F j) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_biUnion]
      aesop
    have hbound : ((F a ∩ S.biUnion F).card:ℝ) ≤ (S.card:ℝ)*B := by
      rw [heq]
      calc
        _ ≤ ∑ j ∈ S, ((F a ∩ F j).card:ℝ) := by
          exact_mod_cast Finset.card_biUnion_le (s:=S) (t:=fun j => F a ∩ F j)
        _ ≤ ∑ _j ∈ S, B := by
          apply Finset.sum_le_sum
          intro j hj
          exact hinter a (Finset.mem_insert_self a S) j (Finset.mem_insert_of_mem hj)
            (by intro h; exact ha (h ▸ hj))
        _ = (S.card:ℝ)*B := by simp
    have hc : ((F a ∪ S.biUnion F).card:ℝ)+((F a ∩ S.biUnion F).card:ℝ)=
        ((F a).card:ℝ)+((S.biUnion F).card:ℝ) := by
      exact_mod_cast Finset.card_union_add_card_inter (F a) (S.biUnion F)
    have hma := hsize a (Finset.mem_insert_self a S)
    simp only [Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one, Finset.biUnion_insert]
    nlinarith

theorem finite_union_uniform_quadratic_lower {I X : Type*} [DecidableEq I] [DecidableEq X]
    (S : Finset I) (F : I → Finset X) (m B : ℝ) (hB : 0 ≤ B)
    (hsize : ∀ i ∈ S, ((F i).card:ℝ)=m)
    (hinter : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((F i ∩ F j).card:ℝ) ≤ B) :
    (S.card:ℝ)*m-(S.card:ℝ)^2*B/2 ≤ (S.biUnion F).card := by
  have h := finite_union_uniform_lower S F m B hsize hinter
  have hn : (0:ℝ) ≤ S.card := by positivity
  nlinarith

theorem finite_union_uniform_upper {I X : Type*} [DecidableEq X]
    (S : Finset I) (F : I → Finset X) (m : ℝ)
    (hsize : ∀ i ∈ S, ((F i).card:ℝ)=m) :
    ((S.biUnion F).card:ℝ) ≤ (S.card:ℝ)*m := by
  calc
    _ ≤ ∑ i ∈ S, ((F i).card:ℝ) := by exact_mod_cast Finset.card_biUnion_le (s:=S) (t:=F)
    _ = _ := by simp only [Finset.sum_congr rfl hsize, Finset.sum_const, nsmul_eq_mul]

end PrimeSquares
