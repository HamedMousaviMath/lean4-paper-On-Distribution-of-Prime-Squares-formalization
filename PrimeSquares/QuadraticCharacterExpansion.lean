import PrimeSquares.QuadraticResidueIndicator

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def quadraticSoftIndicator (p : ℕ) [Fact p.Prime] (a : ZMod p) : ℝ :=
  (1+quadraticCharReal p a)/2

noncomputable def quadraticCorrelation (p : ℕ) [Fact p.Prime] (S : Finset (ZMod p)) : ℝ :=
  ((Finset.univ.filter (fun t : ZMod p => ∀ h ∈ S, t+h ∈ unitSquareResidues p)).card : ℝ)

def RawSplitQuadraticWeilInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ S : Finset (ZMod p), S.Nonempty →
    |∑ t : ZMod p, quadraticCharReal p (∏ h ∈ S, (t+h))| ≤ (S.card : ℝ)*Real.sqrt p

theorem quadraticSoftIndicator_eq (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    quadraticSoftIndicator p a = unitSquareIndicator p a+(if a=0 then 1 else 0)/2 := by
  rw [unitSquareIndicator_formula]
  unfold quadraticSoftIndicator
  ring

theorem quadraticSoftIndicator_bounds (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    0 ≤ quadraticSoftIndicator p a ∧ quadraticSoftIndicator p a ≤ 1 := by
  classical
  by_cases h0 : a=0
  · norm_num [h0, quadraticSoftIndicator, quadraticCharReal]
  · rw [quadraticSoftIndicator_eq]
    simpa only [ite_eq_right h0, zero_div, add_zero] using unitSquareIndicator_bounds p a

theorem quadraticCharReal_prod (p : ℕ) [Fact p.Prime] (S : Finset (ZMod p))
    (f : ZMod p → ZMod p) :
    quadraticCharReal p (∏ h ∈ S, f h) = ∏ h ∈ S, quadraticCharReal p (f h) := by
  simp only [quadraticCharReal, map_prod, Int.cast_prod]

theorem finite_one_add_expansion {X I : Type*} [Fintype X] [DecidableEq I]
    (S : Finset I) (f : X → I → ℝ) :
    ∑ t : X, ∏ h ∈ S, (1+f t h) =
      Fintype.card X + ∑ J ∈ S.powerset.erase ∅, ∑ t : X, ∏ h ∈ J, f t h := by
  classical
  simp_rw [Finset.prod_one_add]
  rw [Finset.sum_comm]
  have he : (∅ : Finset I) ∈ S.powerset := by simp
  rw [←Finset.sum_erase_add _ _ he]
  simp

theorem quadratic_one_add_expansion (p : ℕ) [Fact p.Prime] (S : Finset (ZMod p)) :
    ∑ t : ZMod p, ∏ h ∈ S, (1+quadraticCharReal p (t+h)) =
      p + ∑ J ∈ S.powerset.erase ∅, ∑ t : ZMod p,
        quadraticCharReal p (∏ h ∈ J, (t+h)) := by
  rw [finite_one_add_expansion]
  simp_rw [quadraticCharReal_prod]
  simp only [ZMod.card]

end PrimeSquares
