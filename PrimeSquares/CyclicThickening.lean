import PrimeSquares.FiniteUnionMomentBound
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
open Finset
namespace PrimeSquares

def translatedResidues {G : Type*} [AddGroup G] [DecidableEq G] (S : Finset G) (a : G) : Finset G :=
  S.image (fun x => x+a)

theorem mem_translatedResidues {G : Type*} [AddGroup G] [DecidableEq G]
    (S : Finset G) (a x : G) : x ∈ translatedResidues S a ↔ x-a ∈ S := by
  constructor
  · intro h
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h
    simpa using hu
  · intro h
    exact Finset.mem_image.mpr ⟨x-a,h,by simp⟩

theorem translatedResidues_card {G : Type*} [AddGroup G] [DecidableEq G]
    (S : Finset G) (a : G) : (translatedResidues S a).card=S.card :=
  Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)

theorem translatedResidues_inter_card {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (a b : G) :
    (translatedResidues S a ∩ translatedResidues S b).card=additivePairCount S (a-b) := by
  symm
  unfold additivePairCount
  apply Finset.card_bijective (Equiv.addRight a) (Equiv.addRight a).bijective
  intro u
  simp only [Finset.mem_filter, Finset.mem_inter, mem_translatedResidues]
  change (u ∈ S ∧ u+(a-b) ∈ S) ↔ ((u+a)-a ∈ S ∧ (u+a)-b ∈ S)
  simp only [add_sub_cancel_right, add_sub_assoc]

noncomputable def positiveIntegerShifts (r : ℝ) : Finset ℕ := Finset.Ioo 0 ⌈r⌉₊

theorem mem_positiveIntegerShifts (r : ℝ) (d : ℕ) :
    d ∈ positiveIntegerShifts r ↔ 0 < d ∧ (d:ℝ)<r := by
  simp only [positiveIntegerShifts, Finset.mem_Ioo, Nat.lt_ceil]

theorem positiveIntegerShifts_card_bounds (r : ℝ) (hr : 0 < r) :
    r-1 ≤ ((positiveIntegerShifts r).card:ℝ) ∧ ((positiveIntegerShifts r).card:ℝ) ≤ r := by
  have hc : (positiveIntegerShifts r).card=⌈r⌉₊-1 := by simp [positiveIntegerShifts, Nat.card_Ioo]
  have hceil : 1 ≤ ⌈r⌉₊ := Nat.ceil_pos.mpr hr
  have hcast : ((positiveIntegerShifts r).card:ℝ)=(⌈r⌉₊:ℝ)-1 := by
    rw [hc, Nat.cast_sub hceil]
    norm_num
  rw [hcast]
  constructor
  · linarith [Nat.le_ceil r]
  · linarith [Nat.ceil_lt_add_one hr.le]

noncomputable def cyclicThickening (q : ℕ) (S : Finset (ZMod q)) (γ : ℝ) : Finset (ZMod q) :=
  (positiveIntegerShifts (γ*((q:ℝ)/S.card))).biUnion
    (fun d => translatedResidues S (d:ZMod q))

noncomputable def cyclicThickeningDensity (q : ℕ) (S : Finset (ZMod q)) (γ : ℝ) : ℝ :=
  ((cyclicThickening q S γ).card:ℝ)/q

theorem mem_cyclicThickening (q : ℕ) (S : Finset (ZMod q)) (γ : ℝ) (x : ZMod q) :
    x ∈ cyclicThickening q S γ ↔ ∃ d : ℕ, 0 < d ∧
      (d:ℝ)<γ*((q:ℝ)/S.card) ∧ x-(d:ZMod q) ∈ S := by
  simp only [cyclicThickening, Finset.mem_biUnion, mem_positiveIntegerShifts,
    mem_translatedResidues, and_assoc]

theorem cyclicThickeningDensity_bounds (q : ℕ) [NeZero q] (S : Finset (ZMod q)) (γ : ℝ) :
    0 ≤ cyclicThickeningDensity q S γ ∧ cyclicThickeningDensity q S γ ≤ 1 := by
  have hq : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  constructor
  · unfold cyclicThickeningDensity
    positivity
  · unfold cyclicThickeningDensity
    apply (div_le_iff₀ hq).mpr
    simpa only [one_mul, ZMod.card] using
      (show ((cyclicThickening q S γ).card:ℝ) ≤ Fintype.card (ZMod q) by
        exact_mod_cast Finset.card_le_univ (cyclicThickening q S γ))

end PrimeSquares
