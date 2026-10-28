import PrimeSquares.CyclicThickeningMomentBound
import PrimeSquares.GlobalQuadraticMomentBound

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem small_integer_shift_difference_ne_zero (p : ℕ) [NeZero p] (r : ℝ)
    (hr : r ≤ (p:ℝ)) (d e : ℕ) (hd : d ∈ positiveIntegerShifts r)
    (he : e ∈ positiveIntegerShifts r) (hde : d ≠ e) :
    (((d:ℤ)-(e:ℤ) : ℤ) : ZMod p) ≠ 0 := by
  have hdp : d < p := by
    exact_mod_cast ((mem_positiveIntegerShifts r d).mp hd).2.trans_le hr
  have hep : e < p := by
    exact_mod_cast ((mem_positiveIntegerShifts r e).mp he).2.trans_le hr
  intro hz
  have heq : (d:ZMod p)=(e:ZMod p) := sub_eq_zero.mp (by simpa using hz)
  have hv := congrArg ZMod.val heq
  rw [ZMod.val_natCast_of_lt hdp, ZMod.val_natCast_of_lt hep] at hv
  exact hde hv

theorem prime_product_thickening_bound (HW : RawSplitQuadraticWeilInput)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (hbudget : ∑ p ∈ S, (64/Real.sqrt p : ℝ) ≤ 1) (γ : ℝ) (hγ : 0 < γ)
    (hsmall : ∀ p ∈ S, γ*unitSquareSpacing (∏ r ∈ S, r) ≤ (p:ℝ)) :
    let q := ∏ p ∈ S, p
    letI : NeZero q := ⟨Finset.prod_ne_zero_iff.mpr (fun p hp => (hS p hp).1.ne_zero)⟩
    γ-unitSquareDensity q-(3/2:ℝ)*γ^2 ≤ cyclicThickeningDensity q (unitSquareResidues q) γ ∧
      cyclicThickeningDensity q (unitSquareResidues q) γ ≤ γ := by
  let q := ∏ p ∈ S, p
  have : NeZero q := ⟨Finset.prod_ne_zero_iff.mpr (fun p hp => (hS p hp).1.ne_zero)⟩
  change γ-unitSquareDensity q-(3/2:ℝ)*γ^2 ≤ cyclicThickeningDensity q (unitSquareResidues q) γ ∧
    cyclicThickeningDensity q (unitSquareResidues q) γ ≤ γ
  have hsmall' : ∀ p ∈ S,
      γ*((q:ℝ)/(unitSquareResidues q).card) ≤ (p:ℝ) := by
    simpa only [unitSquareSpacing, unitSquareCard_eq] using hsmall
  have hpair : ∀ d ∈ positiveIntegerShifts (γ*((q:ℝ)/(unitSquareResidues q).card)),
      ∀ e ∈ positiveIntegerShifts (γ*((q:ℝ)/(unitSquareResidues q).card)), d ≠ e →
        (additivePairCount (unitSquareResidues q) ((d:ZMod q)-(e:ZMod q)) : ℝ) ≤
          3*((unitSquareResidues q).card:ℝ)^2/q := by
    intro d hd e he hde
    have ht (p : ℕ) (hp : p ∈ S) : (((d:ℤ)-(e:ℤ):ℤ) : ZMod p) ≠ 0 := by
      have : Fact p.Prime := ⟨(hS p hp).1⟩
      exact small_integer_shift_difference_ne_zero p _ (hsmall' p hp) d e hd he hde
    have h := global_quadratic_pair_moment HW S hS hbudget ((d:ℤ)-(e:ℤ)) ht
    rw [unitSquarePairCount_eq, unitSquareCard_eq] at h
    simpa only [q, Int.cast_sub, Int.cast_natCast, Nat.cast_prod] using h
  simpa only [unitSquareDensity, unitSquareCard_eq] using
    cyclic_thickening_pair_bound q (unitSquareResidues q) (unitSquareResidues_nonempty q)
      γ 3 hγ (by norm_num) hpair

end PrimeSquares
