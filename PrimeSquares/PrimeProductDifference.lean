import PrimeSquares.CyclicDifferenceMomentBound
import PrimeSquares.PrimeProductThickening

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem prime_product_far_pair_bound (HW : RawSplitQuadraticWeilInput)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (hbudget : ∑ p ∈ S, (64/Real.sqrt p : ℝ) ≤ 1) (γ : ℝ) (hγ : 0 ≤ γ) :
    let q := ∏ p ∈ S, p
    letI : NeZero q := ⟨Finset.prod_ne_zero_iff.mpr (fun p hp => (hS p hp).1.ne_zero)⟩
    1-6*γ-3*unitSquareDensity q ≤ cyclicFarPairFraction q (unitSquareResidues q) γ := by
  let q := ∏ p ∈ S, p
  have : NeZero q := ⟨Finset.prod_ne_zero_iff.mpr (fun p hp => (hS p hp).1.ne_zero)⟩
  change 1-6*γ-3*unitSquareDensity q ≤ cyclicFarPairFraction q (unitSquareResidues q) γ
  have htriple : ∀ d ∈ signedIntegerShifts (γ*((q:ℝ)/(unitSquareResidues q).card)),
      (additiveTripleCount (unitSquareResidues q) (d:ZMod q):ℝ) ≤
        3*((unitSquareResidues q).card:ℝ)^3/q := by
    intro d _
    have h := global_quadratic_triple_moment HW S hS hbudget d
    rw [unitSquareTripleCount_eq, unitSquareCard_eq] at h
    simpa only [q, Nat.cast_prod] using h
  simpa only [unitSquareDensity, unitSquareCard_eq, show (2:ℝ)*3=6 by norm_num, mul_div_assoc] using
    cyclic_far_pair_triple_bound q (unitSquareResidues q) (unitSquareResidues_nonempty q)
      γ 3 hγ (by norm_num) htriple

theorem prime_product_finite_badness_conditions (HW : RawSplitQuadraticWeilInput)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (hbudget : ∑ p ∈ S, (64/Real.sqrt p : ℝ) ≤ 1) (γ : ℝ) (hγ : 0 < γ)
    (hsmall : ∀ p ∈ S, γ*unitSquareSpacing (∏ r ∈ S, r) ≤ (p:ℝ)) :
    let q := ∏ p ∈ S, p
    letI : NeZero q := ⟨Finset.prod_ne_zero_iff.mpr (fun p hp => (hS p hp).1.ne_zero)⟩
    (γ-unitSquareDensity q-(3/2:ℝ)*γ^2 ≤ cyclicThickeningDensity q (unitSquareResidues q) γ ∧
      cyclicThickeningDensity q (unitSquareResidues q) γ ≤ γ) ∧
      1-6*γ-3*unitSquareDensity q ≤ cyclicFarPairFraction q (unitSquareResidues q) γ := by
  exact ⟨prime_product_thickening_bound HW S hS hbudget γ hγ hsmall,
    prime_product_far_pair_bound HW S hS hbudget γ hγ.le⟩

theorem badness_difference_constant_margin {γ : ℝ} (hγ : γ < 1/16) :
    5*(1/160:ℝ) < (5/8:ℝ) ∧ (5/8:ℝ) < 1-6*γ := by
  constructor
  · norm_num
  · linarith

end PrimeSquares
