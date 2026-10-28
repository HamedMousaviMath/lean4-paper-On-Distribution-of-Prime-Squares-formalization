import PrimeSquares.BadnessDensityLimits

set_option autoImplicit false
open Filter
open scoped Topology
namespace PrimeSquares

noncomputable def badnessThickeningDeficit (γ : ℝ) : ℝ := γ-
  liminf (fun j : ℕ => cyclicThickeningDensity (badnessBlockModulus j)
    (unitSquareResidues (badnessBlockModulus j)) γ) atTop

theorem badnessThickeningDeficit_bounds (HW : RawSplitQuadraticWeilInput)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    0 ≤ badnessThickeningDeficit γ ∧ badnessThickeningDeficit γ ≤ (3/2:ℝ)*γ^2 := by
  have h0 (j : ℕ) : 0 ≤ cyclicThickeningDensity (badnessBlockModulus j)
      (unitSquareResidues (badnessBlockModulus j)) γ :=
    (cyclicThickeningDensity_bounds _ _ _).1
  have h1 (j : ℕ) : cyclicThickeningDensity (badnessBlockModulus j)
      (unitSquareResidues (badnessBlockModulus j)) γ ≤ 1 :=
    (cyclicThickeningDensity_bounds _ _ _).2
  have hlower (j : ℕ) : (γ-(3/2:ℝ)*γ^2)-unitSquareDensity (badnessBlockModulus j) ≤
      cyclicThickeningDensity (badnessBlockModulus j) (unitSquareResidues (badnessBlockModulus j)) γ := by
    have h := (badnessBlock_finite_conditions HW j γ hγ hγ1).1.1
    linarith
  have hL := liminf_lower_from_vanishing_error h0 h1 badnessBlockDensity_tendsto_zero hlower
  have hU := liminf_le_uniform_upper h0
    (fun j => (badnessBlock_finite_conditions HW j γ hγ hγ1).1.2)
  unfold badnessThickeningDeficit
  constructor <;> linarith

theorem badness_far_pair_liminf (HW : RawSplitQuadraticWeilInput)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    1-6*γ ≤ liminf (fun j : ℕ => cyclicFarPairFraction (badnessBlockModulus j)
      (unitSquareResidues (badnessBlockModulus j)) γ) atTop := by
  have h0 (j : ℕ) : 0 ≤ cyclicFarPairFraction (badnessBlockModulus j)
      (unitSquareResidues (badnessBlockModulus j)) γ :=
    (cyclicFarPairFraction_bounds _ _ _).1
  have h1 (j : ℕ) : cyclicFarPairFraction (badnessBlockModulus j)
      (unitSquareResidues (badnessBlockModulus j)) γ ≤ 1 :=
    (cyclicFarPairFraction_bounds _ _ _).2
  have he : Tendsto (fun j : ℕ => 3*unitSquareDensity (badnessBlockModulus j)) atTop (𝓝 0) := by
    simpa only [mul_zero] using badnessBlockDensity_tendsto_zero.const_mul (3:ℝ)
  exact liminf_lower_from_vanishing_error h0 h1 he
    (fun j => (badnessBlock_finite_conditions HW j γ hγ hγ1).2)

theorem badness_difference_condition (HW : RawSplitQuadraticWeilInput)
    (γ : ℝ) (hγ : 0 < γ) (hγ16 : γ < 1/16) :
    5*(1/160:ℝ) < liminf (fun j : ℕ => cyclicFarPairFraction (badnessBlockModulus j)
      (unitSquareResidues (badnessBlockModulus j)) γ) atTop := by
  have hm := badness_difference_constant_margin hγ16
  exact (hm.1.trans hm.2).trans_le (badness_far_pair_liminf HW γ hγ (by linarith))

end PrimeSquares
