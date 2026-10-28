import PrimeSquares.ReflectedConvolution
import PrimeSquares.WeightedSquareAverages

/-!
# Literal plus-square averages and the change of spatial support

The plus-square operator is defined directly as a finite sum of translations,
not by conjugation. It is then identified with `R T R` for the existing
minus-square operator. Arithmetic indices and weights are unchanged.
-/

open Finset
open scoped lp

namespace PrimeSquares

noncomputable def finitePlusSquareKernel (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ)
    (z : ℤ) : ℂ :=
  (c : ℂ) * ∑ n ∈ S, if z = -((n : ℤ)^2) then (w n : ℂ) else 0

theorem finiteSquareKernel_reflection (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) :
    reflectSequence (finiteSquareKernel S c w) = finitePlusSquareKernel S c w := by
  funext z
  simp only [reflectSequence_apply, finiteSquareKernel, finitePlusSquareKernel]
  congr 1
  apply sum_congr rfl
  intro n _
  have he : -z = (n : ℤ)^2 ↔ z = -((n : ℤ)^2) := by omega
  simp only [he]

noncomputable def finitePlusSquareOperator {p : ENNReal} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) :
    ℓ^p(ℤ, ℂ) →L[ℂ] ℓ^p(ℤ, ℂ) :=
  (c : ℂ) • ∑ n ∈ S, (w n : ℂ) • integerTranslate hp (-((n : ℤ)^2))

theorem finitePlusSquareOperator_apply {p : ENNReal} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ)
    (f : ℓ^p(ℤ, ℂ)) (x : ℤ) :
    finitePlusSquareOperator hp S c w f x =
      (c : ℂ) * ∑ n ∈ S, (w n : ℂ) * f (x + (n : ℤ)^2) := by
  simp only [finitePlusSquareOperator, _root_.smul_apply, _root_.sum_apply,
    lp.coeFn_smul, lp.coeFn_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    integerTranslate_apply, sub_neg_eq_add]

theorem finitePlusSquareOperator_reflection {p : ENNReal} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) :
    finitePlusSquareOperator hp S c w =
      reflectContinuousLinearMap (finiteSquareOperator hp S c w) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  simp only [finitePlusSquareOperator_apply, reflectContinuousLinearMap_apply,
    finiteSquareOperator_apply, reflectLp_apply]
  simp only [neg_sub, sub_neg_eq_add, add_comm]

theorem finitePlusSquareOperator_norm {p : ENNReal} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) :
    ‖finitePlusSquareOperator hp S c w‖ = ‖finiteSquareOperator hp S c w‖ := by
  rw [finitePlusSquareOperator_reflection, reflectContinuousLinearMap_norm]

theorem finitePlusSquareKernel_finiteInput {p : ENNReal} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    finiteConvolution (finitePlusSquareKernel S c w) F f x =
      finitePlusSquareOperator hp S c w (finiteInputLp F f p) x := by
  rw [← finiteSquareKernel_reflection, finiteConvolution_reflect,
    finiteSquareKernel_finiteInput hp, finitePlusSquareOperator_reflection,
    reflectContinuousLinearMap_apply, reflectLp_finiteInput]

noncomputable def plusSquareAverageKernel (N : ℕ) (w : ℕ → ℝ) : ℤ → ℂ :=
  finitePlusSquareKernel (Ioc 0 N) (N : ℝ)⁻¹ w

noncomputable def annularPlusSquareAverageKernel (N : ℕ) (w : ℕ → ℝ) : ℤ → ℂ :=
  finitePlusSquareKernel (Ioc (N/2) N) (N : ℝ)⁻¹ w

theorem weightedSquareAverageKernel_reflection (N : ℕ) (w : ℕ → ℝ) :
    reflectSequence (weightedSquareAverageKernel N w) = plusSquareAverageKernel N w :=
  finiteSquareKernel_reflection _ _ _

theorem annularWeightedSquareAverageKernel_reflection (N : ℕ) (w : ℕ → ℝ) :
    reflectSequence (annularWeightedSquareAverageKernel N w) =
      annularPlusSquareAverageKernel N w := finiteSquareKernel_reflection _ _ _

noncomputable def plusSquareAverage {p : ENNReal} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (N : ℕ) (w : ℕ → ℝ) : ℓ^p(ℤ, ℂ) →L[ℂ] ℓ^p(ℤ, ℂ) :=
  finitePlusSquareOperator hp (Ioc 0 N) (N : ℝ)⁻¹ w

noncomputable def annularPlusSquareAverage {p : ENNReal} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (N : ℕ) (w : ℕ → ℝ) : ℓ^p(ℤ, ℂ) →L[ℂ] ℓ^p(ℤ, ℂ) :=
  finitePlusSquareOperator hp (Ioc (N/2) N) (N : ℝ)⁻¹ w

theorem plusSquareAverage_apply {p : ENNReal} [Fact (1 ≤ p)] (hp : 0 < p.toReal)
    (N : ℕ) (w : ℕ → ℝ) (f : ℓ^p(ℤ, ℂ)) (x : ℤ) :
    plusSquareAverage hp N w f x =
      Complex.ofReal ((N : ℝ)⁻¹) * ∑ n ∈ Ioc 0 N, (w n : ℂ) * f (x + (n : ℤ)^2) :=
  finitePlusSquareOperator_apply hp (Ioc 0 N) (N : ℝ)⁻¹ w f x

theorem annularPlusSquareAverage_apply {p : ENNReal} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (N : ℕ) (w : ℕ → ℝ) (f : ℓ^p(ℤ, ℂ)) (x : ℤ) :
    annularPlusSquareAverage hp N w f x =
      Complex.ofReal ((N : ℝ)⁻¹) * ∑ n ∈ Ioc (N/2) N, (w n : ℂ) * f (x + (n : ℤ)^2) :=
  finitePlusSquareOperator_apply hp (Ioc (N/2) N) (N : ℝ)⁻¹ w f x

theorem plusSquareAverage_reflection {p : ENNReal} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (N : ℕ) (w : ℕ → ℝ) :
    plusSquareAverage hp N w = reflectContinuousLinearMap (weightedSquareAverage hp N w) :=
  finitePlusSquareOperator_reflection hp _ _ _

theorem annularPlusSquareAverage_reflection {p : ENNReal} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (N : ℕ) (w : ℕ → ℝ) :
    annularPlusSquareAverage hp N w =
      reflectContinuousLinearMap (annularWeightedSquareAverage hp N w) :=
  finitePlusSquareOperator_reflection hp _ _ _

theorem minusSquareAverage_from_plus {p : ENNReal} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (N : ℕ) (w : ℕ → ℝ) :
    weightedSquareAverage hp N w = reflectContinuousLinearMap (plusSquareAverage hp N w) := by
  rw [plusSquareAverage_reflection, reflectContinuousLinearMap_involutive]

theorem annularMinusSquareAverage_from_plus {p : ENNReal} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (N : ℕ) (w : ℕ → ℝ) :
    annularWeightedSquareAverage hp N w =
      reflectContinuousLinearMap (annularPlusSquareAverage hp N w) := by
  rw [annularPlusSquareAverage_reflection, reflectContinuousLinearMap_involutive]

theorem plusSquareAverage_opNorm {p : ENNReal} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (N : ℕ) (w : ℕ → ℝ) :
    ‖plusSquareAverage hp N w‖ = ‖weightedSquareAverage hp N w‖ := by
  rw [plusSquareAverage_reflection, reflectContinuousLinearMap_norm]

theorem annularPlusSquareAverage_opNorm {p : ENNReal} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (N : ℕ) (w : ℕ → ℝ) :
    ‖annularPlusSquareAverage hp N w‖ = ‖annularWeightedSquareAverage hp N w‖ := by
  rw [annularPlusSquareAverage_reflection, reflectContinuousLinearMap_norm]

def plusSquareAverageWindow (N : ℕ) (x : ℤ) : Finset ℤ := Icc x (x + (N : ℤ)^2)

theorem squareAverageWindow_reflection (N : ℕ) (x : ℤ) :
    reflectedFinset (squareAverageWindow N x) = plusSquareAverageWindow N (-x) := by
  ext y
  simp only [mem_reflectedFinset, squareAverageWindow, plusSquareAverageWindow, mem_Icc]
  omega

theorem finitePlusSquareKernel_support_interval (S : Finset ℕ) (N : ℕ)
    (hS : S ⊆ Ioc 0 N) (c : ℝ) (w : ℕ → ℝ) {z : ℤ}
    (hz : z ∉ Icc (-((N : ℤ)^2)) (-1)) : finitePlusSquareKernel S c w z = 0 := by
  rw [← finiteSquareKernel_reflection, reflectSequence_apply]
  apply finiteSquareKernel_support_interval S N hS c w
  intro h
  apply hz
  simp only [mem_Icc] at h ⊢
  omega

theorem finitePlusSquareKernel_localization (S : Finset ℕ) (N : ℕ)
    (hS : S ⊆ Ioc 0 N) (c : ℝ) (w : ℕ → ℝ) (F : Finset ℤ) (x : ℤ) :
    indicatorConvolution (finitePlusSquareKernel S c w) F x =
      indicatorConvolution (finitePlusSquareKernel S c w) (F ∩ plusSquareAverageWindow N x) x := by
  have hI : reflectedFinset (F ∩ plusSquareAverageWindow N x) =
      reflectedFinset F ∩ squareAverageWindow N (-x) := by
    ext y
    simp only [mem_reflectedFinset, mem_inter, plusSquareAverageWindow,
      squareAverageWindow, mem_Icc]
    constructor
    · rintro ⟨hy, ha, hb⟩
      exact ⟨hy, by omega, by omega⟩
    · rintro ⟨hy, ha, hb⟩
      exact ⟨hy, by omega, by omega⟩
  rw [← finiteSquareKernel_reflection, indicatorConvolution_reflect,
    indicatorConvolution_reflect, hI]
  exact finiteSquareKernel_localization S N hS c w (reflectedFinset F) (-x)

end PrimeSquares
