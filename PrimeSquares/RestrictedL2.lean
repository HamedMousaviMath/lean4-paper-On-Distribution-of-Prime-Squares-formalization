import PrimeSquares.RestrictedPowers
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Genuine l2 input and globalization of restricted finite-set bounds

The extra hypothesis of Corollary 4.15 is an actual continuous linear l2
operator, agreeing with the convolution on every finite indicator. Large
cardinality products are controlled by this input, with exact N scaling.
-/

open Finset
open scoped lp

namespace PrimeSquares

def KernelL2Bound (K : ℤ → ℂ) (C : ℝ) : Prop :=
  ∃ T : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ),
    (∀ F : Finset ℤ, ∀ x, indicatorConvolution K F x = T (finiteIndicatorLp F 2) x) ∧ ‖T‖ ≤ C

theorem kernelL2Bound_mono {K : ℤ → ℂ} {C D : ℝ} (h : KernelL2Bound K C) (hCD : C ≤ D) :
    KernelL2Bound K D := by
  obtain ⟨T, heq, hT⟩ := h
  exact ⟨T, heq, hT.trans hCD⟩

theorem finiteIndicatorLp_singleton_two (i : ℤ) :
    finiteIndicatorLp {i} 2 = lp.single 2 i (1 : ℂ) := by
  apply lp.ext
  funext x
  simp only [finiteIndicatorLp, finiteIndicator, mem_singleton, lp.single_apply, Pi.single_apply]

/-- The l2 realization is uniquely determined by the kernel on indicators.
This uses continuity, linearity and the density of finite-support inputs. -/
theorem kernelL2_realization_unique {K : ℤ → ℂ}
    (T U : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : ∀ F : Finset ℤ, ∀ x, indicatorConvolution K F x = T (finiteIndicatorLp F 2) x)
    (hU : ∀ F : Finset ℤ, ∀ x, indicatorConvolution K F x = U (finiteIndicatorLp F 2) x) : T = U := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro i
  apply ContinuousLinearMap.ext
  intro z
  change T (lp.single 2 i z) = U (lp.single 2 i z)
  have hi : T (finiteIndicatorLp {i} 2) = U (finiteIndicatorLp {i} 2) := by
    apply lp.ext
    funext x
    exact (hT {i} x).symm.trans (hU {i} x)
  have he : lp.single 2 i z = z • finiteIndicatorLp {i} 2 := by
    rw [finiteIndicatorLp_singleton_two]
    simpa only [smul_eq_mul, mul_one] using lp.single_smul (E := fun _ : ℤ => ℂ) 2 i z (1 : ℂ)
  rw [he, map_smul, map_smul, hi]

/-- The strong p=2 case is exactly the supplied actual l2 bounds. -/
theorem kernelL2_pair_strong_two {KA KB : ℤ → ℂ} {CA CB : ℝ}
    (hA : KernelL2Bound KA CA) (hB : KernelL2Bound KB CB) :
    ∃ TA TB : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ),
      (∀ F : Finset ℤ, ∀ x, indicatorConvolution KA F x = TA (finiteIndicatorLp F 2) x) ∧
      (∀ F : Finset ℤ, ∀ x, indicatorConvolution KB F x = TB (finiteIndicatorLp F 2) x) ∧
      ∀ f : ℓ²(ℤ, ℂ), ‖TA f‖ + ‖TB f‖ ≤ (CA + CB) * ‖f‖ := by
  obtain ⟨TA, hTA, hnormA⟩ := hA
  obtain ⟨TB, hTB, hnormB⟩ := hB
  refine ⟨TA, TB, hTA, hTB, ?_⟩
  intro f
  calc
    _ ≤ CA * ‖f‖ + CB * ‖f‖ := add_le_add (TA.le_of_opNorm_le hnormA f) (TB.le_of_opNorm_le hnormB f)
    _ = _ := by ring

theorem restrictedKernelPairing_l2_bound {K : ℤ → ℂ} {C : ℝ} (h : KernelL2Bound K C)
    (F G : Finset ℤ) :
    ‖restrictedKernelPairing K F G‖ ≤ C * Real.sqrt (F.card : ℝ) * Real.sqrt (G.card : ℝ) := by
  obtain ⟨T, heq, hT⟩ := h
  have hp : restrictedKernelPairing K F G = ∑ x ∈ G, T (finiteIndicatorLp F 2) x :=
    sum_congr rfl (fun x _ => heq F x)
  rw [hp]
  have hn := (T.le_opNorm (finiteIndicatorLp F 2)).trans
    (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  rw [finiteIndicatorLp_two_norm] at hn
  exact (norm_finite_sum_le_lp_two G (T (finiteIndicatorLp F 2))).trans
    (mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg _))

theorem finiteSetDensity_half_rpow {N : ℝ} (hN : 0 < N) (F G : Finset ℤ) :
    (finiteSetDensity N F G) ^ (1 / 2 : ℝ) =
      Real.sqrt (F.card : ℝ) * Real.sqrt (G.card : ℝ) / N := by
  rw [← Real.sqrt_eq_rpow, finiteSetDensity,
    Real.sqrt_div (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
    Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hN.le]

theorem restrictedKernelPairing_l2_normalized {K : ℤ → ℂ} {C N : ℝ}
    (h : KernelL2Bound K C) (hN : 0 < N) (F G : Finset ℤ) :
    ‖restrictedKernelPairing K F G‖ / N ≤ C * (finiteSetDensity N F G) ^ (1 / 2 : ℝ) := by
  calc
    _ ≤ (C * Real.sqrt (F.card : ℝ) * Real.sqrt (G.card : ℝ)) / N :=
      div_le_div_of_nonneg_right (restrictedKernelPairing_l2_bound h F G) hN.le
    _ = _ := by rw [finiteSetDensity_half_rpow hN F G]; ring

/-- The restricted estimate for |F||G|<=N^2 and the actual l2 input give
the same density power for every pair of finite sets, with one constant. -/
theorem restricted_pairing_globalization {K : ℤ → ℂ} {N p CSmall CTwo : ℝ}
    (hN : 0 < N) (hp : 0 < p) (hp2 : p ≤ 2) (hSmall : 0 ≤ CSmall) (hTwo : 0 ≤ CTwo)
    (h2 : KernelL2Bound K CTwo)
    (hlocal : ∀ F G : Finset ℤ, (F.card : ℝ) * (G.card : ℝ) ≤ N ^ 2 →
      ‖restrictedKernelPairing K F G‖ / N ≤ CSmall * (finiteSetDensity N F G) ^ (1 / p))
    (F G : Finset ℤ) :
    ‖restrictedKernelPairing K F G‖ / N ≤ (CSmall + CTwo) * (finiteSetDensity N F G) ^ (1 / p) := by
  have hδ : 0 ≤ finiteSetDensity N F G :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)
  have hpow : 0 ≤ (finiteSetDensity N F G) ^ (1 / p) := Real.rpow_nonneg hδ _
  by_cases hFG : (F.card : ℝ) * (G.card : ℝ) ≤ N ^ 2
  · exact (hlocal F G hFG).trans (mul_le_mul_of_nonneg_right (by linarith) hpow)
  · have hδ1 : 1 ≤ finiteSetDensity N F G :=
      (one_le_div (sq_pos_of_pos hN)).mpr (le_of_lt (lt_of_not_ge hFG))
    have he := Real.rpow_le_rpow_of_exponent_le hδ1 (improving_reciprocal_half hp hp2)
    exact (restrictedKernelPairing_l2_normalized h2 hN F G).trans
      ((mul_le_mul_of_nonneg_left he hTwo).trans
        (mul_le_mul_of_nonneg_right (by linarith) hpow))

theorem density_denormalize_bound {N p D R : ℝ} (hN : 0 < N) (hp : 1 < p)
    (F G : Finset ℤ) (h : R / N ≤ D * (finiteSetDensity N F G) ^ (1 / p)) :
    R ≤ D * N ^ (1 / holderConjugate p - 1 / p) * (F.card : ℝ) ^ (1 / p) *
      (G.card : ℝ) ^ (1 / p) := by
  calc
    _ ≤ (D * (finiteSetDensity N F G) ^ (1 / p)) * N := (div_le_iff₀ hN).mp h
    _ = D * (N * (finiteSetDensity N F G) ^ (1 / p)) := by ring
    _ = _ := by rw [finiteSetDensity_power_scaling hN F G, holderConjugate_scaling hp]; ring

end PrimeSquares
