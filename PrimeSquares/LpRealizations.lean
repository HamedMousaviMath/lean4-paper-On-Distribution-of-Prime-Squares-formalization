import PrimeSquares.FiniteComplexInputs

/-!
# Actual lp operator realizations and passage from finite inputs

An actual continuous l2 realization gives a continuous lp-to-lq realization
for 1 <= p <= 2 <= q < infinity, with a coarse norm bound. This is not the
N-dependent improving bound. A separate density theorem transfers any
proved finite-input norm estimate to all lp inputs with the same constant.
-/

open Finset
open scoped lp

namespace PrimeSquares

variable {P Q : ENNReal} [Fact (1 ≤ P)] [Fact (1 ≤ Q)]

noncomputable def lpL2Lift (T : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hP2 : P ≤ 2) (h2Q : 2 ≤ Q) (hQ : Q ≠ ⊤) :
    lp (fun _ : ℤ => ℂ) P →L[ℂ] lp (fun _ : ℤ => ℂ) Q :=
  (lpInclusion h2Q hQ).comp
    (T.comp (lpInclusion hP2 (by norm_num : (2 : ENNReal) ≠ ⊤)))

theorem lpL2Lift_apply (T : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hP2 : P ≤ 2) (h2Q : 2 ≤ Q) (hQ : Q ≠ ⊤)
    (f : lp (fun _ : ℤ => ℂ) P) (x : ℤ) :
    lpL2Lift T hP2 h2Q hQ f x = T (lpInclusion hP2 (by norm_num) f) x := rfl

theorem lpL2Lift_bound (T : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hP2 : P ≤ 2) (h2Q : 2 ≤ Q) (hQ : Q ≠ ⊤)
    (f : lp (fun _ : ℤ => ℂ) P) :
    ‖lpL2Lift T hP2 h2Q hQ f‖ ≤ ‖T‖ * ‖f‖ := by
  calc
    _ ≤ ‖T (lpInclusion hP2 (by norm_num) f)‖ :=
      lpInclusion_contracts h2Q hQ (T (lpInclusion hP2 (by norm_num) f))
    _ ≤ ‖T‖ * ‖lpInclusion hP2 (by norm_num) f‖ := T.le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_left (lpInclusion_contracts hP2 (by norm_num) f)
      (norm_nonneg _)

theorem lpL2Lift_norm_le (T : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hP2 : P ≤ 2) (h2Q : 2 ≤ Q) (hQ : Q ≠ ⊤) :
    ‖lpL2Lift T hP2 h2Q hQ‖ ≤ ‖T‖ :=
  (lpL2Lift T hP2 h2Q hQ).opNorm_le_bound (norm_nonneg _) (lpL2Lift_bound T hP2 h2Q hQ)

theorem lpInclusion_finiteInput (hPQ : P ≤ Q) (hQ : Q ≠ ⊤)
    (F : Finset ℤ) (f : ℤ → ℂ) :
    lpInclusion hPQ hQ (finiteInputLp F f P) = finiteInputLp F f Q := by
  apply lp.ext
  funext x
  rw [lpInclusion_apply, finiteInputLp_apply, finiteInputLp_apply]

theorem lpL2Lift_finiteInput {K : ℤ → ℂ}
    (T : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : ∀ F : Finset ℤ, ∀ x, indicatorConvolution K F x = T (finiteIndicatorLp F 2) x)
    (hP2 : P ≤ 2) (h2Q : 2 ≤ Q) (hQ : Q ≠ ⊤)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    lpL2Lift T hP2 h2Q hQ (finiteInputLp F f P) x = finiteConvolution K F f x := by
  rw [lpL2Lift_apply, lpInclusion_finiteInput]
  exact kernelL2_realization_finiteInput T hT F f x

def KernelLpBound (K : ℤ → ℂ) (P Q : ENNReal) [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    (C : ℝ) : Prop :=
  ∃ T : lp (fun _ : ℤ => ℂ) P →L[ℂ] lp (fun _ : ℤ => ℂ) Q,
    (∀ F : Finset ℤ, ∀ x, indicatorConvolution K F x = T (finiteIndicatorLp F P) x) ∧ ‖T‖ ≤ C

/-- This coarse bound is inherited from l2; it supplies an operator, not
the improved scale-dependent norm required in Corollary 4.15. -/
theorem kernelLpBound_of_l2 {K : ℤ → ℂ} {C : ℝ} (h2 : KernelL2Bound K C)
    (hP2 : P ≤ 2) (h2Q : 2 ≤ Q) (hQ : Q ≠ ⊤) : KernelLpBound K P Q C := by
  obtain ⟨T, hT, hnorm⟩ := h2
  refine ⟨lpL2Lift T hP2 h2Q hQ, ?_, (lpL2Lift_norm_le T hP2 h2Q hQ).trans hnorm⟩
  intro F x
  rw [lpL2Lift_apply, lpInclusion_finiteIndicator]
  exact hT F x

theorem finiteIndicatorLp_singleton (P : ENNReal) (i : ℤ) :
    finiteIndicatorLp {i} P = lp.single P i (1 : ℂ) := by
  apply lp.ext
  funext x
  simp only [finiteIndicatorLp, finiteIndicator, mem_singleton, lp.single_apply, Pi.single_apply]

theorem kernelLp_realization_unique {K : ℤ → ℂ} (hP : P ≠ ⊤)
    (T U : lp (fun _ : ℤ => ℂ) P →L[ℂ] lp (fun _ : ℤ => ℂ) Q)
    (hT : ∀ F : Finset ℤ, ∀ x, indicatorConvolution K F x = T (finiteIndicatorLp F P) x)
    (hU : ∀ F : Finset ℤ, ∀ x, indicatorConvolution K F x = U (finiteIndicatorLp F P) x) :
    T = U := by
  apply lp.ext_continuousLinearMap hP
  intro i
  apply ContinuousLinearMap.ext
  intro z
  change T (lp.single P i z) = U (lp.single P i z)
  have hi : T (finiteIndicatorLp {i} P) = U (finiteIndicatorLp {i} P) := by
    apply lp.ext
    funext x
    exact (hT {i} x).symm.trans (hU {i} x)
  have he : lp.single P i z = z • finiteIndicatorLp {i} P := by
    rw [finiteIndicatorLp_singleton]
    simpa only [smul_eq_mul, mul_one] using
      lp.single_smul (E := fun _ : ℤ => ℂ) P i z (1 : ℂ)
  rw [he, map_smul, map_smul, hi]

/-- A finite-input estimate, once proved, extends with exactly the same
constant. No interpolation conclusion is supplied as an external input. -/
theorem lp_bound_of_finiteInputs {D : ℝ} (hP : P ≠ ⊤)
    (T : lp (fun _ : ℤ => ℂ) P →L[ℂ] lp (fun _ : ℤ => ℂ) Q)
    (hfinite : ∀ (F : Finset ℤ) (f : ℤ → ℂ),
      ‖T (finiteInputLp F f P)‖ ≤ D * ‖finiteInputLp F f P‖)
    (f : lp (fun _ : ℤ => ℂ) P) : ‖T f‖ ≤ D * ‖f‖ := by
  have hconv : Filter.Tendsto (fun F : Finset ℤ => finiteInputLp F f P)
      Filter.atTop (nhds f) := lp.hasSum_single hP f
  exact le_of_tendsto_of_tendsto
    ((T.continuous.tendsto f).comp hconv |>.norm)
    (tendsto_const_nhds.mul hconv.norm)
    (Filter.Eventually.of_forall fun F => hfinite F f)

theorem lp_opNorm_bound_of_finiteInputs {D : ℝ} (hD : 0 ≤ D) (hP : P ≠ ⊤)
    (T : lp (fun _ : ℤ => ℂ) P →L[ℂ] lp (fun _ : ℤ => ℂ) Q)
    (hfinite : ∀ (F : Finset ℤ) (f : ℤ → ℂ),
      ‖T (finiteInputLp F f P)‖ ≤ D * ‖finiteInputLp F f P‖) : ‖T‖ ≤ D :=
  T.opNorm_le_bound hD (lp_bound_of_finiteInputs hP T hfinite)

end PrimeSquares
