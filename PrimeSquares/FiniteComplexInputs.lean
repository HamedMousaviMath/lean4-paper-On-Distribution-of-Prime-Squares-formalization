import PrimeSquares.LpInclusion
import PrimeSquares.PositivePairing

/-!
# Finite complex inputs and the actual convolution operator

Finite inputs are linear combinations of lp.single, with arbitrary complex
coefficients. The l2 realization agreeing on indicators agrees with these
inputs as well. Positivity extends indicator-pair bounds to bounded finite
complex inputs, including their phases and zero coefficients.
-/

open Finset
open scoped lp

namespace PrimeSquares

noncomputable def finiteInputLp (F : Finset ℤ) (f : ℤ → ℂ) (P : ENNReal) :
    lp (fun _ : ℤ => ℂ) P := ∑ y ∈ F, lp.single P y (f y)

theorem finiteInputLp_apply (F : Finset ℤ) (f : ℤ → ℂ) (P : ENNReal) (x : ℤ) :
    finiteInputLp F f P x = if x ∈ F then f x else 0 := by
  simp only [finiteInputLp, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, sum_pi_single]

theorem finiteInputLp_one (F : Finset ℤ) (P : ENNReal) :
    finiteInputLp F (fun _ => 1) P = finiteIndicatorLp F P := by
  apply lp.ext
  funext x
  exact finiteInputLp_apply F (fun _ => 1) P x

theorem finiteInputLp_norm_rpow (F : Finset ℤ) (f : ℤ → ℂ) (P : ENNReal)
    (hp : 0 < P.toReal) :
    ‖finiteInputLp F f P‖ ^ P.toReal = ∑ y ∈ F, ‖f y‖ ^ P.toReal :=
  lp.norm_sum_single hp f F

theorem finiteInputLp_norm (F : Finset ℤ) (f : ℤ → ℂ) (P : ENNReal)
    (hp : 0 < P.toReal) :
    ‖finiteInputLp F f P‖ = (∑ y ∈ F, ‖f y‖ ^ P.toReal) ^ (1 / P.toReal) := by
  calc
    _ = (‖finiteInputLp F f P‖ ^ P.toReal) ^ (1 / P.toReal) := by
      simpa only [one_div] using
        (Real.rpow_rpow_inv (lp.norm_nonneg' _) hp.ne').symm
    _ = _ := by rw [finiteInputLp_norm_rpow F f P hp]

theorem finiteInputLp_norm_le {P : ENNReal} [Fact (1 ≤ P)] (hP : P ≠ 0)
    (F : Finset ℤ) (f : lp (fun _ : ℤ => ℂ) P) :
    ‖finiteInputLp F f P‖ ≤ ‖f‖ := by
  apply lp.norm_mono hP
  intro x
  rw [finiteInputLp_apply]
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (f x)

noncomputable def finiteConvolution (K : ℤ → ℂ) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑ y ∈ F, K (x - y) * f y

noncomputable def finiteKernelPairing (K : ℤ → ℂ) (F G : Finset ℤ)
    (f g : ℤ → ℂ) : ℂ := ∑ x ∈ G, finiteConvolution K F f x * star (g x)

theorem finiteConvolution_indicator (K : ℤ → ℂ) (F : Finset ℤ) (x : ℤ) :
    finiteConvolution K F (fun _ => 1) x = indicatorConvolution K F x := by
  simp only [finiteConvolution, mul_one, indicatorConvolution]

theorem finiteKernelPairing_indicators (K : ℤ → ℂ) (F G : Finset ℤ) :
    finiteKernelPairing K F G (fun _ => 1) (fun _ => 1) = restrictedKernelPairing K F G := by
  simp only [finiteKernelPairing, star_one, mul_one, finiteConvolution_indicator,
    restrictedKernelPairing]

theorem kernelL2_realization_single {K : ℤ → ℂ}
    (T : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : ∀ F : Finset ℤ, ∀ x, indicatorConvolution K F x = T (finiteIndicatorLp F 2) x)
    (i : ℤ) (z : ℂ) (x : ℤ) : T (lp.single 2 i z) x = K (x - i) * z := by
  have he : lp.single 2 i z = z • finiteIndicatorLp {i} 2 := by
    rw [finiteIndicatorLp_singleton_two]
    simpa only [smul_eq_mul, mul_one] using
      lp.single_smul (E := fun _ : ℤ => ℂ) 2 i z (1 : ℂ)
  rw [he, map_smul]
  change z * T (finiteIndicatorLp {i} 2) x = _
  rw [← hT]
  simp only [indicatorConvolution, sum_singleton, mul_comm]

theorem kernelL2_realization_finiteInput {K : ℤ → ℂ}
    (T : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : ∀ F : Finset ℤ, ∀ x, indicatorConvolution K F x = T (finiteIndicatorLp F 2) x)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    T (finiteInputLp F f 2) x = finiteConvolution K F f x := by
  simp only [finiteInputLp, map_sum, lp.coeFn_sum, Finset.sum_apply, finiteConvolution]
  exact sum_congr rfl (fun y _ => kernelL2_realization_single T hT y (f y) x)

theorem restrictedKernelPairing_norm_sum {K : ℤ → ℂ} (hK : NonnegativeKernel K)
    (F G : Finset ℤ) :
    ‖restrictedKernelPairing K F G‖ = ∑ x ∈ G, ∑ y ∈ F, ‖K (x - y)‖ := by
  rw [restrictedKernelPairing_norm_positive hK]
  apply sum_congr rfl
  intro x _
  simp only [indicatorConvolution, Complex.re_sum]
  exact sum_congr rfl (fun y _ => (complex_norm_eq_re (hK (x-y)).1 (hK (x-y)).2).symm)

/-- Complex phases cause no loss beyond the maximum magnitudes on each
finite set, because all kernel coefficients are nonnegative real numbers. -/
theorem finiteKernelPairing_bound_by_indicators {K : ℤ → ℂ} (hK : NonnegativeKernel K)
    (F G : Finset ℤ) (f g : ℤ → ℂ) {A B : ℝ} (hA : 0 ≤ A)
    (hf : ∀ y ∈ F, ‖f y‖ ≤ A) (hg : ∀ x ∈ G, ‖g x‖ ≤ B) :
    ‖finiteKernelPairing K F G f g‖ ≤ A * B * ‖restrictedKernelPairing K F G‖ := by
  calc
    _ ≤ ∑ x ∈ G, ‖finiteConvolution K F f x * star (g x)‖ := norm_sum_le _ _
    _ = ∑ x ∈ G, ‖finiteConvolution K F f x‖ * ‖g x‖ := by
      simp only [norm_mul, norm_star]
    _ ≤ ∑ x ∈ G, (∑ y ∈ F, ‖K (x-y)‖ * A) * B := by
      apply sum_le_sum
      intro x hx
      apply mul_le_mul _ (hg x hx) (norm_nonneg _) (sum_nonneg fun y _ => by positivity)
      calc
        _ ≤ ∑ y ∈ F, ‖K (x-y) * f y‖ := norm_sum_le _ _
        _ ≤ _ := sum_le_sum fun y hy => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hf y hy) (norm_nonneg _)
    _ = _ := by
      rw [restrictedKernelPairing_norm_sum hK]
      simp only [← sum_mul]
      ring

end PrimeSquares
