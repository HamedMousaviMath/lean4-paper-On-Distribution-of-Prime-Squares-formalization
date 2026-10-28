import PrimeSquares.SquareAverageKernels

/-!
# Full and annular weighted square averages with the source normalization

N is the arithmetic cutoff. The spatial scale is N^2. The interval of
indices is 0<n<=N, and the annular interval is N/2<n<=N, with natural
integer division. These definitions include prime powers when w is Lambda.
-/

open Finset
open scoped lp

namespace PrimeSquares

noncomputable def weightedSquareAverageKernel (N : ℕ) (w : ℕ → ℝ) : ℤ → ℂ :=
  finiteSquareKernel (Ioc 0 N) (N : ℝ)⁻¹ w

noncomputable def annularWeightedSquareAverageKernel (N : ℕ) (w : ℕ → ℝ) : ℤ → ℂ :=
  finiteSquareKernel (Ioc (N/2) N) (N : ℝ)⁻¹ w

noncomputable def weightedSquareAverage {P : ENNReal} [Fact (1 ≤ P)]
    (hp : 0 < P.toReal) (N : ℕ) (w : ℕ → ℝ) :
    lp (fun _ : ℤ => ℂ) P →L[ℂ] lp (fun _ : ℤ => ℂ) P :=
  finiteSquareOperator hp (Ioc 0 N) (N : ℝ)⁻¹ w

noncomputable def annularWeightedSquareAverage {P : ENNReal} [Fact (1 ≤ P)]
    (hp : 0 < P.toReal) (N : ℕ) (w : ℕ → ℝ) :
    lp (fun _ : ℤ => ℂ) P →L[ℂ] lp (fun _ : ℤ => ℂ) P :=
  finiteSquareOperator hp (Ioc (N/2) N) (N : ℝ)⁻¹ w

theorem annularIndices_subset (N : ℕ) : Ioc (N/2) N ⊆ Ioc 0 N := by
  intro n hn
  simp only [mem_Ioc] at hn ⊢
  omega

theorem weightedSquareAverage_apply {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    (N : ℕ) (w : ℕ → ℝ) (f : lp (fun _ : ℤ => ℂ) P) (x : ℤ) :
    weightedSquareAverage hp N w f x = Complex.ofReal ((N : ℝ)⁻¹) *
      ∑ n ∈ Ioc 0 N, (w n : ℂ) * f (x-(n : ℤ)^2) :=
  finiteSquareOperator_apply hp (Ioc 0 N) ((N : ℝ)⁻¹) w f x

theorem annularWeightedSquareAverage_apply {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    (N : ℕ) (w : ℕ → ℝ) (f : lp (fun _ : ℤ => ℂ) P) (x : ℤ) :
    annularWeightedSquareAverage hp N w f x = Complex.ofReal ((N : ℝ)⁻¹) *
      ∑ n ∈ Ioc (N/2) N, (w n : ℂ) * f (x-(n : ℤ)^2) :=
  finiteSquareOperator_apply hp (Ioc (N/2) N) ((N : ℝ)⁻¹) w f x

theorem weightedSquareAverage_finiteInput {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    (N : ℕ) (w : ℕ → ℝ) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    finiteConvolution (weightedSquareAverageKernel N w) F f x =
      weightedSquareAverage hp N w (finiteInputLp F f P) x :=
  finiteSquareKernel_finiteInput hp _ _ w F f x

theorem annularWeightedSquareAverage_finiteInput {P : ENNReal} [Fact (1 ≤ P)]
    (hp : 0 < P.toReal) (N : ℕ) (w : ℕ → ℝ) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    finiteConvolution (annularWeightedSquareAverageKernel N w) F f x =
      annularWeightedSquareAverage hp N w (finiteInputLp F f P) x :=
  finiteSquareKernel_finiteInput hp _ _ w F f x

theorem normalized_square_mass_le {N : ℕ} (hN : 0 < N) (S : Finset ℕ)
    (hS : S ⊆ Ioc 0 N) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) {C : ℝ}
    (hmass : ∑ n ∈ Ioc 0 N, w n ≤ C * N) :
    (N : ℝ)⁻¹ * ∑ n ∈ S, w n ≤ C := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : ∑ n ∈ S, w n ≤ ∑ n ∈ Ioc 0 N, w n :=
    sum_le_sum_of_subset_of_nonneg hS (fun n _ _ => hw n)
  calc
    _ ≤ (N : ℝ)⁻¹ * (C * N) :=
      mul_le_mul_of_nonneg_left (hs.trans hmass) (inv_nonneg.mpr hNr.le)
    _ = C := by rw [mul_left_comm, inv_mul_cancel₀ hNr.ne', mul_one]

theorem normalizedSquareOperator_norm_le {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    {N : ℕ} (hN : 0 < N) (S : Finset ℕ) (hS : S ⊆ Ioc 0 N)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) {C : ℝ}
    (hmass : ∑ n ∈ Ioc 0 N, w n ≤ C * N) :
    ‖finiteSquareOperator hp S (N : ℝ)⁻¹ w‖ ≤ C :=
  (finiteSquareOperator_norm_le_mass hp S (by positivity) w (fun n _ => hw n)).trans
    (normalized_square_mass_le hN S hS w hw hmass)

theorem normalizedSquareKernel_l2_bound {N : ℕ} (hN : 0 < N) (S : Finset ℕ)
    (hS : S ⊆ Ioc 0 N) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) {C : ℝ}
    (hmass : ∑ n ∈ Ioc 0 N, w n ≤ C * N) :
    KernelL2Bound (finiteSquareKernel S (N : ℝ)⁻¹ w) C :=
  kernelL2Bound_mono (finiteSquareKernel_l2_bound S (by positivity) w (fun n _ => hw n))
    (normalized_square_mass_le hN S hS w hw hmass)

theorem square_inverse_spatial_scale (N : ℕ) :
    ((N : ℝ)^2)^(-(1/2 : ℝ)) = (N : ℝ)⁻¹ := by
  have hNr : (0 : ℝ) ≤ N := by positivity
  rw [← Real.rpow_two, ← Real.rpow_mul hNr]
  rw [show (2 : ℝ) * (-(1/2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]

theorem squareKernel_local_bound (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Ioc 0 N)
    (F : Finset ℤ) (x : ℤ) :
    ‖indicatorConvolution (finiteSquareKernel S (N : ℝ)⁻¹ (fun _ => 1)) F x‖ ≤
      ((N : ℝ)^2)^(-(1/2 : ℝ)) * ‖finiteIndicatorLp (F ∩ squareAverageWindow N x) 1‖ := by
  rw [square_inverse_spatial_scale N]
  simpa only [mul_one] using finiteSquareKernel_local_bound S N hS (by positivity)
    (by norm_num : (0 : ℝ) ≤ 1) (fun _ => 1) (fun _ _ => by norm_num)
    (fun _ _ => le_refl (1 : ℝ)) F x

end PrimeSquares
