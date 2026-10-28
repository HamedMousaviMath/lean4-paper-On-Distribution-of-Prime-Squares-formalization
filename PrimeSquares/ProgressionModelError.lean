import PrimeSquares.PrefixErrorBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Quantitative partial summation after subtracting a differentiable model

The prefix is the actual progression von Mangoldt sum. Model regularity
and a uniform bound on the actual prefix difference imply the weighted
residue error, with both endpoints and the exact normalization retained.
-/

open Finset MeasureTheory

namespace PrimeSquares

theorem progression_prefix_derivative_integrable (q : ℕ) (r : ZMod q) (θ : ℝ)
    {a b : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t => quadraticOscillationDerivative θ t * progressionMangoldtPrefix q r t)
      (Set.Ioc a b) := by
  have h := integrableOn_mul_sum_Icc (progressionMangoldtCoeff q r) (m := 0) (b := b) ha
    (quadraticOscillationDerivative_continuous θ).integrableOn_Icc
  exact h.mono_set Set.Ioc_subset_Icc_self

theorem squareResidueSum_model_error_identity (q : ℕ) (r : ZMod q) (θ : ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (H H' : ℝ → ℂ)
    (hH : ∀ t ∈ Set.Icc a b, HasDerivAt H (H' t) t)
    (hH' : IntervalIntegrable H' volume a b) :
    squareResidueSum (Ioc ⌊a⌋₊ ⌊b⌋₊) q r ArithmeticFunction.vonMangoldt (θ : PrimeCircle) -
        ∫ t in Set.Ioc a b, quadraticOscillation θ t * H' t =
      quadraticOscillation θ b * (progressionMangoldtPrefix q r b - H b) -
      quadraticOscillation θ a * (progressionMangoldtPrefix q r a - H a) -
      ∫ t in Set.Ioc a b, quadraticOscillationDerivative θ t *
        (progressionMangoldtPrefix q r t - H t) := by
  have hHc : ContinuousOn H (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact fun t ht => (hH t ht).continuousAt.continuousWithinAt
  have hM : IntegrableOn (fun t => quadraticOscillationDerivative θ t * H t) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      ((quadraticOscillationDerivative_intervalIntegrable θ a b).mul_continuousOn hHc)
  have hC := progression_prefix_derivative_integrable q r θ ha (b := b)
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t _ => quadraticOscillation_hasDerivAt θ t)
    (fun t ht => hH t (by simpa only [Set.uIcc_of_le hab] using ht))
    (quadraticOscillationDerivative_intervalIntegrable θ a b) hH'
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab] at hi
  have hs : (∫ t in Set.Ioc a b, quadraticOscillationDerivative θ t *
        (progressionMangoldtPrefix q r t - H t)) =
      (∫ t in Set.Ioc a b, quadraticOscillationDerivative θ t * progressionMangoldtPrefix q r t) -
      ∫ t in Set.Ioc a b, quadraticOscillationDerivative θ t * H t := by
    simp_rw [mul_sub]
    exact integral_sub hC hM
  rw [squareResidueSum_abel q r θ ha hab, hi, hs]
  ring

theorem squareResidueSum_model_error_bound (q : ℕ) (r : ZMod q) (θ : ℝ)
    {a b N B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbN : b ≤ N) (hB : 0 ≤ B)
    (H H' : ℝ → ℂ) (hH : ∀ t ∈ Set.Icc a b, HasDerivAt H (H' t) t)
    (hH' : IntervalIntegrable H' volume a b)
    (herror : ∀ t ∈ Set.Icc a b, ‖progressionMangoldtPrefix q r t - H t‖ ≤ B) :
    ‖squareResidueSum (Ioc ⌊a⌋₊ ⌊b⌋₊) q r ArithmeticFunction.vonMangoldt (θ : PrimeCircle) -
        ∫ t in Set.Ioc a b, quadraticOscillation θ t * H' t‖ ≤
      B * (2 + 4 * Real.pi * |θ| * N^2) := by
  rw [squareResidueSum_model_error_identity q r θ ha hab H H' hH hH']
  exact quadratic_prefix_error_bound_square θ ha hab hbN hB
    (fun t => progressionMangoldtPrefix q r t - H t) herror

theorem annularProgressionModel_error_bound {N : ℕ} (hN : 1 ≤ N)
    (q : ℕ) (r : ZMod q) (θ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (H H' : ℝ → ℂ)
    (hH : ∀ t ∈ Set.Icc ((N : ℝ)/2) N, HasDerivAt H (H' t) t)
    (hH' : IntervalIntegrable H' volume ((N : ℝ)/2) N)
    (herror : ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix q r t - H t‖ ≤ (N : ℝ)*δ) :
    ‖Complex.ofReal ((N : ℝ)⁻¹) *
        squareResidueSum (Ioc (N/2) N) q r ArithmeticFunction.vonMangoldt (θ : PrimeCircle) -
      Complex.ofReal ((N : ℝ)⁻¹) *
        ∫ t in Set.Ioc ((N : ℝ)/2) N, quadraticOscillation θ t * H' t‖ ≤
      δ * (2 + 4 * Real.pi * |θ| * (N : ℝ)^2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : ⌊(N : ℝ)/2⌋₊ = N/2 := Nat.floor_div_eq_div N 2
  have hraw := squareResidueSum_model_error_bound q r θ
    (a := (N : ℝ)/2) (b := N) (N := N) (B := (N : ℝ)*δ)
    (by positivity) (by linarith) le_rfl (mul_nonneg hN0.le hδ) H H' hH hH' herror
  simp only [hf, Nat.floor_natCast] at hraw
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hN0.le)]
  calc
    _ ≤ (N : ℝ)⁻¹ * ((N : ℝ)*δ * (2 + 4 * Real.pi * |θ| * (N : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hN0.le)
    _ = ((N : ℝ)⁻¹ * (N : ℝ)) * (δ * (2 + 4 * Real.pi * |θ| * (N : ℝ)^2)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hN0.ne', one_mul]

end PrimeSquares
