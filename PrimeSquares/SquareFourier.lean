import PrimeSquares.CircleMultipliers
import PrimeSquares.PrimeSquareAverages

/-!
# Exact Fourier symbols of the actual square averages

Translations and finite weighted square averages are identified with their
negative-phase multipliers on every integer l2 input. Both full and annular
von Mangoldt symbols retain all prime powers and the exact normalization.
-/

open Finset MeasureTheory
open scoped lp

namespace PrimeSquares

theorem integerTranslate_single {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    (d n : ℤ) (z : ℂ) :
    integerTranslate hp d (lp.single P n z) = lp.single P (n+d) z := by
  apply lp.ext
  funext x
  simp only [integerTranslate_apply, lp.single_apply, Pi.single_apply, sub_eq_iff_eq_add]

theorem circleMultiply_negativeCharacter (d n : ℤ) :
    circleMultiply (negativeFourierCharacter d) (fourierLp (T := (1 : ℝ)) 2 (-n)) =
      fourierLp (T := (1 : ℝ)) 2 (-(n+d)) := by
  change circleMultiply (negativeFourierCharacter d)
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (negativeFourierCharacter n)) =
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (negativeFourierCharacter (n+d))
  rw [circleMultiply_toLp]
  congr 1
  apply ContinuousMap.ext
  intro θ
  change negativeFourierCharacter d θ * negativeFourierCharacter n θ =
    negativeFourierCharacter (n+d) θ
  rw [add_comm n d, negativeFourierCharacter_add]

theorem integerTranslate_l2_multiplier (d : ℤ) :
    integerTranslate (P := 2) (by norm_num) d =
      integerMultiplier (negativeFourierCharacter d) := by
  apply lp.ext_continuousLinearMap (by norm_num)
  intro n
  apply ContinuousLinearMap.ext
  intro z
  change integerTranslate (P := 2) (by norm_num) d (lp.single 2 n z) =
    integerMultiplier (negativeFourierCharacter d) (lp.single 2 n z)
  apply integerFourier.injective
  rw [integerTranslate_single, integerFourier_multiplier, integerFourier_single,
    integerFourier_single, map_smul, circleMultiply_negativeCharacter]

theorem integerFourier_translate (d : ℤ) (f : ℓ²(ℤ, ℂ)) :
    integerFourier (integerTranslate (P := 2) (by norm_num) d f) =
      circleMultiply (negativeFourierCharacter d) (integerFourier f) := by
  rw [integerTranslate_l2_multiplier, integerFourier_multiplier]

theorem integerFourier_translate_ae (d : ℤ) (f : ℓ²(ℤ, ℂ)) :
    integerFourier (integerTranslate (P := 2) (by norm_num) d f)
      =ᵐ[AddCircle.haarAddCircle] fun θ =>
        negativeFourierCharacter d θ * integerFourier f θ := by
  rw [integerFourier_translate]
  exact circleMultiply_ae _ _

noncomputable def finiteSquareSymbol (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) :
    C(PrimeCircle, ℂ) :=
  (c : ℂ) • ∑ n ∈ S, (w n : ℂ) • negativeFourierCharacter ((n : ℤ)^2)

theorem finiteSquareSymbol_apply (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) (θ : PrimeCircle) :
    finiteSquareSymbol S c w θ =
      (c : ℂ) * ∑ n ∈ S, (w n : ℂ) * negativeFourierCharacter ((n : ℤ)^2) θ := by
  simp only [finiteSquareSymbol, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]

theorem finiteSquareSymbol_real (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) (θ : ℝ) :
    finiteSquareSymbol S c w (θ : PrimeCircle) = (c : ℂ) *
      ∑ n ∈ S, (w n : ℂ) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ)^2) * (θ : ℂ))) := by
  simp only [finiteSquareSymbol_apply, negativeFourierCharacter_real, Int.cast_pow,
    Int.cast_natCast]

theorem finiteSquareOperator_l2_multiplier (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) :
    finiteSquareOperator (P := 2) (by norm_num) S c w =
      integerMultiplier (finiteSquareSymbol S c w) := by
  classical
  have hsum : integerMultiplier
      (∑ n ∈ S, (w n : ℂ) • negativeFourierCharacter ((n : ℤ)^2)) =
      ∑ n ∈ S, (w n : ℂ) • integerMultiplier (negativeFourierCharacter ((n : ℤ)^2)) := by
    induction S using Finset.induction_on with
    | empty =>
        simp only [sum_empty]
        exact integerMultiplier_zero
    | @insert n S hn ih =>
        rw [sum_insert hn, sum_insert hn, integerMultiplier_add, integerMultiplier_smul, ih]
  rw [finiteSquareOperator, finiteSquareSymbol, integerMultiplier_smul, hsum]
  simp only [integerTranslate_l2_multiplier]

theorem integerFourier_finiteSquareOperator (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ)
    (f : ℓ²(ℤ, ℂ)) :
    integerFourier (finiteSquareOperator (P := 2) (by norm_num) S c w f) =
      circleMultiply (finiteSquareSymbol S c w) (integerFourier f) := by
  rw [finiteSquareOperator_l2_multiplier, integerFourier_multiplier]

theorem integerFourier_finiteSquareOperator_ae (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ)
    (f : ℓ²(ℤ, ℂ)) :
    integerFourier (finiteSquareOperator (P := 2) (by norm_num) S c w f)
      =ᵐ[AddCircle.haarAddCircle] fun θ =>
        finiteSquareSymbol S c w θ * integerFourier f θ := by
  rw [integerFourier_finiteSquareOperator]
  exact circleMultiply_ae _ _

noncomputable def weightedSquareAverageSymbol (N : ℕ) (w : ℕ → ℝ) :
    C(PrimeCircle, ℂ) := finiteSquareSymbol (Ioc 0 N) (N : ℝ)⁻¹ w

noncomputable def annularWeightedSquareAverageSymbol (N : ℕ) (w : ℕ → ℝ) :
    C(PrimeCircle, ℂ) := finiteSquareSymbol (Ioc (N/2) N) (N : ℝ)⁻¹ w

theorem weightedSquareAverage_l2_multiplier (N : ℕ) (w : ℕ → ℝ) :
    weightedSquareAverage (P := 2) (by norm_num) N w =
      integerMultiplier (weightedSquareAverageSymbol N w) :=
  finiteSquareOperator_l2_multiplier _ _ _

theorem annularWeightedSquareAverage_l2_multiplier (N : ℕ) (w : ℕ → ℝ) :
    annularWeightedSquareAverage (P := 2) (by norm_num) N w =
      integerMultiplier (annularWeightedSquareAverageSymbol N w) :=
  finiteSquareOperator_l2_multiplier _ _ _

theorem mangoldtSquareAverageSymbol_real (N : ℕ) (θ : ℝ) :
    weightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (θ : PrimeCircle) =
      Complex.ofReal ((N : ℝ)⁻¹) * ∑ n ∈ Ioc 0 N,
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ)^2) * (θ : ℂ))) :=
  finiteSquareSymbol_real _ _ _ _

theorem annularMangoldtSquareAverageSymbol_real (N : ℕ) (θ : ℝ) :
    annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (θ : PrimeCircle) =
      Complex.ofReal ((N : ℝ)⁻¹) * ∑ n ∈ Ioc (N/2) N,
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ)^2) * (θ : ℂ))) :=
  finiteSquareSymbol_real _ _ _ _

theorem finiteSquareOperator_fourier_error_bound (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ)
    (m : C(PrimeCircle, ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (herror : ∀ θ, ‖finiteSquareSymbol S c w θ - m θ‖ ≤ B) :
    ‖finiteSquareOperator (P := 2) (by norm_num) S c w - integerMultiplier m‖ ≤ B := by
  rw [finiteSquareOperator_l2_multiplier]
  exact integerMultiplier_error_bound _ _ hB herror

theorem annularWeightedSquareAverage_fourier_error_bound (N : ℕ) (w : ℕ → ℝ)
    (m : C(PrimeCircle, ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (herror : ∀ θ, ‖annularWeightedSquareAverageSymbol N w θ - m θ‖ ≤ B) :
    ‖annularWeightedSquareAverage (P := 2) (by norm_num) N w - integerMultiplier m‖ ≤ B :=
  finiteSquareOperator_fourier_error_bound _ _ _ m hB herror

end PrimeSquares
