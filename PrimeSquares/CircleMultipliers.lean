import PrimeSquares.CircleFourier

/-!
# Actual L2 multiplier operators

Continuous circle symbols multiply arbitrary circle L2 classes. Conjugating
by the negative-phase integer Fourier isometry gives actual bounded integer
l2 operators. Uniform symbol bounds imply operator bounds on all inputs.
-/

open Finset MeasureTheory
open scoped lp

namespace PrimeSquares

theorem circleProduct_memLp (m : C(PrimeCircle, ℂ)) (f : PrimeCircleL2) :
    MemLp (fun θ => m θ * f θ) 2 AddCircle.haarAddCircle := by
  apply (Lp.memLp f).of_le_mul (c := ‖m‖)
  · exact m.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  · exact Filter.Eventually.of_forall fun θ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (m.norm_coe_le_norm θ) (norm_nonneg _)

noncomputable def circleMultiplyValue (m : C(PrimeCircle, ℂ))
    (f : PrimeCircleL2) : PrimeCircleL2 :=
  (circleProduct_memLp m f).toLp (fun θ => m θ * f θ)

theorem circleMultiplyValue_ae (m : C(PrimeCircle, ℂ)) (f : PrimeCircleL2) :
    circleMultiplyValue m f =ᵐ[AddCircle.haarAddCircle] fun θ => m θ * f θ :=
  MemLp.coeFn_toLp (circleProduct_memLp m f)

theorem circleMultiplyValue_norm_le (m : C(PrimeCircle, ℂ)) (f : PrimeCircleL2) :
    ‖circleMultiplyValue m f‖ ≤ ‖m‖ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [circleMultiplyValue_ae m f] with θ hθ
  rw [hθ, norm_mul]
  exact mul_le_mul_of_nonneg_right (m.norm_coe_le_norm θ) (norm_nonneg _)

noncomputable def circleMultiply (m : C(PrimeCircle, ℂ)) :
    PrimeCircleL2 →L[ℂ] PrimeCircleL2 :=
  LinearMap.mkContinuous
    { toFun := circleMultiplyValue m
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [circleMultiplyValue_ae m (f+g), circleMultiplyValue_ae m f,
          circleMultiplyValue_ae m g, Lp.coeFn_add f g,
          Lp.coeFn_add (circleMultiplyValue m f) (circleMultiplyValue m g)] with θ hfg hf hg ha hb
        simp only [Pi.add_apply] at ha hb
        rw [hfg, hb, hf, hg, ha, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [circleMultiplyValue_ae m (c • f), circleMultiplyValue_ae m f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (circleMultiplyValue m f)] with θ hcf hf ha hb
        simp only [Pi.smul_apply, smul_eq_mul] at ha hb
        change circleMultiplyValue m (c • f) θ = (c • circleMultiplyValue m f) θ
        rw [hcf, hb, ha, hf]
        ring }
    ‖m‖ (fun f => by
      change ‖circleMultiplyValue m f‖ ≤ ‖m‖ * ‖f‖
      exact circleMultiplyValue_norm_le m f)

theorem circleMultiply_ae (m : C(PrimeCircle, ℂ)) (f : PrimeCircleL2) :
    circleMultiply m f =ᵐ[AddCircle.haarAddCircle] fun θ => m θ * f θ :=
  circleMultiplyValue_ae m f

theorem circleMultiply_norm_le (m : C(PrimeCircle, ℂ)) (f : PrimeCircleL2) :
    ‖circleMultiply m f‖ ≤ ‖m‖ * ‖f‖ := circleMultiplyValue_norm_le m f

theorem circleMultiply_opNorm_le (m : C(PrimeCircle, ℂ)) :
    ‖circleMultiply m‖ ≤ ‖m‖ :=
  (circleMultiply m).opNorm_le_bound (norm_nonneg m) (circleMultiply_norm_le m)

theorem circleMultiply_opNorm_le_of_bound (m : C(PrimeCircle, ℂ))
    {B : ℝ} (hB : 0 ≤ B) (hm : ∀ θ, ‖m θ‖ ≤ B) : ‖circleMultiply m‖ ≤ B := by
  apply (circleMultiply m).opNorm_le_bound hB
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [circleMultiply_ae m f] with θ hθ
  rw [hθ, norm_mul]
  exact mul_le_mul_of_nonneg_right (hm θ) (norm_nonneg _)

theorem circleMultiply_toLp (m g : C(PrimeCircle, ℂ)) :
    circleMultiply m (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ g) =
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (m*g) := by
  apply Lp.ext
  filter_upwards [circleMultiply_ae m (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ g),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle g,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle (m*g)] with θ hm hg hmg
  rw [hm, hg, hmg]
  rfl

theorem circleMultiply_add (m n : C(PrimeCircle, ℂ)) :
    circleMultiply (m+n) = circleMultiply m + circleMultiply n := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [circleMultiply_ae (m+n) f, circleMultiply_ae m f, circleMultiply_ae n f,
    Lp.coeFn_add (circleMultiply m f) (circleMultiply n f)] with θ hmn hm hn ha
  simp only [Pi.add_apply] at ha
  change circleMultiply (m+n) f θ = (circleMultiply m f + circleMultiply n f) θ
  rw [hmn, ha, hm, hn]
  exact add_mul _ _ _

theorem circleMultiply_smul (c : ℂ) (m : C(PrimeCircle, ℂ)) :
    circleMultiply (c • m) = c • circleMultiply m := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [circleMultiply_ae (c • m) f, circleMultiply_ae m f,
    Lp.coeFn_smul c (circleMultiply m f)] with θ hcm hm hs
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  change circleMultiply (c • m) f θ = (c • circleMultiply m f) θ
  rw [hcm, hs, hm]
  change (c * m θ) * f θ = c * (m θ * f θ)
  ring

noncomputable def integerMultiplier (m : C(PrimeCircle, ℂ)) :
    ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) :=
  integerFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((circleMultiply m).comp integerFourier.toContinuousLinearEquiv.toContinuousLinearMap)

theorem integerMultiplier_apply (m : C(PrimeCircle, ℂ)) (f : ℓ²(ℤ, ℂ)) :
    integerMultiplier m f = integerFourier.symm (circleMultiply m (integerFourier f)) := rfl

theorem integerFourier_multiplier (m : C(PrimeCircle, ℂ)) (f : ℓ²(ℤ, ℂ)) :
    integerFourier (integerMultiplier m f) = circleMultiply m (integerFourier f) :=
  integerFourier.apply_symm_apply _

theorem integerMultiplier_norm_le (m : C(PrimeCircle, ℂ)) (f : ℓ²(ℤ, ℂ)) :
    ‖integerMultiplier m f‖ ≤ ‖m‖ * ‖f‖ := by
  rw [integerMultiplier_apply, integerFourier.symm.norm_map]
  simpa only [integerFourier_norm] using circleMultiply_norm_le m (integerFourier f)

theorem integerMultiplier_opNorm_le (m : C(PrimeCircle, ℂ)) :
    ‖integerMultiplier m‖ ≤ ‖m‖ :=
  (integerMultiplier m).opNorm_le_bound (norm_nonneg m) (integerMultiplier_norm_le m)

theorem integerMultiplier_opNorm_le_of_bound (m : C(PrimeCircle, ℂ))
    {B : ℝ} (hB : 0 ≤ B) (hm : ∀ θ, ‖m θ‖ ≤ B) : ‖integerMultiplier m‖ ≤ B := by
  apply (integerMultiplier m).opNorm_le_bound hB
  intro f
  rw [integerMultiplier_apply, integerFourier.symm.norm_map]
  calc
    _ ≤ ‖circleMultiply m‖ * ‖integerFourier f‖ := (circleMultiply m).le_opNorm _
    _ ≤ B * ‖integerFourier f‖ := mul_le_mul_of_nonneg_right
      (circleMultiply_opNorm_le_of_bound m hB hm) (norm_nonneg _)
    _ = _ := by rw [integerFourier_norm]

theorem integerMultiplier_add (m n : C(PrimeCircle, ℂ)) :
    integerMultiplier (m+n) = integerMultiplier m + integerMultiplier n := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [integerMultiplier_apply, circleMultiply_add, _root_.add_apply, map_add]

theorem integerMultiplier_smul (c : ℂ) (m : C(PrimeCircle, ℂ)) :
    integerMultiplier (c • m) = c • integerMultiplier m := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [integerMultiplier_apply, circleMultiply_smul, _root_.smul_apply, map_smul]

theorem integerMultiplier_zero :
    integerMultiplier (0 : C(PrimeCircle, ℂ)) = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa only [norm_zero] using
    integerMultiplier_opNorm_le (0 : C(PrimeCircle, ℂ))) (norm_nonneg _)

theorem integerMultiplier_neg (m : C(PrimeCircle, ℂ)) :
    integerMultiplier (-m) = -integerMultiplier m := by
  simpa only [neg_one_smul ℂ m, neg_one_smul ℂ (integerMultiplier m)] using
    integerMultiplier_smul (-1) m

theorem integerMultiplier_sub (m n : C(PrimeCircle, ℂ)) :
    integerMultiplier (m-n) = integerMultiplier m - integerMultiplier n := by
  rw [sub_eq_add_neg, integerMultiplier_add, integerMultiplier_neg, sub_eq_add_neg]

theorem integerMultiplier_error_bound (m n : C(PrimeCircle, ℂ))
    {B : ℝ} (hB : 0 ≤ B) (hmn : ∀ θ, ‖m θ - n θ‖ ≤ B) :
    ‖integerMultiplier m - integerMultiplier n‖ ≤ B := by
  rw [← integerMultiplier_sub]
  exact integerMultiplier_opNorm_le_of_bound (m-n) hB hmn

end PrimeSquares
