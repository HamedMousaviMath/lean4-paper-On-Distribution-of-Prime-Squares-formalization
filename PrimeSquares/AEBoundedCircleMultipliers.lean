import PrimeSquares.CircleMultipliers

set_option autoImplicit false
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares

/-- A measurable representative of a circle symbol with an almost everywhere bound. -/
structure AEBoundedCircleSymbol (B : ℝ) where
  value : PrimeCircle → ℂ
  measurable : AEStronglyMeasurable value AddCircle.haarAddCircle
  norm_bound : ∀ᵐ θ ∂AddCircle.haarAddCircle,‖value θ‖≤B

theorem aeCircleProduct_memLp {B : ℝ} (m : AEBoundedCircleSymbol B) (f : PrimeCircleL2) :
    MemLp (fun θ => m.value θ * f θ) 2 AddCircle.haarAddCircle := by
  apply (Lp.memLp f).of_le_mul (c := B)
  · exact m.measurable.mul (Lp.aestronglyMeasurable f)
  · filter_upwards [m.norm_bound] with θ hm
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hm (norm_nonneg _)

noncomputable def aeCircleMultiplyValue {B : ℝ} (m : AEBoundedCircleSymbol B)
    (f : PrimeCircleL2) : PrimeCircleL2 :=
  (aeCircleProduct_memLp m f).toLp (fun θ => m.value θ * f θ)

theorem aeCircleMultiplyValue_ae {B : ℝ} (m : AEBoundedCircleSymbol B) (f : PrimeCircleL2) :
    aeCircleMultiplyValue m f =ᵐ[AddCircle.haarAddCircle] fun θ => m.value θ * f θ :=
  MemLp.coeFn_toLp (aeCircleProduct_memLp m f)

theorem aeCircleMultiplyValue_norm_le {B : ℝ} (m : AEBoundedCircleSymbol B) (f : PrimeCircleL2) :
    ‖aeCircleMultiplyValue m f‖ ≤ B * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [aeCircleMultiplyValue_ae m f,m.norm_bound] with θ hθ hm
  rw [hθ, norm_mul]
  exact mul_le_mul_of_nonneg_right hm (norm_nonneg _)

noncomputable def aeCircleMultiply {B : ℝ} (m : AEBoundedCircleSymbol B) :
    PrimeCircleL2 →L[ℂ] PrimeCircleL2 :=
  LinearMap.mkContinuous
    { toFun := aeCircleMultiplyValue m
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [aeCircleMultiplyValue_ae m (f+g), aeCircleMultiplyValue_ae m f,
          aeCircleMultiplyValue_ae m g, Lp.coeFn_add f g,
          Lp.coeFn_add (aeCircleMultiplyValue m f) (aeCircleMultiplyValue m g)] with θ hfg hf hg ha hb
        simp only [Pi.add_apply] at ha hb
        rw [hfg, hb, hf, hg, ha, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [aeCircleMultiplyValue_ae m (c • f), aeCircleMultiplyValue_ae m f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (aeCircleMultiplyValue m f)] with θ hcf hf ha hb
        simp only [Pi.smul_apply, smul_eq_mul] at ha hb
        change aeCircleMultiplyValue m (c • f) θ = (c • aeCircleMultiplyValue m f) θ
        rw [hcf, hb, ha, hf]
        ring }
    B (fun f => by
      change ‖aeCircleMultiplyValue m f‖ ≤ B * ‖f‖
      exact aeCircleMultiplyValue_norm_le m f)

theorem aeCircleMultiply_ae {B : ℝ} (m : AEBoundedCircleSymbol B) (f : PrimeCircleL2) :
    aeCircleMultiply m f =ᵐ[AddCircle.haarAddCircle] fun θ => m.value θ * f θ :=
  aeCircleMultiplyValue_ae m f

theorem aeCircleMultiply_norm_le {B : ℝ} (m : AEBoundedCircleSymbol B) (f : PrimeCircleL2) :
    ‖aeCircleMultiply m f‖ ≤ B * ‖f‖ := aeCircleMultiplyValue_norm_le m f

theorem aeCircleMultiply_opNorm_le {B : ℝ} (hB : 0≤B) (m : AEBoundedCircleSymbol B) :
    ‖aeCircleMultiply m‖≤B :=
  (aeCircleMultiply m).opNorm_le_bound hB (aeCircleMultiply_norm_le m)

noncomputable def aeIntegerMultiplier {B : ℝ} (m : AEBoundedCircleSymbol B) :
    ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ) :=
  integerFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((aeCircleMultiply m).comp integerFourier.toContinuousLinearEquiv.toContinuousLinearMap)

theorem aeIntegerMultiplier_apply {B : ℝ} (m : AEBoundedCircleSymbol B) (f : ℓ²(ℤ,ℂ)) :
    aeIntegerMultiplier m f=integerFourier.symm (aeCircleMultiply m (integerFourier f)) := rfl

theorem integerFourier_aeMultiplier {B : ℝ} (m : AEBoundedCircleSymbol B) (f : ℓ²(ℤ,ℂ)) :
    integerFourier (aeIntegerMultiplier m f)=aeCircleMultiply m (integerFourier f) :=
  integerFourier.apply_symm_apply _

theorem aeIntegerMultiplier_norm_le {B : ℝ} (m : AEBoundedCircleSymbol B) (f : ℓ²(ℤ,ℂ)) :
    ‖aeIntegerMultiplier m f‖≤B*‖f‖ := by
  rw [aeIntegerMultiplier_apply,integerFourier.symm.norm_map]
  simpa only [integerFourier_norm] using aeCircleMultiply_norm_le m (integerFourier f)

theorem aeIntegerMultiplier_opNorm_le {B : ℝ} (hB : 0≤B) (m : AEBoundedCircleSymbol B) :
    ‖aeIntegerMultiplier m‖≤B :=
  (aeIntegerMultiplier m).opNorm_le_bound hB (aeIntegerMultiplier_norm_le m)

/-- Only equality after multiplication by the outer symbol is needed. -/
theorem aeIntegerMultiplier_localized_comp {B D : ℝ} (m : AEBoundedCircleSymbol B)
    (n : AEBoundedCircleSymbol D) (a : C(PrimeCircle,ℂ))
    (he : ∀ᵐ θ ∂AddCircle.haarAddCircle,a θ*m.value θ=a θ*n.value θ) :
    (integerMultiplier a).comp (aeIntegerMultiplier m)=
      (integerMultiplier a).comp (aeIntegerMultiplier n) := by
  apply ContinuousLinearMap.ext
  intro f
  apply integerFourier.injective
  simp only [ContinuousLinearMap.comp_apply,integerFourier_multiplier]
  apply Lp.ext
  filter_upwards [circleMultiply_ae a (integerFourier (aeIntegerMultiplier m f)),
    circleMultiply_ae a (integerFourier (aeIntegerMultiplier n f)),
    aeCircleMultiply_ae m (integerFourier f),aeCircleMultiply_ae n (integerFourier f),he] with θ hm hn hmf hnf hθ
  rw [integerFourier_aeMultiplier] at hm hn
  rw [integerFourier_aeMultiplier,integerFourier_aeMultiplier,hm,hn,hmf,hnf,←mul_assoc,←mul_assoc,hθ]

end PrimeSquares
