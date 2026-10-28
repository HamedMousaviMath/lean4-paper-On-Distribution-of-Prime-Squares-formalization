import PrimeSquares.RealLineFourierMultipliers
import PrimeSquares.RealFourierDilation

set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform ENNReal
namespace PrimeSquares

/-- An arbitrary essentially bounded measurable real multiplier, without any
continuity, differentiability or pointwise support requirement. -/
structure AEBoundedRealSymbol (B : ℝ) where
  value : ℝ → ℂ
  measurable : AEStronglyMeasurable value volume
  norm_bound : ∀ᵐ θ ∂volume, ‖value θ‖ ≤ B

theorem aeRealProduct_memLp {B : ℝ} (m : AEBoundedRealSymbol B) (f : RealLineL2) :
    MemLp (fun θ => m.value θ*f θ) 2 volume := by
  apply (Lp.memLp f).of_le_mul (c := B)
  · exact m.measurable.mul (Lp.aestronglyMeasurable f)
  · filter_upwards [m.norm_bound] with θ hm
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hm (norm_nonneg _)

noncomputable def aeRealMultiplyValue {B : ℝ} (m : AEBoundedRealSymbol B)
    (f : RealLineL2) : RealLineL2 :=
  (aeRealProduct_memLp m f).toLp (fun θ => m.value θ*f θ)

theorem aeRealMultiplyValue_ae {B : ℝ} (m : AEBoundedRealSymbol B) (f : RealLineL2) :
    aeRealMultiplyValue m f =ᵐ[volume] fun θ => m.value θ*f θ :=
  MemLp.coeFn_toLp (aeRealProduct_memLp m f)

theorem aeRealMultiplyValue_norm_le {B : ℝ} (m : AEBoundedRealSymbol B) (f : RealLineL2) :
    ‖aeRealMultiplyValue m f‖ ≤ B*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [aeRealMultiplyValue_ae m f,m.norm_bound] with θ hf hm
  rw [hf,norm_mul]
  exact mul_le_mul_of_nonneg_right hm (norm_nonneg _)

noncomputable def aeRealMultiply {B : ℝ} (m : AEBoundedRealSymbol B) :
    RealLineL2 →L[ℂ] RealLineL2 :=
  LinearMap.mkContinuous
    { toFun := aeRealMultiplyValue m
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [aeRealMultiplyValue_ae m (f+g),aeRealMultiplyValue_ae m f,
          aeRealMultiplyValue_ae m g,Lp.coeFn_add f g,
          Lp.coeFn_add (aeRealMultiplyValue m f) (aeRealMultiplyValue m g)] with θ hfg hf hg ha hb
        simp only [Pi.add_apply] at ha hb
        rw [hfg,hb,hf,hg,ha,mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [aeRealMultiplyValue_ae m (c • f),aeRealMultiplyValue_ae m f,
          Lp.coeFn_smul c f,Lp.coeFn_smul c (aeRealMultiplyValue m f)] with θ hcf hf ha hb
        simp only [Pi.smul_apply,smul_eq_mul] at ha hb
        change aeRealMultiplyValue m (c • f) θ = (c • aeRealMultiplyValue m f) θ
        rw [hcf,hb,ha,hf]
        ring }
    B (fun f => aeRealMultiplyValue_norm_le m f)

theorem aeRealMultiply_ae {B : ℝ} (m : AEBoundedRealSymbol B) (f : RealLineL2) :
    aeRealMultiply m f =ᵐ[volume] fun θ => m.value θ*f θ := aeRealMultiplyValue_ae m f

noncomputable def aeRealLineMultiplier {B : ℝ} (m : AEBoundedRealSymbol B) :
    RealLineL2 →L[ℂ] RealLineL2 :=
  realLineFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((aeRealMultiply m).comp realLineFourier.toContinuousLinearEquiv.toContinuousLinearMap)

theorem realLineFourier_aeMultiplier {B : ℝ} (m : AEBoundedRealSymbol B) (f : RealLineL2) :
    realLineFourier (aeRealLineMultiplier m f) = aeRealMultiply m (realLineFourier f) :=
  realLineFourier.apply_symm_apply _

theorem aeRealLineMultiplier_norm_le {B : ℝ} (m : AEBoundedRealSymbol B) (f : RealLineL2) :
    ‖aeRealLineMultiplier m f‖ ≤ B*‖f‖ := by
  change ‖realLineFourier.symm (aeRealMultiply m (realLineFourier f))‖ ≤ _
  rw [realLineFourier.symm.norm_map]
  change ‖aeRealMultiplyValue m (realLineFourier f)‖ ≤ _
  simpa only [realLineFourier.norm_map] using aeRealMultiplyValue_norm_le m (realLineFourier f)

noncomputable def aeRealSymbol_smul {B : ℝ} (c : ℂ) (m : AEBoundedRealSymbol B) :
    AEBoundedRealSymbol (‖c‖*B) where
  value := fun θ => c*m.value θ
  measurable := m.measurable.const_smul c
  norm_bound := by
    filter_upwards [m.norm_bound] with θ hm
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hm (norm_nonneg _)

theorem aeRealLineMultiplier_smul {B : ℝ} (c : ℂ) (m : AEBoundedRealSymbol B) :
    aeRealLineMultiplier (aeRealSymbol_smul c m) = c • aeRealLineMultiplier m := by
  apply ContinuousLinearMap.ext
  intro f
  apply realLineFourier.injective
  rw [_root_.smul_apply,map_smul,realLineFourier_aeMultiplier,
    realLineFourier_aeMultiplier]
  apply Lp.ext
  filter_upwards [aeRealMultiply_ae (aeRealSymbol_smul c m) (realLineFourier f),
    aeRealMultiply_ae m (realLineFourier f),Lp.coeFn_smul c (aeRealMultiply m (realLineFourier f))]
    with θ hm hn hs
  simp only [Pi.smul_apply,smul_eq_mul] at hs
  rw [hm,hs,hn]
  change (c*m.value θ)*realLineFourier f θ = c*(m.value θ*realLineFourier f θ)
  ring

/-- A full Lp operator realizing the given rough multiplier on the actual
L2 intersection. Its norm is the ordinary full Lp operator norm. -/
structure FullRealLpMultiplier {B : ℝ} (m : AEBoundedRealSymbol B)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] where
  map : Lp ℂ p (volume : Measure ℝ) →L[ℂ] Lp ℂ p (volume : Measure ℝ)
  agreement : ∀ f : RealLineL2, ∀ hf : MemLp (f : ℝ → ℂ) p volume,
    map (hf.toLp (f : ℝ → ℂ)) =ᵐ[volume] (aeRealLineMultiplier m f : ℝ → ℂ)

noncomputable def FullRealLpMultiplier.smul {B : ℝ} {m : AEBoundedRealSymbol B}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (A : FullRealLpMultiplier m p) (c : ℂ) :
    FullRealLpMultiplier (aeRealSymbol_smul c m) p where
  map := c • A.map
  agreement := by
    intro f hf
    rw [_root_.smul_apply,aeRealLineMultiplier_smul,_root_.smul_apply]
    filter_upwards [Lp.coeFn_smul c (A.map (hf.toLp (f : ℝ → ℂ))),A.agreement f hf,
      Lp.coeFn_smul c (aeRealLineMultiplier m f)] with θ h₁ h₂ h₃
    simp only [Pi.smul_apply,smul_eq_mul] at h₁ h₃
    rw [h₁,h₂,h₃]

theorem aeRealSymbol_smul_inverse_kernel {B : ℝ} (c : ℂ)
    (m : AEBoundedRealSymbol B) (x : ℝ) :
    𝓕⁻ (aeRealSymbol_smul c m).value x = c*𝓕⁻ m.value x :=
  real_inverse_fourier_const_mul c m.value x

end PrimeSquares
