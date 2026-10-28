import PrimeSquares.CircleMultipliers
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Topology.ContinuousMap.Bounded.Normed

set_option autoImplicit false
open MeasureTheory
open scoped lp
namespace PrimeSquares

noncomputable abbrev RealLineL2 := MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)

noncomputable def realLineFourier : RealLineL2 ≃ₗᵢ[ℂ] RealLineL2 :=
  MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ

theorem realLineProduct_memLp (m : (BoundedContinuousFunction ℝ ℂ)) (f : RealLineL2) :
    MemLp (fun θ => m θ * f θ) 2 (volume : Measure ℝ) := by
  apply (Lp.memLp f).of_le_mul (c := ‖m‖)
  · exact m.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  · exact Filter.Eventually.of_forall fun θ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (m.norm_coe_le_norm θ) (norm_nonneg _)

noncomputable def realLineMultiplyValue (m : (BoundedContinuousFunction ℝ ℂ))
    (f : RealLineL2) : RealLineL2 :=
  (realLineProduct_memLp m f).toLp (fun θ => m θ * f θ)

theorem realLineMultiplyValue_ae (m : (BoundedContinuousFunction ℝ ℂ)) (f : RealLineL2) :
    realLineMultiplyValue m f =ᵐ[(volume : Measure ℝ)] fun θ => m θ * f θ :=
  MemLp.coeFn_toLp (realLineProduct_memLp m f)

theorem realLineMultiplyValue_norm_le (m : (BoundedContinuousFunction ℝ ℂ)) (f : RealLineL2) :
    ‖realLineMultiplyValue m f‖ ≤ ‖m‖ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [realLineMultiplyValue_ae m f] with θ hθ
  rw [hθ, norm_mul]
  exact mul_le_mul_of_nonneg_right (m.norm_coe_le_norm θ) (norm_nonneg _)

noncomputable def realLineMultiply (m : (BoundedContinuousFunction ℝ ℂ)) :
    RealLineL2 →L[ℂ] RealLineL2 :=
  LinearMap.mkContinuous
    { toFun := realLineMultiplyValue m
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [realLineMultiplyValue_ae m (f+g), realLineMultiplyValue_ae m f,
          realLineMultiplyValue_ae m g, Lp.coeFn_add f g,
          Lp.coeFn_add (realLineMultiplyValue m f) (realLineMultiplyValue m g)] with θ hfg hf hg ha hb
        simp only [Pi.add_apply] at ha hb
        rw [hfg, hb, hf, hg, ha, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [realLineMultiplyValue_ae m (c • f), realLineMultiplyValue_ae m f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (realLineMultiplyValue m f)] with θ hcf hf ha hb
        simp only [Pi.smul_apply, smul_eq_mul] at ha hb
        change realLineMultiplyValue m (c • f) θ = (c • realLineMultiplyValue m f) θ
        rw [hcf, hb, ha, hf]
        ring }
    ‖m‖ (fun f => by
      change ‖realLineMultiplyValue m f‖ ≤ ‖m‖ * ‖f‖
      exact realLineMultiplyValue_norm_le m f)

theorem realLineMultiply_ae (m : (BoundedContinuousFunction ℝ ℂ)) (f : RealLineL2) :
    realLineMultiply m f =ᵐ[(volume : Measure ℝ)] fun θ => m θ * f θ :=
  realLineMultiplyValue_ae m f

theorem realLineMultiply_norm_le (m : (BoundedContinuousFunction ℝ ℂ)) (f : RealLineL2) :
    ‖realLineMultiply m f‖ ≤ ‖m‖ * ‖f‖ := realLineMultiplyValue_norm_le m f

theorem realLineMultiply_opNorm_le (m : (BoundedContinuousFunction ℝ ℂ)) :
    ‖realLineMultiply m‖ ≤ ‖m‖ :=
  (realLineMultiply m).opNorm_le_bound (norm_nonneg m) (realLineMultiply_norm_le m)

theorem realLineMultiply_opNorm_le_of_bound (m : (BoundedContinuousFunction ℝ ℂ))
    {B : ℝ} (hB : 0 ≤ B) (hm : ∀ θ, ‖m θ‖ ≤ B) : ‖realLineMultiply m‖ ≤ B := by
  apply (realLineMultiply m).opNorm_le_bound hB
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [realLineMultiply_ae m f] with θ hθ
  rw [hθ, norm_mul]
  exact mul_le_mul_of_nonneg_right (hm θ) (norm_nonneg _)

noncomputable def realLineMultiplier (m : BoundedContinuousFunction ℝ ℂ) : RealLineL2 →L[ℂ] RealLineL2 :=
  realLineFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((realLineMultiply m).comp realLineFourier.toContinuousLinearEquiv.toContinuousLinearMap)

theorem realLineMultiplier_apply (m : BoundedContinuousFunction ℝ ℂ) (f : RealLineL2) :
    realLineMultiplier m f=realLineFourier.symm (realLineMultiply m (realLineFourier f)) := rfl

theorem realLineFourier_multiplier (m : BoundedContinuousFunction ℝ ℂ) (f : RealLineL2) :
    realLineFourier (realLineMultiplier m f)=realLineMultiply m (realLineFourier f) :=
  realLineFourier.apply_symm_apply _

theorem realLineMultiplier_norm_le (m : BoundedContinuousFunction ℝ ℂ) (f : RealLineL2) :
    ‖realLineMultiplier m f‖≤‖m‖*‖f‖ := by
  rw [realLineMultiplier_apply,realLineFourier.symm.norm_map]
  exact (realLineMultiply_norm_le m (realLineFourier f)).trans_eq
    (by rw [realLineFourier.norm_map])

theorem realLineMultiplier_opNorm_le (m : BoundedContinuousFunction ℝ ℂ) : ‖realLineMultiplier m‖≤‖m‖ :=
  (realLineMultiplier m).opNorm_le_bound (norm_nonneg _) (realLineMultiplier_norm_le m)

theorem realLineMultiplier_opNorm_le_of_bound (m : BoundedContinuousFunction ℝ ℂ)
    {K : ℝ} (hK : 0≤K) (hm : ∀ x,‖m x‖≤K) : ‖realLineMultiplier m‖≤K := by
  apply (realLineMultiplier m).opNorm_le_bound hK
  intro f
  rw [realLineMultiplier_apply,realLineFourier.symm.norm_map]
  have h := (realLineMultiply m).le_opNorm (realLineFourier f)
  exact h.trans ((mul_le_mul_of_nonneg_right (realLineMultiply_opNorm_le_of_bound m hK hm)
    (norm_nonneg _)).trans_eq (by rw [realLineFourier.norm_map]))

/-- An actual Lp assertion on the dense L2 intersection. Membership is explicit,
so a totalized real norm outside its domain cannot imply a false estimate. -/
def RealLpMultiplierBound (p : ENNReal) (m : BoundedContinuousFunction ℝ ℂ) (K : ℝ) : Prop :=
  ∀ f : RealLineL2,MemLp (f : ℝ → ℂ) p volume →
    MemLp (realLineMultiplier m f : ℝ → ℂ) p volume ∧
      eLpNorm (realLineMultiplier m f : ℝ → ℂ) p volume≤ENNReal.ofReal K*eLpNorm (f : ℝ → ℂ) p volume

/-- The same actual-space assertion for the existing negative-phase integer
Fourier realization. This is a property, not a new analytic axiom. -/
def IntegerLpMultiplierBound (p : ENNReal) (m : C(PrimeCircle,ℂ)) (K : ℝ) : Prop :=
  ∀ f : ℓ²(ℤ,ℂ),MemLp (f : ℤ → ℂ) p Measure.count →
    MemLp (integerMultiplier m f : ℤ → ℂ) p Measure.count ∧
      eLpNorm (integerMultiplier m f : ℤ → ℂ) p Measure.count≤
        ENNReal.ofReal K*eLpNorm (f : ℤ → ℂ) p Measure.count

theorem realLpMultiplierBound_mono {p : ENNReal} {m : BoundedContinuousFunction ℝ ℂ} {K L : ℝ}
    (H : RealLpMultiplierBound p m K) (hKL : K≤L) : RealLpMultiplierBound p m L := by
  intro f hf
  obtain ⟨hm,hn⟩ := H f hf
  exact ⟨hm,hn.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hKL) _)⟩

theorem integerLpMultiplierBound_mono {p : ENNReal} {m : C(PrimeCircle,ℂ)} {K L : ℝ}
    (H : IntegerLpMultiplierBound p m K) (hKL : K≤L) : IntegerLpMultiplierBound p m L := by
  intro f hf
  obtain ⟨hm,hn⟩ := H f hf
  exact ⟨hm,hn.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hKL) _)⟩

end PrimeSquares
