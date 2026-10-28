import PrimeSquares.RealAnnularConvolution
import PrimeSquares.ContinuousAnnularMaximalInterface
import Mathlib.Topology.Order.IsLUB

set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace PrimeSquares

/-- The same standard one-sided Hardy--Littlewood boundary on its full Lp domain.
No annular operator or current-paper conclusion occurs in this hypothesis. -/
def RawFullOneSidedHLInput (C : ℝ) : Prop :=
  ∀ p : ℝ, 1 < p → p ≤ 2 → ∀ f : ℝ → ℂ, MemLp f (ENNReal.ofReal p) volume →
    ∃ H : ℝ → ℝ, MemLp H (ENNReal.ofReal p) volume ∧ (∀ x,0 ≤ H x) ∧
      eLpNorm H (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C/(p-1))*eLpNorm f (ENNReal.ofReal p) volume ∧
      ∀ R : ℝ, 0 < R → ∀ᵐ x ∂volume, oneSidedBoxAverage R f x ≤ H x

theorem full_one_sided_HL_implies_existing {C : ℝ} (H : RawFullOneSidedHLInput C) :
    RawOneSidedHLInput C := by
  intro p hp hp2 f _ hf
  exact H p hp hp2 f hf

noncomputable def realAnnularDenseScales : Set (Set.Ici (2:ℝ)) :=
  Classical.choose (TopologicalSpace.exists_countable_dense (Set.Ici (2:ℝ)))

theorem realAnnularDenseScales_countable : realAnnularDenseScales.Countable :=
  (Classical.choose_spec (TopologicalSpace.exists_countable_dense (Set.Ici (2:ℝ)))).1

theorem realAnnularDenseScales_dense : Dense realAnnularDenseScales :=
  (Classical.choose_spec (TopologicalSpace.exists_countable_dense (Set.Ici (2:ℝ)))).2

noncomputable def realContinuousAnnularMaxENorm (β : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ N : Set.Ici (2:ℝ), ‖realContinuousAnnularConvolution N.val β f x‖ₑ

noncomputable def realContinuousAnnularMaxValue (β : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  (realContinuousAnnularMaxENorm β f x).toReal

theorem realContinuousAnnularMax_countable {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : ℝ → ℂ} (hf : MemLp f p volume) (β x : ℝ) :
    realContinuousAnnularMaxENorm β f x=
      ⨆ N : realAnnularDenseScales,
        ‖realContinuousAnnularConvolution N.val.val β f x‖ₑ := by
  symm
  exact realAnnularDenseScales_dense.ciSup'
    ((realContinuousAnnularConvolution_continuous_scale β hp hf x).enorm)

theorem realContinuousAnnularMax_aemeasurable {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : ℝ → ℂ} (hf : MemLp f p volume) (β : ℝ) :
    AEMeasurable (realContinuousAnnularMaxENorm β f) volume := by
  have : Countable realAnnularDenseScales := realAnnularDenseScales_countable.to_subtype
  have he : realContinuousAnnularMaxENorm β f=
      (fun x => ⨆ N : realAnnularDenseScales,
        ‖realContinuousAnnularConvolution N.val.val β f x‖ₑ) :=
    funext (realContinuousAnnularMax_countable hp hf β)
  rw [he]
  apply AEMeasurable.iSup
  intro N
  have hN : 0 < N.val.val := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) N.val.property
  exact (realContinuousAnnularConvolution_aestronglyMeasurable hN β hf.aestronglyMeasurable).aemeasurable.enorm

theorem oneSidedBoxAverage_enlarge {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℝ → ℂ}
    (hf : MemLp f p volume) {R T : ℝ} (hR : 0 < R) (hRT : R ≤ T) (hT : T ≤ 2*R)
    (x : ℝ) : oneSidedBoxAverage R f x ≤ 2*oneSidedBoxAverage T f x := by
  have hTp : 0 < T := hR.trans_le hRT
  have hi := (shiftedLp_integrableOn hp hf x 0 T).norm
  have hsub : Set.Icc (0:ℝ) R ⊆ Set.Icc 0 T := fun _ hy => ⟨hy.1,hy.2.trans hRT⟩
  have hInt : (∫ y in Set.Icc 0 R,‖f (x-y)‖) ≤ ∫ y in Set.Icc 0 T,‖f (x-y)‖ :=
    setIntegral_mono_set hi (Eventually.of_forall (fun _ => norm_nonneg _))
      (Eventually.of_forall (fun _ hy => hsub hy))
  have hcoef : 1/R ≤ 2/T := (div_le_div_iff₀ hR hTp).mpr (by linarith)
  unfold oneSidedBoxAverage
  calc
    _ ≤ (1/R)*(∫ y in Set.Icc 0 T,‖f (x-y)‖) :=
      mul_le_mul_of_nonneg_left hInt (by positivity)
    _ ≤ (2/T)*(∫ y in Set.Icc 0 T,‖f (x-y)‖) :=
      mul_le_mul_of_nonneg_right hcoef (integral_nonneg (fun _ => norm_nonneg _))
    _ = _ := by ring

theorem realContinuousAnnular_common_majorant {C p β : ℝ}
    (HHL : RawFullOneSidedHLInput C) (hp : 1 < p) (hp2 : p ≤ 2) (hβ : β ≤ 1)
    {f : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∃ H : ℝ → ℝ, MemLp H (ENNReal.ofReal p) volume ∧ (∀ x,0 ≤ H x) ∧
      eLpNorm H (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C/(p-1))*eLpNorm f (ENNReal.ofReal p) volume ∧
      ∀ᵐ x ∂volume, ∀ N : ℝ, 2 ≤ N →
        ‖realContinuousAnnularConvolution N β f x‖ ≤ 2*H x := by
  obtain ⟨H,hH,hH0,hBound,hBoxes⟩ := HHL p hp hp2 f hf
  have hcount : ∀ᵐ x ∂volume, ∀ m : ℕ, 0 < m → oneSidedBoxAverage (m:ℝ) f x ≤ H x := by
    apply ae_all_iff.mpr
    intro m
    by_cases hm : 0 < m
    · exact (hBoxes m (by exact_mod_cast hm)).mono (fun _ hx _ => hx)
    · exact Eventually.of_forall (fun _ h => False.elim (hm h))
  have hpp : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  refine ⟨H,hH,hH0,hBound,?_⟩
  filter_upwards [hcount] with x hx
  intro N hN
  have hR : (1:ℝ) ≤ N^2 := by nlinarith
  have hCeil : (⌈N^2⌉₊:ℝ) ≤ 2*N^2 := by
    have h := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ N^2)
    linarith
  have hM : 0 < ⌈N^2⌉₊ := Nat.ceil_pos.mpr (by positivity)
  exact (realContinuousAnnularConvolution_box_bound hN hβ hpp hf x).trans
    ((oneSidedBoxAverage_enlarge hpp hf (by positivity : (0:ℝ)<N^2) (Nat.le_ceil _) hCeil x).trans
      (mul_le_mul_of_nonneg_left (hx _ hM) (by norm_num)))

theorem realContinuousAnnular_maximal_Lp {C p β : ℝ}
    (HHL : RawFullOneSidedHLInput C) (hp : 1 < p) (hp2 : p ≤ 2) (hβ : β ≤ 1)
    {f : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∀ᵐ x ∂volume, realContinuousAnnularMaxENorm β f x < ∞) ∧
      MemLp (realContinuousAnnularMaxValue β f) (ENNReal.ofReal p) volume ∧
      eLpNorm (realContinuousAnnularMaxValue β f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (2*C/(p-1))*eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨H,hH,hH0,hBound,hDom⟩ := realContinuousAnnular_common_majorant HHL hp hp2 hβ hf
  have hpp : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hmax : ∀ᵐ x ∂volume, realContinuousAnnularMaxENorm β f x ≤ ENNReal.ofReal (2*H x) := by
    filter_upwards [hDom] with x hx
    apply iSup_le
    intro N
    rw [←ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hx N.val N.property)
  have hfinite : ∀ᵐ x ∂volume, realContinuousAnnularMaxENorm β f x < ∞ :=
    hmax.mono (fun _ hx => hx.trans_lt ENNReal.ofReal_lt_top)
  have hm := (realContinuousAnnularMax_aemeasurable hpp hf β).ennreal_toReal.aestronglyMeasurable
  have hd : ∀ᵐ x ∂volume, ‖realContinuousAnnularMaxValue β f x‖ ≤ 2*H x := by
    filter_upwards [hmax,hfinite] with x hx _
    rw [realContinuousAnnularMaxValue,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (hH0 x)))
  have h2H : MemLp (fun x => (2:ℝ)*H x) (ENNReal.ofReal p) volume := hH.const_mul 2
  refine ⟨hfinite,h2H.mono' hm hd,?_⟩
  calc
    _ ≤ eLpNorm (fun x => (2:ℝ)*H x) (ENNReal.ofReal p) volume :=
      eLpNorm_mono_ae_real hm hd
    _ = ENNReal.ofReal 2*eLpNorm H (ENNReal.ofReal p) volume := by
      change eLpNorm ((2:ℝ) • H) (ENNReal.ofReal p) volume=_
      rw [eLpNorm_const_smul,Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤2)]
    _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal (C/(p-1))*eLpNorm f (ENNReal.ofReal p) volume) :=
      mul_le_mul_right hBound _
    _ = _ := by rw [←mul_assoc,←ENNReal.ofReal_mul (by norm_num)];congr 2;ring

end PrimeSquares
