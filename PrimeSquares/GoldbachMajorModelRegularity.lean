import PrimeSquares.GoldbachMajorArcGeometry
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

noncomputable def goldbachArcCoordinate (r : ℚ) (θ : PrimeCircle) : ℝ :=
  (AddCircle.measurableEquivIco (T:=(1:ℝ)) (-(1/2:ℝ)) (θ-((r:ℝ):PrimeCircle))).val

theorem goldbachArcCoordinate_measurable (r : ℚ) : Measurable (goldbachArcCoordinate r) :=
  measurable_subtype_coe.comp ((AddCircle.measurableEquivIco (T:=(1:ℝ)) (-(1/2:ℝ))).measurable.comp
    (measurable_id.sub measurable_const))

theorem goldbachArcCoordinate_coe (r : ℚ) (θ : PrimeCircle) :
    ((goldbachArcCoordinate r θ:ℝ):PrimeCircle)=θ-((r:ℝ):PrimeCircle) :=
  AddCircle.coe_equivIco

theorem goldbachArcCoordinate_bounds (r : ℚ) (θ : PrimeCircle) :
    -(1/2:ℝ)≤goldbachArcCoordinate r θ ∧ goldbachArcCoordinate r θ<1/2 := by
  have h := (AddCircle.equivIco (1:ℝ) (-(1/2:ℝ)) (θ-((r:ℝ):PrimeCircle))).prop
  change -(1/2:ℝ)≤goldbachArcCoordinate r θ ∧ goldbachArcCoordinate r θ< -(1/2:ℝ)+1 at h
  exact ⟨h.1,by linarith [h.2]⟩

theorem goldbachArcCoordinate_abs (r : ℚ) (θ : PrimeCircle) :
    |goldbachArcCoordinate r θ|=dist θ ((r:ℝ):PrimeCircle) := by
  obtain ⟨hlo,hhi⟩ := goldbachArcCoordinate_bounds r θ
  have hhalf : |goldbachArcCoordinate r θ|≤|(1:ℝ)|/2 := by
    rw [abs_one]
    exact abs_le.mpr ⟨hlo,hhi.le⟩
  have hn := (AddCircle.norm_coe_eq_abs_iff (p:=(1:ℝ)) (x:=goldbachArcCoordinate r θ) (by norm_num)).mpr hhalf
  rw [goldbachArcCoordinate_coe] at hn
  simpa only [dist_eq_norm] using hn.symm

theorem goldbachArcCoordinate_reconstruct (r : ℚ) (θ : PrimeCircle) :
    (((r:ℝ)+goldbachArcCoordinate r θ:ℝ):PrimeCircle)=θ := by
  rw [AddCircle.coe_add,goldbachArcCoordinate_coe]
  abel

theorem goldbachSquareIntegral_stronglyMeasurable (U : ℝ) :
    StronglyMeasurable (goldbachSquareIntegral U) := by
  have ho : Continuous (fun z : ℝ×ℝ => quadraticOscillation (-z.1) z.2) := by
    unfold quadraticOscillation
    fun_prop
  have hd : StronglyMeasurable (fun z : ℝ×ℝ => (((Real.log z.2)⁻¹:ℝ):ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp measurable_snd).inv).stronglyMeasurable
  exact (ho.stronglyMeasurable.mul hd).integral_prod_right' (ν:=volume.restrict (Set.Ioc 2 U))

theorem goldbachLinearIntegral_stronglyMeasurable (U : ℝ) :
    StronglyMeasurable (goldbachLinearIntegral U) := by
  have ho : Continuous (fun z : ℝ×ℝ => realFourierPhase (z.1*z.2)) :=
    realFourierPhase_continuous.comp (by fun_prop)
  have hd : StronglyMeasurable (fun z : ℝ×ℝ => (((Real.log z.2)⁻¹:ℝ):ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp measurable_snd).inv).stronglyMeasurable
  exact (ho.stronglyMeasurable.mul hd).integral_prod_right' (ν:=volume.restrict (Set.Ioc 2 U))

theorem goldbachLinearSourceIntegral_stronglyMeasurable (N ℓ : ℕ) (hℓ : 0<ℓ) (W : ℝ) :
    StronglyMeasurable (goldbachLinearSourceIntegral N ℓ W) := by
  have h := (goldbachLinearIntegral_stronglyMeasurable (min W ((N:ℝ)^2/ℓ))).comp_measurable
    (show Measurable (fun γ : ℝ => (ℓ:ℝ)*γ) by fun_prop)
  have he : goldbachLinearSourceIntegral N ℓ W=
      (fun γ => goldbachLinearIntegral (min W ((N:ℝ)^2/ℓ)) ((ℓ:ℝ)*γ)) :=
    funext (goldbach_linear_source_integral N ℓ hℓ W)
  rw [he]
  exact h

theorem goldbach_phase_log_weight_bound {v : ℝ} (hv : 2≤v) (z : ℂ) (hz : ‖z‖=1) :
    ‖z*((Real.log v)⁻¹:ℝ)‖≤1/Real.log 2 := by
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlv : Real.log 2≤Real.log v := Real.log_le_log (by norm_num) hv
  rw [norm_mul,hz,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (hl2.le.trans hlv))]
  simpa only [one_div] using one_div_le_one_div_of_le hl2 hlv

theorem goldbachSquareIntegral_norm {U : ℝ} (hU : 2≤U) (γ : ℝ) :
    ‖goldbachSquareIntegral U γ‖≤U/Real.log 2 := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=2) (b:=U) (f:=fun v => quadraticOscillation (-γ) v*((Real.log v)⁻¹:ℝ))
    (C:=1/Real.log 2) (fun v hv => by
      have hv' : v∈Set.Ioc 2 U := by simpa only [Set.uIoc_of_le hU] using hv
      exact goldbach_phase_log_weight_bound hv'.1.le _ (quadraticOscillation_norm _ _))
  have hb : ‖goldbachSquareIntegral U γ‖≤(1/Real.log 2)*(U-2) := by
    simpa only [goldbachSquareIntegral,intervalIntegral.integral_of_le hU,
      abs_of_nonneg (sub_nonneg.mpr hU)] using hh
  calc
    _≤(1/Real.log 2)*(U-2) := hb
    _=(U-2)/Real.log 2 := by ring
    _≤U/Real.log 2 := div_le_div_of_nonneg_right (by linarith) (Real.log_pos (by norm_num)).le

theorem goldbachLinearIntegral_norm {U : ℝ} (hU : 2≤U) (β : ℝ) :
    ‖goldbachLinearIntegral U β‖≤U/Real.log 2 := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=2) (b:=U) (f:=fun v => realFourierPhase (β*v)*((Real.log v)⁻¹:ℝ))
    (C:=1/Real.log 2) (fun v hv => by
      have hv' : v∈Set.Ioc 2 U := by simpa only [Set.uIoc_of_le hU] using hv
      exact goldbach_phase_log_weight_bound hv'.1.le _ (realFourierPhase_norm _))
  have hb : ‖goldbachLinearIntegral U β‖≤(1/Real.log 2)*(U-2) := by
    simpa only [goldbachLinearIntegral,intervalIntegral.integral_of_le hU,
      abs_of_nonneg (sub_nonneg.mpr hU)] using hh
  calc
    _≤(1/Real.log 2)*(U-2) := hb
    _=(U-2)/Real.log 2 := by ring
    _≤U/Real.log 2 := div_le_div_of_nonneg_right (by linarith) (Real.log_pos (by norm_num)).le

theorem goldbachLinearSourceIntegral_norm (N ℓ : ℕ) (hℓ : 0<ℓ) {W : ℝ} (hW : 2≤W)
    (hX : 2≤(N:ℝ)^2/ℓ) (γ : ℝ) :
    ‖goldbachLinearSourceIntegral N ℓ W γ‖≤W/Real.log 2 := by
  rw [goldbach_linear_source_integral N ℓ hℓ W γ]
  exact (goldbachLinearIntegral_norm (le_min hW hX) _).trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (Real.log_pos (by norm_num)).le)

end PrimeSquares
