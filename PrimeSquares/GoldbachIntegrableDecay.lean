import PrimeSquares.GoldbachCutoffBounds

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

theorem goldbach_halfline_integrable_decay (f : ℝ→ℂ) (hf : StronglyMeasurable f)
    {c M B : ℝ} (hc : 0<c) (_hB : 0≤B)
    (hnear : ∀ t : ℝ,0<t →t≤c →‖f t‖≤M)
    (hfar : ∀ t : ℝ,c<t →‖f t‖≤B*t^(-(3/2:ℝ))) :
    IntegrableOn f (Set.Ioi 0) ∧
      (∫ t in Set.Ioi (0:ℝ),‖f t‖)≤M*c+2*B/Real.sqrt c := by
  have hi₁ : IntegrableOn f (Set.Ioc 0 c) := IntegrableOn.of_bound (by rw [Real.volume_Ioc];exact ENNReal.ofReal_lt_top)
    hf.aestronglyMeasurable.restrict M (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hnear t ht.1 ht.2)
  have hip := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3/2:ℝ))< -1) hc).const_mul B
  have hi₂ : IntegrableOn f (Set.Ioi c) := hip.mono' hf.aestronglyMeasurable.restrict (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hfar t ht)
  have hi : IntegrableOn f (Set.Ioi 0) := by
    simpa only [Set.Ioc_union_Ioi_eq_Ioi hc.le] using hi₁.union hi₂
  refine ⟨hi,?_⟩
  have h₁ : (∫ t in Set.Ioc (0:ℝ) c,‖f t‖)≤M*c := by
    calc
      _≤∫ _t in Set.Ioc (0:ℝ) c,M := integral_mono_ae hi₁.norm (integrableOn_const (by rw [Real.volume_Ioc];exact ENNReal.ofReal_ne_top)) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hnear t ht.1 ht.2)
      _=_ := by rw [setIntegral_const,smul_eq_mul,Measure.real,Real.volume_Ioc,
          sub_zero,ENNReal.toReal_ofReal hc.le];ring
  have h₂ : (∫ t in Set.Ioi c,‖f t‖)≤2*B/Real.sqrt c := by
    calc
      _≤∫ t in Set.Ioi c,B*t^(-(3/2:ℝ)) := integral_mono_ae hi₂.norm hip (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hfar t ht)
      _=_ := by
        rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-(3/2:ℝ))< -1) hc,
          show (-(3/2:ℝ))+1= -(1/2:ℝ) by norm_num,Real.rpow_neg hc.le,←Real.sqrt_eq_rpow]
        ring
  have he := setIntegral_union (s:=Set.Ioc (0:ℝ) c) (t:=Set.Ioi c)
    (by apply Set.disjoint_left.mpr;intro t ht₁ ht₂;exact not_lt_of_ge ht₁.2 ht₂)
    measurableSet_Ioi hi₁.norm hi₂.norm
  rw [Set.Ioc_union_Ioi_eq_Ioi hc.le] at he
  rw [he]
  exact add_le_add h₁ h₂

theorem goldbach_two_sided_integrable_decay (f : ℝ→ℂ) (hf : StronglyMeasurable f)
    {c M B : ℝ} (hc : 0<c) (hB : 0≤B)
    (hnear : ∀ t : ℝ,|t|≤c →‖f t‖≤M)
    (hfar : ∀ t : ℝ,c < |t| →‖f t‖≤B*|t|^(-(3/2:ℝ))) :
    Integrable f ∧ (∫ t : ℝ,‖f t‖)≤2*M*c+4*B/Real.sqrt c := by
  have hp := goldbach_halfline_integrable_decay f hf hc hB
    (fun t ht htc=>hnear t (by rwa [abs_of_pos ht]))
    (fun t ht=>by simpa only [abs_of_pos (hc.trans ht)] using hfar t (by rwa [abs_of_pos (hc.trans ht)]))
  have hm := goldbach_halfline_integrable_decay (fun t=>f (-t))
    (hf.comp_measurable measurable_neg) hc hB
    (fun t ht htc=>hnear (-t) (by simpa only [abs_neg,abs_of_pos ht] using htc))
    (fun t ht=>by simpa only [abs_neg,abs_of_pos (hc.trans ht)] using (hfar (-t) (by simpa only [abs_neg,abs_of_pos (hc.trans ht)] using ht)))
  have hl : IntegrableOn f (Set.Iic 0) := by
    rw [←Measure.map_neg_eq_self (volume:Measure ℝ)]
    let m : MeasurableEmbedding (fun t : ℝ=>-t) := (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    rw [m.integrableOn_map_iff]
    simpa only [Function.comp_def,Set.neg_preimage,Set.neg_Iic,neg_zero] using
      (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hm.1)
  have hi : Integrable f := by
    have h := hl.union hp.1
    simpa only [Set.Iic_union_Ioi,integrableOn_univ] using h
  refine ⟨hi,?_⟩
  have he := intervalIntegral.integral_Iic_add_Ioi hl.norm hp.1.norm
  rw [←he]
  have hr : (∫ t in Set.Iic (0:ℝ),‖f t‖)=(∫ t in Set.Ioi (0:ℝ),‖f (-t)‖) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi 0 (fun t=>‖f t‖)).symm
  rw [hr]
  exact (add_le_add hm.2 hp.2).trans_eq (by ring)

end PrimeSquares
