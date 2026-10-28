import PrimeSquares.ContinuousAnnularConvolution

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

/-- Independent one-sided real Hardy-Littlewood maximal theorem. This is a
hypothesis for arbitrary functions and all positive real interval lengths,
with explicit near-one dependence. It contains no annular or IW conclusion. -/
def RawOneSidedHLInput (C : ℝ) : Prop :=
  ∀ p : ℝ,1<p → p≤2 → ∀ f : ℝ→ℂ,MemLp f 2 volume →
    MemLp f (ENNReal.ofReal p) volume →
    ∃ H : ℝ→ℝ,MemLp H (ENNReal.ofReal p) volume ∧ (∀ x,0≤H x) ∧
      eLpNorm H (ENNReal.ofReal p) volume≤
        ENNReal.ofReal (C/(p-1))*eLpNorm f (ENNReal.ofReal p) volume ∧
      ∀ R : ℝ,0<R → ∀ᵐ x ∂volume,oneSidedBoxAverage R f x≤H x

noncomputable def continuousAnnularMaximal (β : ℝ) (f : ℝ→ℂ) (x : ℝ) : ℝ :=
  ⨆ n : ℕ,‖continuousAnnularConvolution (n+2) β f x‖

theorem continuousAnnular_maximal_majorant {C : ℝ} (HHL : RawOneSidedHLInput C)
    {p β : ℝ} (hp0 : 1<p) (hp1 : p≤2) (hβ1 : β≤1)
    {f : ℝ→ℂ} (hf2 : MemLp f 2 volume) (hfp : MemLp f (ENNReal.ofReal p) volume) :
    ∃ H : ℝ→ℝ,MemLp H (ENNReal.ofReal p) volume ∧ (∀ x,0≤H x) ∧
      eLpNorm H (ENNReal.ofReal p) volume≤
        ENNReal.ofReal (C/(p-1))*eLpNorm f (ENNReal.ofReal p) volume ∧
      ∀ᵐ x ∂volume,∀ N : ℕ,2≤N → ‖continuousAnnularConvolution N β f x‖≤H x := by
  obtain ⟨H,hH,hpos,hbound,havg⟩ := HHL p hp0 hp1 f hf2 hfp
  refine ⟨H,hH,hpos,hbound,ae_all_iff.mpr ?_⟩
  intro N
  by_cases hN : 2≤N
  · have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
    filter_upwards [havg ((N : ℝ)^2) (by positivity)] with x hx
    intro _
    exact (continuousAnnularConvolution_box_bound hN hβ1 hf2 x).trans hx
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (hN h))

theorem continuousAnnular_maximal_Lp {C : ℝ} (HHL : RawOneSidedHLInput C)
    {p β : ℝ} (hp0 : 1<p) (hp1 : p≤2) (hβ1 : β≤1)
    {f : ℝ→ℂ} (hf2 : MemLp f 2 volume) (hfp : MemLp f (ENNReal.ofReal p) volume) :
    MemLp (continuousAnnularMaximal β f) (ENNReal.ofReal p) volume ∧
      eLpNorm (continuousAnnularMaximal β f) (ENNReal.ofReal p) volume≤
        ENNReal.ofReal (C/(p-1))*eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨H,hH,_hpos,hbound,hdom⟩ := continuousAnnular_maximal_majorant HHL hp0 hp1 hβ1 hf2 hfp
  have hm : AEStronglyMeasurable (continuousAnnularMaximal β f) volume := by
    exact (AEMeasurable.iSup (fun n : ℕ =>
      (continuousAnnularConvolution_aestronglyMeasurable (N := n+2) (by omega) β hf2.aestronglyMeasurable).norm.aemeasurable)).aestronglyMeasurable
  have hd : ∀ᵐ x ∂volume,‖continuousAnnularMaximal β f x‖≤H x := by
    filter_upwards [hdom] with x hx
    have hb : BddAbove (Set.range (fun n : ℕ => ‖continuousAnnularConvolution (n+2) β f x‖)) := by
      refine ⟨H x,?_⟩
      rintro y ⟨n,rfl⟩
      exact hx (n+2) (by omega)
    have hnon : 0≤continuousAnnularMaximal β f x :=
      (norm_nonneg _).trans (le_ciSup hb 0)
    rw [Real.norm_eq_abs,abs_of_nonneg hnon]
    exact ciSup_le (fun n : ℕ => hx (n+2) (by omega))
  refine ⟨hH.mono' hm hd,?_⟩
  exact (eLpNorm_mono_ae hm (hd.mono (fun x hx => hx.trans (le_abs_self (H x))))).trans hbound

end PrimeSquares
