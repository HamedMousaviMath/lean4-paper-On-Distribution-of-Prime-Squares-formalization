import PrimeSquares.ContinuousAnnularKernelTranslation

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

noncomputable def annularFarTranslation (N : ℕ) (β h x : ℝ) : ℝ :=
  {y : ℝ | 2*|h| < |y|}.indicator
    (fun y => |continuousAnnularKernel N β (y-h)-continuousAnnularKernel N β y|) x

theorem annularFarTranslation_nonneg (N : ℕ) (β h x : ℝ) :
    0≤annularFarTranslation N β h x :=
  Set.indicator_nonneg (fun _ _ => abs_nonneg _) x

theorem annularFarTranslation_integrable {N : ℕ} (hN : 1≤N) (β h : ℝ) :
    Integrable (annularFarTranslation N β h) volume :=
  (continuousAnnularKernel_translation_integrable hN β h).indicator
    (measurableSet_lt measurable_const continuous_abs.measurable)

theorem annularFarTranslation_integral_le {N : ℕ} (hN : 1≤N) (β h : ℝ) :
    (∫ x,annularFarTranslation N β h x)≤
      ∫ x,|continuousAnnularKernel N β (x-h)-continuousAnnularKernel N β x| := by
  apply integral_mono (annularFarTranslation_integrable hN β h)
    (continuousAnnularKernel_translation_integrable hN β h)
  intro x
  by_cases hx : x∈{y : ℝ | 2*|h| < |y|}
  · rw [annularFarTranslation,Set.indicator_of_mem hx]
  · rw [annularFarTranslation,Set.indicator_of_notMem hx]
    exact abs_nonneg _

theorem annularFarTranslation_small_zero (N : ℕ) (β : ℝ) {h : ℝ}
    (hsmall : (N : ℝ)^2≤ |h|) (x : ℝ) : annularFarTranslation N β h x=0 := by
  by_cases hx : x∈{y : ℝ | 2*|h| < |y|}
  · rw [annularFarTranslation,Set.indicator_of_mem hx]
    rcases continuousAnnularKernel_far_zero N β hsmall hx with ⟨h1,h2⟩
    rw [h1,h2,sub_self,abs_zero]
  · exact Set.indicator_of_notMem hx _

theorem annularFarTranslation_profile {N : ℕ} (hN : 2≤N) {β : ℝ}
    (hβ0 : 0≤β) (hβ1 : β≤1) {h : ℝ} (hh : 0 < |h|) :
    (∫ x,annularFarTranslation N β h x)≤
      7*min ((N : ℝ)^2/|h|) (((N : ℝ)^2/|h|)⁻¹) := by
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hy : 0≤(N : ℝ)^2/|h| := by positivity
  by_cases hs : (N : ℝ)^2≤ |h|
  · have he : annularFarTranslation N β h=0 := by
      funext x
      exact annularFarTranslation_small_zero N β hs x
    rw [he]
    simp only [Pi.zero_apply,integral_zero]
    positivity
  · have hgt : |h|<(N : ℝ)^2 := lt_of_not_ge hs
    have h1 : 1≤(N : ℝ)^2/|h| := (le_div_iff₀ hh).mpr (by linarith)
    have hi : ((N : ℝ)^2/|h|)⁻¹≤(N : ℝ)^2/|h| :=
      (inv_le_one_of_one_le₀ h1).trans h1
    rw [min_eq_right hi,inv_div]
    calc
      _ ≤ ∫ x,|continuousAnnularKernel N β (x-h)-continuousAnnularKernel N β x| :=
        annularFarTranslation_integral_le (by omega) β h
      _ ≤ 7*|h|/(N : ℝ)^2 := continuousAnnularKernel_translation_bound hN hβ0 hβ1 h
      _ = _ := by ring

end PrimeSquares
