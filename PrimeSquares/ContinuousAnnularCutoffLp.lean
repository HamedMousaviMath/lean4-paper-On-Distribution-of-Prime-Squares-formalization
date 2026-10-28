import PrimeSquares.ScalarHormanderInterface
import PrimeSquares.CutoffYoungInterface

set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform
namespace PrimeSquares

theorem continuousAnnularSignedSymbol_cutoff (β : ℝ) (hβ0 : 0≤β) (hβ1 : β≤1)
    (a : ℝ) (J : ℕ) (σ : ℕ→ℂ) :
    continuousAnnularSignedSymbol β hβ0 hβ1 a J σ=
      continuousAnnularSignedSymbol β hβ0 hβ1 0 J σ*continuousCutoffSymbol a := by
  ext θ
  rw [BoundedContinuousFunction.mul_apply,continuousAnnularSignedSymbol_apply,
    continuousAnnularSignedSymbol_untruncated,continuousCutoffSymbol_apply]

theorem continuousAnnularCutoffSignedMultiplier_Lp {C : ℝ} (hC : 0≤C)
    (HCZ : RawScalarHormanderInput C) (HY : RawYoungMultiplierInput)
    {β a : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (ha : 0<a)
    (J : ℕ) (σ : ℕ→ℂ) (hσ : ∀ j∈Finset.range J,‖σ j‖≤1)
    {p : ℝ} (hp0 : 1<p) (hp1 : p≤2) :
    RealLpMultiplierBound (ENNReal.ofReal p)
      (continuousAnnularSignedSymbol β hβ0.le hβ1 a J σ)
      ((C*(continuousAnnularIncrementConstant+2+50)/(p-1))*cutoffL1Constant) := by
  rw [continuousAnnularSignedSymbol_cutoff]
  apply realLpMultiplierBound_mul
    (by have h := continuousAnnularIncrementConstant_pos;positivity)
    (continuousAnnularSignedMultiplier_Lp HCZ hβ0 hβ1 J σ hσ hp0 hp1)
    (continuousCutoffMultiplier_Lp HY ha hp0.le)

theorem allAnnularBoundedSymbol_untruncated (N : ℕ) (hN : 1≤N) (β : ℝ)
    (hβ0 : 0≤β) (hβ1 : β≤1) (θ : ℝ) :
    allAnnularBoundedSymbol N hN β hβ0 hβ1 0 θ=annularOscillatoryModel N β θ := by
  rw [allAnnularBoundedSymbol_apply,zero_mul,
    sourceArcCutoff_core (by norm_num : |(0 : ℝ)|≤1/2),Complex.ofReal_one,mul_one]

theorem continuousAnnularKernel_integral_norm_le {N : ℕ} (hN : 1≤N)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) :
    (∫ x,‖Complex.ofReal (continuousAnnularKernel N β x)‖)≤1 := by
  have he (x : ℝ) : ‖Complex.ofReal (continuousAnnularKernel N β x)‖=continuousAnnularKernel N β x := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (continuousAnnularKernel_nonneg hN β x)]
  simp_rw [he]
  rw [continuousAnnularKernel_integral hN β]
  exact (annularMass_re_bounds hN hβ0 hβ1).2

theorem annularYoungMultiplier_Lp (HY : RawYoungMultiplierInput)
    {N : ℕ} (hN : 1≤N) {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1)
    {p : ℝ} (hp : 1≤p) :
    RealLpMultiplierBound (ENNReal.ofReal p) (allAnnularBoundedSymbol N hN β hβ0.le hβ1 0) 1 := by
  have hF (θ : ℝ) :
      𝓕 (fun x => Complex.ofReal (continuousAnnularKernel N β x)) θ=
        allAnnularBoundedSymbol N hN β hβ0.le hβ1 0 θ := by
    rw [allAnnularBoundedSymbol_untruncated]
    exact continuousAnnularKernel_fourier hN β θ
  have h := HY _ (continuousAnnularKernel_complex_integrable hN β) _ hF p hp
  exact realLpMultiplierBound_mono h (continuousAnnularKernel_integral_norm_le hN hβ0 hβ1)

theorem allAnnularBoundedSymbol_cutoff (N : ℕ) (hN : 1≤N) (β : ℝ)
    (hβ0 : 0≤β) (hβ1 : β≤1) (a : ℝ) :
    allAnnularBoundedSymbol N hN β hβ0 hβ1 a=
      allAnnularBoundedSymbol N hN β hβ0 hβ1 0*continuousCutoffSymbol a := by
  ext θ
  rw [BoundedContinuousFunction.mul_apply,allAnnularBoundedSymbol_untruncated,
    allAnnularBoundedSymbol_apply,continuousCutoffSymbol_apply]

theorem annularCutoffYoungMultiplier_Lp (HY : RawYoungMultiplierInput)
    {N : ℕ} (hN : 1≤N) {β a : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (ha : 0<a)
    {p : ℝ} (hp : 1≤p) :
    RealLpMultiplierBound (ENNReal.ofReal p) (allAnnularBoundedSymbol N hN β hβ0.le hβ1 a)
      cutoffL1Constant := by
  rw [allAnnularBoundedSymbol_cutoff]
  simpa only [one_mul] using realLpMultiplierBound_mul zero_le_one
    (annularYoungMultiplier_Lp HY hN hβ0 hβ1 hp) (continuousCutoffMultiplier_Lp HY ha hp)

end PrimeSquares
