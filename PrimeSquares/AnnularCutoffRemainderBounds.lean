import PrimeSquares.RealMultiplierSubtraction
import PrimeSquares.ContinuousAnnularCutoffLp
import PrimeSquares.AnnularFourierSmoothness
import PrimeSquares.AnnularModelDecay

set_option autoImplicit false
open scoped ContDiff
namespace PrimeSquares

theorem sourceArcCutoff_nested_core {a b θ : ℝ} (ha : 0≤ a) (hb : 0< b)
    (hab : 2*a≤ b) (hθ : sourceArcCutoff (b*θ)≠0) : sourceArcCutoff (a*θ)=1 := by
  have hr := sourceArcCutoff_radius hθ
  rw [abs_mul,abs_of_pos hb] at hr
  apply sourceArcCutoff_core
  rw [abs_mul,abs_of_nonneg ha]
  have hm := mul_le_mul_of_nonneg_right hab (abs_nonneg θ)
  nlinarith

theorem sourceArcCutoff_nested_product {a b : ℝ} (ha : 0≤ a) (hb : 0< b)
    (hab : 2*a≤ b) (θ : ℝ) :
    sourceArcCutoff (a*θ)*sourceArcCutoff (b*θ)=sourceArcCutoff (b*θ) := by
  by_cases hz : sourceArcCutoff (b*θ)=0
  · rw [hz,mul_zero]
  · rw [sourceArcCutoff_nested_core ha hb hab hz,one_mul]

noncomputable def annularCutoffRemainderSymbol (N : ℕ) (hN : 1≤ N) (β : ℝ)
    (hβ0 : 0≤β) (hβ1 : β≤1) (a b : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  allAnnularBoundedSymbol N hN β hβ0 hβ1 a-allAnnularBoundedSymbol N hN β hβ0 hβ1 b

theorem annularCutoffRemainderSymbol_factor (N : ℕ) (hN : 1≤ N) (β : ℝ)
    (hβ0 : 0≤β) (hβ1 : β≤1) {a b : ℝ} (ha : 0≤ a) (hb : 0< b)
    (hab : 2*a≤ b) (θ : ℝ) :
    annularCutoffRemainderSymbol N hN β hβ0 hβ1 a b θ=
      annularOscillatoryModel N β θ*Complex.ofReal (sourceArcCutoff (a*θ))*
        (1-Complex.ofReal (sourceArcCutoff (b*θ))) := by
  change allAnnularBoundedSymbol N hN β hβ0 hβ1 a θ-
    allAnnularBoundedSymbol N hN β hβ0 hβ1 b θ=_
  rw [allAnnularBoundedSymbol_apply,allAnnularBoundedSymbol_apply]
  have he : Complex.ofReal (sourceArcCutoff (a*θ))*Complex.ofReal (sourceArcCutoff (b*θ))=
      Complex.ofReal (sourceArcCutoff (b*θ)) := by
    rw [←Complex.ofReal_mul,sourceArcCutoff_nested_product ha hb hab θ]
  calc
    _ = annularOscillatoryModel N β θ*Complex.ofReal (sourceArcCutoff (a*θ))-
        annularOscillatoryModel N β θ*(Complex.ofReal (sourceArcCutoff (a*θ))*
          Complex.ofReal (sourceArcCutoff (b*θ))) := by rw [he]
    _ = _ := by ring

theorem annularCutoffRemainderSymbol_norm_le (N : ℕ) (hN : 1≤ N) (β : ℝ)
    (hβ0 : 0≤β) (hβ1 : β≤1) {a b : ℝ} (ha : 0≤ a) (hb : 0< b)
    (hab : 2*a≤ b) (θ : ℝ) :
    ‖annularCutoffRemainderSymbol N hN β hβ0 hβ1 a b θ‖≤‖annularOscillatoryModel N β θ‖ := by
  have hneg : 0≤1-sourceArcCutoff (b*θ) := sub_nonneg.mpr (sourceArcCutoff_le_one _)
  have hsub : ‖(1 : ℂ)-Complex.ofReal (sourceArcCutoff (b*θ))‖=1-sourceArcCutoff (b*θ) := by
    rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hneg]
  rw [annularCutoffRemainderSymbol_factor N hN β hβ0 hβ1 ha hb hab θ,norm_mul,norm_mul,
    hsub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sourceArcCutoff_nonneg _)]
  have hprod : sourceArcCutoff (a*θ)*(1-sourceArcCutoff (b*θ))≤1 := by
    have h := mul_le_mul (sourceArcCutoff_le_one (a*θ))
      (show 1-sourceArcCutoff (b*θ)≤1 by linarith [sourceArcCutoff_nonneg (b*θ)]) hneg (by norm_num : (0 : ℝ)≤1)
    simpa only [mul_one] using h
  have h := mul_le_mul_of_nonneg_left hprod (norm_nonneg (annularOscillatoryModel N β θ))
  nlinarith

theorem annularCutoffRemainderSymbol_decay {N : ℕ} (hN : 2≤ N) {β : ℝ}
    (hβ0 : 0≤β) (hβ1 : β≤1) {a b : ℝ} (ha : 0≤ a) (hb : 0< b)
    (hab : 2*a≤ b) (θ : ℝ) :
    ‖annularCutoffRemainderSymbol N (by omega) β hβ0 hβ1 a b θ‖≤
      4*b/(Real.pi*(N : ℝ)^2) := by
  have hNp : (0 : ℝ)< N := by exact_mod_cast (show 0< N by omega)
  by_cases hz : sourceArcCutoff (b*θ)=1
  · rw [annularCutoffRemainderSymbol_factor N (by omega) β hβ0 hβ1 ha hb hab θ,
      hz,Complex.ofReal_one,sub_self,mul_zero,norm_zero]
    positivity
  · have hcore : (1/2 : ℝ)< |b*θ| := by
      by_contra hn
      exact hz (sourceArcCutoff_core (le_of_not_gt hn))
    rw [abs_mul,abs_of_pos hb] at hcore
    have hθ : 1/(2*b)≤|θ| := by
      apply (div_le_iff₀ (show 0<2*b by positivity)).mpr
      nlinarith
    have hθ0 : θ≠0 := by
      intro he
      subst θ
      norm_num at hcore
    calc
      _ ≤ ‖annularOscillatoryModel N β θ‖ :=
        annularCutoffRemainderSymbol_norm_le N (by omega) β hβ0 hβ1 ha hb hab θ
      _ ≤ 2/(Real.pi*|θ| *(N : ℝ)^2) := annularOscillatoryModel_decay hN hβ0 hβ1 hθ0
      _ ≤ 2/(Real.pi*(1/(2*b))*(N : ℝ)^2) := by gcongr
      _ = _ := by field_simp;ring

theorem annularCutoffRemainderSymbol_smooth (N : ℕ) (hN : 1≤ N) (β : ℝ)
    (hβ0 : 0≤β) (hβ1 : β≤1) (a b : ℝ) :
    ContDiff ℝ ∞ (annularCutoffRemainderSymbol N hN β hβ0 hβ1 a b : ℝ→ℂ) := by
  exact (annularCutoffSymbol_contDiff hN β a).sub (annularCutoffSymbol_contDiff hN β b)

theorem annularCutoffRemainder_Lp_rough (HY : RawYoungMultiplierInput) {N : ℕ} (hN : 1≤ N)
    {β a b p : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (ha : 0< a) (hb : 0< b) (hp : 1≤ p) :
    RealLpMultiplierBound (ENNReal.ofReal p)
      (annularCutoffRemainderSymbol N hN β hβ0.le hβ1 a b) (2*cutoffL1Constant) := by
  have hpen : (1 : ENNReal)≤ ENNReal.ofReal p := by
    rw [←ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  simpa only [two_mul,annularCutoffRemainderSymbol] using realLpMultiplierBound_sub hpen cutoffL1Constant_nonneg cutoffL1Constant_nonneg
    (annularCutoffYoungMultiplier_Lp HY hN hβ0 hβ1 ha hp)
    (annularCutoffYoungMultiplier_Lp HY hN hβ0 hβ1 hb hp)

theorem annularCutoffRemainder_L2 {N : ℕ} (hN : 2≤ N) {β : ℝ}
    (hβ0 : 0≤β) (hβ1 : β≤1) {a b : ℝ} (ha : 0≤ a) (hb : 0< b) (hab : 2*a≤ b) :
    RealLpMultiplierBound 2 (annularCutoffRemainderSymbol N (by omega) β hβ0 hβ1 a b)
      (4*b/(Real.pi*(N : ℝ)^2)) :=
  realLpMultiplierBound_two_of_bound _ (by positivity)
    (annularCutoffRemainderSymbol_decay hN hβ0 hβ1 ha hb hab)

end PrimeSquares
