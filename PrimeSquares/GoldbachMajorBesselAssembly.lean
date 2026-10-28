import PrimeSquares.GoldbachCircleMajorEstimates

set_option autoImplicit false
open Finset MeasureTheory
open scoped ENNReal
namespace PrimeSquares

theorem goldbach_restricted_function_bessel (S : Finset ℤ) (s : Set PrimeCircle)
    (hs : MeasurableSet s) (f : PrimeCircle→ℂ) (hf : MemLp f 2 AddCircle.haarAddCircle) :
    (∑ n∈S,‖∫ θ : PrimeCircle in s,f θ*fourier (-n) θ ∂AddCircle.haarAddCircle‖^2)≤
      ∫ θ : PrimeCircle in s,‖f θ‖^2 ∂AddCircle.haarAddCircle := by
  classical
  let g := s.indicator f
  have hg : MemLp g 2 AddCircle.haarAddCircle := hf.indicator hs
  have hc (n : ℤ) : fourierCoeff g n=
      ∫ θ : PrimeCircle in s,f θ*fourier (-n) θ ∂AddCircle.haarAddCircle := by
    rw [←integral_indicator hs]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun θ => by
      by_cases hθ : θ∈s <;> simp [g,hθ,smul_eq_mul,mul_comm])
  have he : (∫ θ : PrimeCircle,‖g θ‖^2 ∂AddCircle.haarAddCircle)=
      ∫ θ : PrimeCircle in s,‖f θ‖^2 ∂AddCircle.haarAddCircle := by
    rw [←integral_indicator hs]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun θ => by by_cases hθ : θ∈s <;> simp [g,hθ])
  calc
    _=(∑ n∈S,‖fourierCoeff g n‖^2) := by simp only [hc]
    _≤∫ θ : PrimeCircle,‖g θ‖^2 ∂AddCircle.haarAddCircle := goldbach_finite_fourier_bessel S g hg
    _=_ := he

theorem goldbach_restricted_uniform_bessel (S : Finset ℤ) (s : Set PrimeCircle)
    (hs : MeasurableSet s) (f : PrimeCircle→ℂ) (hf : MemLp f 2 AddCircle.haarAddCircle)
    {B : ℝ} (hbound : ∀ θ∈s,‖f θ‖≤B) :
    (∑ n∈S,‖∫ θ : PrimeCircle in s,f θ*fourier (-n) θ ∂AddCircle.haarAddCircle‖^2)≤
      B^2*(AddCircle.haarAddCircle s).toReal := by
  have hi : (∫ θ : PrimeCircle in s,‖f θ‖^2 ∂AddCircle.haarAddCircle)≤
      ∫ _θ : PrimeCircle in s,B^2 ∂AddCircle.haarAddCircle := by
    apply integral_mono_ae (hf.integrable_norm_pow (by decide : 2≠0)).restrict (integrable_const _)
    filter_upwards [ae_restrict_mem hs] with θ hθ
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound θ hθ) 2
  apply (goldbach_restricted_function_bessel S s hs f hf).trans
  apply hi.trans_eq
  rw [setIntegral_const,smul_eq_mul,mul_comm]
  rfl

theorem goldbach_restricted_measurable_multiplier_bessel (S : Finset ℤ) (s : Set PrimeCircle)
    (hs : MeasurableSet s) (P F : PrimeCircle→ℂ)
    (hP : MemLp P ∞ AddCircle.haarAddCircle) (hF : MemLp F 2 AddCircle.haarAddCircle)
    {B : ℝ} (hbound : ∀ θ∈s,‖P θ‖≤B) :
    (∑ n∈S,‖∫ θ : PrimeCircle in s,P θ*F θ*fourier (-n) θ ∂AddCircle.haarAddCircle‖^2)≤
      B^2*(∫ θ : PrimeCircle,‖F θ‖^2 ∂AddCircle.haarAddCircle) := by
  classical
  have hp : MemLp (fun θ => P θ*F θ) 2 AddCircle.haarAddCircle := hP.mul hF
  apply (goldbach_restricted_function_bessel S s hs _ hp).trans
  rw [←integral_indicator hs]
  have hiF := hF.integrable_norm_pow (by decide : 2≠0)
  have hiP := (hp.integrable_norm_pow (by decide : 2≠0)).indicator hs
  calc
    _≤∫ θ : PrimeCircle,B^2*‖F θ‖^2 ∂AddCircle.haarAddCircle := by
      apply integral_mono hiP (hiF.const_mul _)
      intro θ
      by_cases hθ : θ∈s
      · rw [Set.indicator_of_mem hθ,norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hbound θ hθ) 2) (sq_nonneg _)
      · rw [Set.indicator_of_notMem hθ]
        positivity
    _=_ := integral_const_mul _ _

theorem goldbach_two_model_major_bessel (S : Finset ℤ) (s : Set PrimeCircle)
    (hs : MeasurableSet s) (P F Q G : PrimeCircle→ℂ)
    (hP : MemLp P ∞ AddCircle.haarAddCircle) (hF : MemLp F 2 AddCircle.haarAddCircle)
    (hQ : MemLp Q ∞ AddCircle.haarAddCircle) (hG : MemLp G 2 AddCircle.haarAddCircle)
    {BQ BP BE E : ℝ} (hBQ : 0≤BQ)
    (hQbound : ∀ θ∈s,‖Q θ‖≤BQ) (hPbound : ∀ θ∈s,‖P θ-Q θ‖≤BP)
    (hFbound : ∀ θ∈s,‖F θ-G θ‖≤BE)
    (henergy : (∫ θ : PrimeCircle,‖F θ‖^2 ∂AddCircle.haarAddCircle)≤E) :
    (∑ n∈S,‖∫ θ : PrimeCircle in s,(P θ*F θ-Q θ*G θ)*fourier (-n) θ
      ∂AddCircle.haarAddCircle‖^2)≤
        2*(BQ^2*BE^2*(AddCircle.haarAddCircle s).toReal+BP^2*E) := by
  let f₁ := fun θ => Q θ*(F θ-G θ)
  let f₂ := fun θ => (P θ-Q θ)*F θ
  have h₁ : MemLp f₁ 2 AddCircle.haarAddCircle := hQ.mul (hF.sub hG)
  have h₂ : MemLp f₂ 2 AddCircle.haarAddCircle := (hP.sub hQ).mul hF
  have hb₁ := goldbach_restricted_uniform_bessel S s hs f₁ h₁ (B:=BQ*BE) (fun θ hθ => by
    rw [norm_mul]
    exact mul_le_mul (hQbound θ hθ) (hFbound θ hθ) (norm_nonneg _) hBQ)
  have hb₂ := goldbach_restricted_measurable_multiplier_bessel S s hs
    (fun θ => P θ-Q θ) F (hP.sub hQ) hF hPbound
  have hb₂' := hb₂.trans (mul_le_mul_of_nonneg_left henergy (sq_nonneg BP))
  have he (n : ℤ) : (∫ θ : PrimeCircle in s,(P θ*F θ-Q θ*G θ)*fourier (-n) θ
      ∂AddCircle.haarAddCircle)=
      (∫ θ : PrimeCircle in s,f₁ θ*fourier (-n) θ ∂AddCircle.haarAddCircle)+
      ∫ θ : PrimeCircle in s,f₂ θ*fourier (-n) θ ∂AddCircle.haarAddCircle := by
    have hc : MemLp ((fourier (-n)) : PrimeCircle→ℂ) ∞ AddCircle.haarAddCircle := ContinuousMap.memLp AddCircle.haarAddCircle ℂ _
    have hp₁ : MemLp (fun θ => f₁ θ*fourier (-n) θ) 2 AddCircle.haarAddCircle := h₁.mul hc
    have hp₂ : MemLp (fun θ => f₂ θ*fourier (-n) θ) 2 AddCircle.haarAddCircle := h₂.mul hc
    have hpnt : (fun θ => (P θ*F θ-Q θ*G θ)*fourier (-n) θ)=
        (fun θ => f₁ θ*fourier (-n) θ+f₂ θ*fourier (-n) θ) := by
      funext θ
      dsimp only [f₁,f₂]
      ring
    rw [hpnt]
    exact integral_add (hp₁.integrable (by norm_num : (1:ℝ≥0∞)≤2)).restrict
      (hp₂.integrable (by norm_num : (1:ℝ≥0∞)≤2)).restrict
  calc
    _≤∑ n∈S,2*(‖∫ θ : PrimeCircle in s,f₁ θ*fourier (-n) θ ∂AddCircle.haarAddCircle‖^2+
      ‖∫ θ : PrimeCircle in s,f₂ θ*fourier (-n) θ ∂AddCircle.haarAddCircle‖^2) := by
      apply sum_le_sum
      intro n _
      rw [he]
      have hh := norm_add_le
        (∫ θ : PrimeCircle in s,f₁ θ*fourier (-n) θ ∂AddCircle.haarAddCircle)
        (∫ θ : PrimeCircle in s,f₂ θ*fourier (-n) θ ∂AddCircle.haarAddCircle)
      have hsquare := pow_le_pow_left₀ (norm_nonneg _) hh 2
      nlinarith only [hsquare,sq_nonneg (‖∫ θ : PrimeCircle in s,f₁ θ*fourier (-n) θ ∂AddCircle.haarAddCircle‖-
        ‖∫ θ : PrimeCircle in s,f₂ θ*fourier (-n) θ ∂AddCircle.haarAddCircle‖)]
    _=2*((∑ n∈S,‖∫ θ : PrimeCircle in s,f₁ θ*fourier (-n) θ ∂AddCircle.haarAddCircle‖^2)+
      ∑ n∈S,‖∫ θ : PrimeCircle in s,f₂ θ*fourier (-n) θ ∂AddCircle.haarAddCircle‖^2) := by
      rw [←mul_sum,sum_add_distrib]
    _≤2*((BQ*BE)^2*(AddCircle.haarAddCircle s).toReal+BP^2*E) :=
      mul_le_mul_of_nonneg_left (add_le_add hb₁ hb₂') (by norm_num)
    _=2*(BQ^2*BE^2*(AddCircle.haarAddCircle s).toReal+BP^2*E) := by ring

end PrimeSquares
