import PrimeSquares.GoldbachScaledCutoff
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
open MeasureTheory FourierTransform
open scoped SchwartzMap
namespace PrimeSquares

theorem goldbach_eta_real (ψ : 𝓢(ℝ,ℝ)) (x : ℝ) : (goldbachEta ψ x).im=0 := by
  simp only [goldbachEta,smul_apply,smul_eq_mul,goldbach_autocorrelation_integral,
    ←Complex.ofReal_inv,←Complex.ofReal_mul,Complex.ofReal_im]

theorem goldbach_eta_even (ψ : 𝓢(ℝ,ℝ)) (x : ℝ) : goldbachEta ψ (-x)=goldbachEta ψ x := by
  have he : goldbachAutocorrelation ψ (-x)=goldbachAutocorrelation ψ x := by
    simp only [goldbach_autocorrelation_integral,sub_neg_eq_add]
    congr 1
    have ht := integral_sub_right_eq_self (fun t : ℝ=>ψ t*ψ (t+x)) x (μ:=volume)
    simpa only [sub_add_cancel,mul_comm] using ht.symm
  simp only [goldbachEta,smul_apply,he]

theorem goldbach_autocorrelation_norm (ψ : 𝓢(ℝ,ℝ)) (x : ℝ) :
    ‖goldbachAutocorrelation ψ x‖≤goldbachSeedMass ψ := by
  let g : 𝓢(ℝ,ℝ) := SchwartzMap.compSubConstCLM ℝ x ψ
  have h₁ : Integrable (fun t : ℝ=>ψ t*ψ t) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) ψ ψ).integrable
  have h₂ : Integrable (fun t : ℝ=>ψ (t-x)*ψ (t-x)) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) g g).integrable
  have h₃ : Integrable (fun t : ℝ=>ψ t*ψ (t-x)) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) ψ g).integrable
  have hh : ∀ t : ℝ,‖ψ t*ψ (t-x)‖≤(ψ t*ψ t+ψ (t-x)*ψ (t-x))/2 := by
    intro t
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> nlinarith [sq_nonneg (ψ t-ψ (t-x)),sq_nonneg (ψ t+ψ (t-x))]
  rw [goldbach_autocorrelation_integral,Complex.norm_real]
  calc
    _≤∫ t : ℝ,‖ψ t*ψ (t-x)‖ := norm_integral_le_integral_norm _
    _≤∫ t : ℝ,(ψ t*ψ t+ψ (t-x)*ψ (t-x))/2 :=
      integral_mono h₃.norm ((h₁.add h₂).div_const 2) hh
    _=goldbachSeedMass ψ := by
      rw [integral_div,integral_add h₁ h₂,
        integral_sub_right_eq_self (fun t : ℝ=>ψ t*ψ t) x]
      unfold goldbachSeedMass
      ring

theorem goldbach_eta_norm_le_one (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0) (x : ℝ) :
    ‖goldbachEta ψ x‖≤1 := by
  have hm := goldbach_seed_mass_pos ψ hψ
  simp only [goldbachEta,smul_apply,norm_smul,norm_inv,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hm]
  calc
    _≤(goldbachSeedMass ψ)⁻¹*goldbachSeedMass ψ :=
      mul_le_mul_of_nonneg_left (goldbach_autocorrelation_norm ψ x) (inv_nonneg.mpr hm.le)
    _=1 := inv_mul_cancel₀ hm.ne'

theorem goldbach_eta_deriv_zero (ψ : 𝓢(ℝ,ℝ)) : deriv (goldbachEta ψ) 0=0 := by
  have he : ((goldbachEta ψ : ℝ→ℂ) ∘ Neg.neg)=(goldbachEta ψ : ℝ→ℂ) := funext (goldbach_eta_even ψ)
  have hd := ((goldbachEta ψ).hasDerivAt (-(0:ℝ))).scomp 0 (hasDerivAt_neg (0:ℝ))
  simp only [neg_zero,he,neg_smul,one_smul] at hd
  have heq := hd.unique ((goldbachEta ψ).hasDerivAt 0)
  linear_combination -(1/2:ℂ)*heq

theorem goldbach_schwartz_derivative_difference (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    ‖deriv f x-deriv f 0‖≤
      SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ f))*|x| := by
  let g := SchwartzMap.derivCLM ℝ ℂ f
  simpa only [g,SchwartzMap.derivCLM_apply,sub_zero,Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (Set.univ: Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun t _=>g.differentiableAt)
    (fun t _=>SchwartzMap.norm_le_seminorm ℝ (SchwartzMap.derivCLM ℝ ℂ g) t)
    (Set.mem_univ 0) (Set.mem_univ x)

theorem goldbach_eta_quadratic (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0) (x : ℝ) :
    ‖goldbachEta ψ x-1‖≤
      SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℂ
        (SchwartzMap.derivCLM ℝ ℂ (goldbachEta ψ)))*|x|^2 := by
  let K := SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℂ
    (SchwartzMap.derivCLM ℝ ℂ (goldbachEta ψ)))
  have hK : 0≤K := apply_nonneg _ _
  have hb (t : ℝ) : ‖deriv (goldbachEta ψ) t‖≤K*|t| := by
    simpa only [goldbach_eta_deriv_zero,sub_zero] using
      goldbach_schwartz_derivative_difference (goldbachEta ψ) t
  have hh := (convex_Icc (min 0 x) (max 0 x)).norm_image_sub_le_of_norm_deriv_le
    (fun t _=>(goldbachEta ψ).differentiableAt)
    (C:=K*|x|) (fun t ht=> (hb t).trans (mul_le_mul_of_nonneg_left
      (by rw [abs_le];constructor <;> grind [ht.1,ht.2,le_abs_self x,neg_abs_le x]) hK))
    (by simp : (0:ℝ)∈Set.Icc (min 0 x) (max 0 x))
    (by simp : x∈Set.Icc (min 0 x) (max 0 x))
  simpa only [goldbach_eta_zero ψ hψ,sub_zero,Real.norm_eq_abs,mul_assoc,←pow_two] using hh

theorem goldbach_eta_square_cutoff_bound (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0) :
    ∃ K : ℝ,0<K ∧ ∀ x : ℝ,‖1-goldbachEta ψ x*goldbachEta ψ x‖≤K*min 1 (|x|^2) := by
  let D := SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℂ
    (SchwartzMap.derivCLM ℝ ℂ (goldbachEta ψ)))
  have hD : 0≤D := apply_nonneg _ _
  refine ⟨2*(D+1),by positivity,?_⟩
  intro x
  have hn := goldbach_eta_norm_le_one ψ hψ x
  have hq := goldbach_eta_quadratic ψ hψ x
  have hlin : ‖1-goldbachEta ψ x*goldbachEta ψ x‖≤2*D*|x|^2 := by
    have he : (1:ℂ)-goldbachEta ψ x*goldbachEta ψ x=
        (1-goldbachEta ψ x)*(1+goldbachEta ψ x) := by ring
    rw [he,norm_mul]
    have hs : ‖1+goldbachEta ψ x‖≤2 := (norm_add_le _ _).trans (by rw [norm_one];linarith)
    have hq' : ‖1-goldbachEta ψ x‖≤D*|x|^2 := by simpa only [norm_sub_rev] using hq
    nlinarith [mul_le_mul hq' hs (norm_nonneg _) (by positivity : (0:ℝ)≤D*|x|^2)]
  have hflat : ‖1-goldbachEta ψ x*goldbachEta ψ x‖≤2 :=
    (norm_sub_le _ _).trans (by rw [norm_one,norm_mul];nlinarith [norm_nonneg (goldbachEta ψ x)])
  by_cases hx : |x|^2≤1
  · rw [min_eq_right hx]
    nlinarith [sq_nonneg |x|]
  · rw [min_eq_left (le_of_not_ge hx),mul_one]
    linarith

end PrimeSquares
