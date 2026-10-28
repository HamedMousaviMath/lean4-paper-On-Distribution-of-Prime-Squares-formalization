import PrimeSquares.GoldbachEuclideanDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

noncomputable def goldbachEuclideanDecayConstant : ℝ :=
  (2*quadraticIntegralConstant/Real.log 2)*(1/(Real.pi*Real.log 2))

theorem goldbachEuclideanDecayConstant_pos : 0<goldbachEuclideanDecayConstant := by
  have hc := quadraticIntegralConstant_one_le
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold goldbachEuclideanDecayConstant
  positivity

theorem goldbachLinearSourceIntegral_norm_scale (N ℓ : ℕ) (hℓ : 0<ℓ)
    {W : ℝ} (hW : 2≤W) (hX : 2≤(N:ℝ)^2/ℓ) (γ : ℝ) :
    ‖goldbachLinearSourceIntegral N ℓ W γ‖≤(N:ℝ)^2/((ℓ:ℝ)*Real.log 2) := by
  rw [goldbach_linear_source_integral N ℓ hℓ W γ]
  calc
    _≤min W ((N:ℝ)^2/ℓ)/Real.log 2 := goldbachLinearIntegral_norm (le_min hW hX) _
    _≤((N:ℝ)^2/ℓ)/Real.log 2 :=
      div_le_div_of_nonneg_right (min_le_right _ _) (Real.log_pos (by norm_num)).le
    _=_ := by ring

theorem goldbach_euclidean_product_flat (N ℓ : ℕ) (hℓ : 0<ℓ) {U W : ℝ}
    (hU : 2≤U) (hUN : U≤N) (hW : 2≤W) (hX : 2≤(N:ℝ)^2/ℓ) (γ : ℝ) :
    ‖goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ‖≤
      (N:ℝ)^3/((ℓ:ℝ)*(Real.log 2)^2) := by
  have hI : ‖goldbachSquareIntegral U γ‖≤(N:ℝ)/Real.log 2 :=
    (goldbachSquareIntegral_norm hU γ).trans
      (div_le_div_of_nonneg_right hUN (Real.log_pos (by norm_num)).le)
  rw [norm_mul]
  apply (mul_le_mul hI (goldbachLinearSourceIntegral_norm_scale N ℓ hℓ hW hX γ)
    (norm_nonneg _) (by positivity)).trans_eq
  ring

theorem goldbach_inverse_sqrt_power {t : ℝ} (ht : 0<t) :
    (Real.sqrt t*t)⁻¹=t^(-(3/2:ℝ)) := by
  calc
    _=(t^(1/2:ℝ)*t^(1:ℝ))⁻¹ := by rw [Real.rpow_one,Real.sqrt_eq_rpow]
    _=(t^((1/2:ℝ)+1))⁻¹ := by rw [Real.rpow_add ht]
    _=_ := by rw [←Real.rpow_neg ht.le];congr 1;ring

theorem goldbach_euclidean_product_decay (N ℓ : ℕ) (hℓ : 0<ℓ) {U W γ : ℝ}
    (hU : 2≤U) (hW : 2≤W) (hX : 2≤(N:ℝ)^2/ℓ) (hγ : γ≠0) :
    ‖goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ‖≤
      (goldbachEuclideanDecayConstant/(ℓ:ℝ))*|γ|^(-(3/2:ℝ)) := by
  rw [norm_mul]
  calc
    _≤((2*quadraticIntegralConstant/Real.log 2)/Real.sqrt |γ|)*
        ((1/(Real.pi*Real.log 2))/((ℓ:ℝ)*|γ|)) :=
      mul_le_mul (goldbachSquareIntegral_decay hU hγ)
        (goldbachLinearSourceIntegral_decay N ℓ hℓ hW hX hγ)
        (norm_nonneg _) (by have := quadraticIntegralConstant_one_le;positivity)
    _=(goldbachEuclideanDecayConstant/(ℓ:ℝ))*(Real.sqrt |γ| * |γ|)⁻¹ := by
      unfold goldbachEuclideanDecayConstant
      ring
    _=_ := by rw [goldbach_inverse_sqrt_power (abs_pos.mpr hγ)]

theorem goldbach_euclidean_product_tail (N ℓ : ℕ) (hℓ : 0<ℓ) {U W c σ : ℝ}
    (hU : 2≤U) (hW : 2≤W) (hX : 2≤(N:ℝ)^2/ℓ) (hc : 0<c) (hσ : |σ|=1) :
    IntegrableOn (fun γ => goldbachSquareIntegral U (σ*γ)*goldbachLinearSourceIntegral N ℓ W (σ*γ))
      (Set.Ioi c) ∧
    (∫ γ in Set.Ioi c,‖goldbachSquareIntegral U (σ*γ)*goldbachLinearSourceIntegral N ℓ W (σ*γ)‖)≤
      (2*goldbachEuclideanDecayConstant/(ℓ:ℝ))/Real.sqrt c := by
  have hs : σ≠0 := by intro hz;rw [hz,abs_zero] at hσ;norm_num at hσ
  have hsm : StronglyMeasurable (fun γ => goldbachSquareIntegral U (σ*γ)*
      goldbachLinearSourceIntegral N ℓ W (σ*γ)) :=
    ((goldbachSquareIntegral_stronglyMeasurable U).comp_measurable (by fun_prop)).mul
      ((goldbachLinearSourceIntegral_stronglyMeasurable N ℓ hℓ W).comp_measurable (by fun_prop))
  have hB : 0≤goldbachEuclideanDecayConstant/(ℓ:ℝ) := by
    exact div_nonneg goldbachEuclideanDecayConstant_pos.le (Nat.cast_nonneg _)
  have hpow := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3/2:ℝ))< -1) hc).const_mul
    (goldbachEuclideanDecayConstant/(ℓ:ℝ))
  have hb : ∀ᵐ γ ∂volume.restrict (Set.Ioi c),
      ‖goldbachSquareIntegral U (σ*γ)*goldbachLinearSourceIntegral N ℓ W (σ*γ)‖≤
        (goldbachEuclideanDecayConstant/(ℓ:ℝ))*γ^(-(3/2:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with γ hγ
    have hγ0 : 0<γ := hc.trans hγ
    simpa only [abs_mul,hσ,one_mul,abs_of_pos hγ0] using
      goldbach_euclidean_product_decay N ℓ hℓ hU hW hX (mul_ne_zero hs hγ0.ne')
  have hi := hpow.mono' hsm.aestronglyMeasurable hb
  refine ⟨hi,?_⟩
  calc
    _≤∫ γ in Set.Ioi c,(goldbachEuclideanDecayConstant/(ℓ:ℝ))*γ^(-(3/2:ℝ)) :=
      integral_mono_ae hi.norm hpow hb
    _=_ := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-(3/2:ℝ))< -1) hc,
        show (-(3/2:ℝ))+1= -(1/2:ℝ) by norm_num,Real.rpow_neg hc.le,←Real.sqrt_eq_rpow]
      ring

end PrimeSquares
