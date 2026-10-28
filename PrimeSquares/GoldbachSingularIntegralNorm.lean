import PrimeSquares.GoldbachSingularIntegralPositive

set_option autoImplicit false
open MeasureTheory
open scoped SchwartzMap
namespace PrimeSquares

noncomputable def goldbachEuclideanL1Constant : ℝ :=
  2/(Real.log 2)^2+4*goldbachEuclideanDecayConstant

theorem goldbachEuclideanL1Constant_pos : 0<goldbachEuclideanL1Constant := by
  have := goldbachEuclideanDecayConstant_pos
  unfold goldbachEuclideanL1Constant
  positivity

theorem goldbach_euclidean_product_integrable (N ℓ : ℕ) (hN : 0<N) (hℓ : 0<ℓ)
    {U W : ℝ} (hU : 2≤U) (hUN : U≤N) (hW : 2≤W) (hX : 2≤(N:ℝ)^2/ℓ) :
    Integrable (fun γ=>goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ) ∧
      (∫ γ : ℝ,‖goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ‖)≤
        goldbachEuclideanL1Constant*(N:ℝ)/(ℓ:ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hl : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  let c := 1/(N:ℝ)^2
  have hc : 0<c := by dsimp [c];positivity
  have hs : Real.sqrt c=1/(N:ℝ) := by
    dsimp [c]
    rw [Real.sqrt_div zero_le_one,Real.sqrt_one,Real.sqrt_sq_eq_abs,abs_of_pos hn]
  have hi := goldbach_two_sided_integrable_decay
    (fun γ=>goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ)
    ((goldbachSquareIntegral_stronglyMeasurable U).mul (goldbachLinearSourceIntegral_stronglyMeasurable N ℓ hℓ W))
    hc (div_nonneg goldbachEuclideanDecayConstant_pos.le hl.le)
    (M:=(N:ℝ)^3/((ℓ:ℝ)*(Real.log 2)^2))
    (fun γ _=>goldbach_euclidean_product_flat N ℓ hℓ hU hUN hW hX γ)
    (fun γ hγ=>goldbach_euclidean_product_decay N ℓ hℓ hU hW hX
      (by have hh : 0 < |γ| := hc.trans hγ;exact abs_pos.mp hh))
  refine ⟨hi.1,hi.2.trans_eq ?_⟩
  rw [hs]
  dsimp only [c,goldbachEuclideanL1Constant]
  field_simp

theorem goldbach_singular_integrand_norm (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (N ℓ : ℕ) (R n U W γ : ℝ) :
    ‖(goldbachEta ψ ((N:ℝ)^2*γ/R))^2*goldbachSquareIntegral U γ*
      goldbachLinearSourceIntegral N ℓ W γ*realFourierPhase (-n*γ)‖≤
      ‖goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ‖ := by
  rw [mul_assoc ((goldbachEta ψ ((N:ℝ)^2*γ/R))^2),norm_mul,realFourierPhase_norm,mul_one,
    norm_mul,norm_pow]
  have hn := goldbach_eta_norm_le_one ψ hψ ((N:ℝ)^2*γ/R)
  exact mul_le_of_le_one_left (norm_nonneg _)
    (by nlinarith [norm_nonneg (goldbachEta ψ ((N:ℝ)^2*γ/R))])

theorem goldbach_singular_integrand_integrable (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (N ℓ : ℕ) (hN : 0<N) (hℓ : 0<ℓ) {U W : ℝ}
    (hU : 2≤U) (hUN : U≤N) (hW : 2≤W) (hX : 2≤(N:ℝ)^2/ℓ) (R n : ℝ) :
    Integrable (fun γ=>(goldbachEta ψ ((N:ℝ)^2*γ/R))^2*goldbachSquareIntegral U γ*
      goldbachLinearSourceIntegral N ℓ W γ*realFourierPhase (-n*γ)) := by
  have hη : StronglyMeasurable (fun γ : ℝ=>(goldbachEta ψ ((N:ℝ)^2*γ/R))^2) :=
    (((goldbachEta ψ).continuous.comp (by fun_prop)).pow 2).stronglyMeasurable
  have hph : StronglyMeasurable (fun γ : ℝ=>realFourierPhase (-n*γ)) :=
    (realFourierPhase_continuous.comp (by fun_prop)).stronglyMeasurable
  exact (goldbach_euclidean_product_integrable N ℓ hN hℓ hU hUN hW hX).1.norm.mono'
    (((hη.mul (goldbachSquareIntegral_stronglyMeasurable U)).mul
      (goldbachLinearSourceIntegral_stronglyMeasurable N ℓ hℓ W)).mul hph).aestronglyMeasurable
    (Filter.Eventually.of_forall (goldbach_singular_integrand_norm ψ hψ N ℓ R n U W))

theorem goldbach_singular_integral_norm (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (N ℓ : ℕ) (hN : 0<N) (hℓ : 0<ℓ) {U W : ℝ}
    (hU : 2≤U) (hUN : U≤N) (hW : 2≤W) (R n : ℝ) :
    ‖goldbachSingularIntegral ψ N ℓ R n U W‖≤goldbachEuclideanL1Constant*(N:ℝ) := by
  by_cases hX : 2≤(N:ℝ)^2/ℓ
  · have hl : (0:ℝ)<ℓ := by exact_mod_cast hℓ
    have hI := goldbach_euclidean_product_integrable N ℓ hN hℓ hU hUN hW hX
    have hJ := goldbach_singular_integrand_integrable ψ hψ N ℓ hN hℓ hU hUN hW hX R n
    unfold goldbachSingularIntegral
    rw [norm_mul,Complex.norm_natCast]
    apply (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hl.le).trans
    apply (mul_le_mul_of_nonneg_left (integral_mono hJ.norm hI.1.norm
      (goldbach_singular_integrand_norm ψ hψ N ℓ R n U W)) hl.le).trans
    apply (mul_le_mul_of_nonneg_left hI.2 hl.le).trans_eq
    field_simp
  · rw [goldbach_singular_integral_empty ψ N ℓ hℓ (le_of_not_ge hX),norm_zero]
    exact mul_nonneg goldbachEuclideanL1Constant_pos.le (Nat.cast_nonneg _)

end PrimeSquares
