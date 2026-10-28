import PrimeSquares.IWQuantitativeModelComparison
import PrimeSquares.IWFixedSmallCharacter

set_option autoImplicit false
open scoped lp
namespace PrimeSquares

theorem rationalPrincipalGauss_norm_one (t : ℚ) : ‖rationalPrincipalGauss t‖≤1 := by
  have : NeZero t.den := ⟨t.den_pos.ne'⟩
  simpa only [rationalPrincipalGauss,twistedSquareSum_principal] using
    norm_twistedSquareSum_le_one t.den 1 (t.num : ZMod t.den)

theorem rationalInducedSquareCoefficient_norm_one (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℚ) :
    ‖rationalInducedSquareCoefficient q χ t‖≤1 := by
  classical
  have : NeZero t.den := ⟨t.den_pos.ne'⟩
  unfold rationalInducedSquareCoefficient
  split_ifs
  · exact norm_twistedSquareSum_le_one t.den (sourceInducedCharacter q χ t) (t.num : ZMod t.den)
  · simp only [norm_zero]
    norm_num

theorem rationalInducedSquareCoefficient_uniform_decay {δ : ℝ} (hδ : δ<1/2) :
    ∃ A : ℝ,0<A ∧ ∀ t : ℚ,‖rationalPrincipalGauss t‖≤A*(t.den : ℝ)^(-δ) ∧
      ∀ q : ℕ,∀ χ : DirichletCharacter ℂ q,
        ‖rationalInducedSquareCoefficient q χ t‖≤A*(t.den : ℝ)^(-δ) := by
  classical
  obtain ⟨A,hA,hGauss⟩ := rationalGauss_uniform_decay hδ
  refine ⟨A,hA,fun t => ⟨(hGauss t).1,?_⟩⟩
  intro q χ
  unfold rationalInducedSquareCoefficient
  split_ifs
  · exact (hGauss t).2 _
  · simp only [norm_zero]
    positivity

/-- Both low-model measures are actual cyclic square measures. The original
and IW symbols, coefficients, phases and beta values are all fixed here. -/
theorem iw_character_model_comparisons {Cb : ℝ} (hCb : 0≤Cb)
    (HB : SmoothCircleBourgainInput Cb) :
    ∃ K : ℝ,0<K ∧ ∀ (C : ℝ) (hC : 2≤C) (r k Q M : ℕ) (hr : 2≤r) (_hk : 4≤k)
      (_hQ : 2^k≤Q) (hM : 2≤M) (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period],
      ((Q : ℝ)+1)^2*iwCutoffScale C r k Q*(Q : ℝ)≤(M : ℝ)^2 →
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (_hχ : χ.IsPrimitive) (hq : 2≤q) (hqQ : q≤Q)
        (β : ℕ → ℝ),(∀ j,0≤β j) → (∀ j,β j≤1) →
      ∀ (R : ℕ → ℝ),(∀ j,(Q : ℝ)≤R j) → ∀ f : ℓ²(ℤ,ℂ),
      ∃ g₀ gχ : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g₀ x ∧ 0≤gχ x) ∧
        (∀ j x,‖integerMultiplier
          (varyingIndexAnnularBlock (sourceRationalCenters (R j)) ((2 : ℕ)^j*M)
            (by have h := dyadic_annular_scale_lower hM j;omega) 1 rationalPrincipalGauss-
          weightedWidthAnnularBlock (iwFrequencySet d.S k) ((2 : ℕ)^j*M)
            (by have h := dyadic_annular_scale_lower hM j;omega) 1 (iwCutoffScale C r k Q)
            (by have h := iwCutoffScale_four_le hC hr k Q;linarith)
            (cyclicRationalCoefficient d.period (cyclicSquareMeasure d.period 1))) f x‖≤g₀ x) ∧
        (∀ j x,‖integerMultiplier
          (varyingIndexAnnularBlock (sourceRationalCenters (R j)) ((2 : ℕ)^j*M)
            (by have h := dyadic_annular_scale_lower hM j;omega) (β j) (rationalInducedSquareCoefficient q χ)-
          weightedWidthAnnularBlock (iwFrequencySet d.S k) ((2 : ℕ)^j*M)
            (by have h := dyadic_annular_scale_lower hM j;omega) (β j) (iwCutoffScale C r k Q)
            (by have h := iwCutoffScale_four_le hC hr k Q;linarith)
            (cyclicRationalCoefficient d.period (cyclicSquareMeasure d.period
              (DirichletCharacter.changeLevel (iw_period_divisible_small d hq hqQ) χ)))) f x‖≤gχ x) ∧
        ‖g₀‖≤K*(Q : ℝ)^(-(1/4 : ℝ))*‖f‖ ∧ ‖gχ‖≤K*(Q : ℝ)^(-(1/4 : ℝ))*‖f‖ := by
  obtain ⟨A,hA,hGauss⟩ := rationalInducedSquareCoefficient_uniform_decay (by norm_num : (3/8 : ℝ)<1/2)
  let K := 2*annularPowerConstant Cb (1/8)*A+24/Real.pi
  have hK : 0<K := by
    have hP := annularPowerConstant_pos hCb (1/8)
    dsimp [K]
    positivity
  refine ⟨K,hK,?_⟩
  intro C hC r k Q M hr hk hQ hM d inst hbudget q χ hχ hq hqQ β hβ0 hβ1 R hR f
  obtain ⟨g₀,hg₀,ht₀,hn₀⟩ := iw_quantitative_model_comparison hC hCb HB hA.le hr hk hQ hM d hbudget
    (fun _ => 1) (fun _ => by norm_num) (fun _ => le_rfl) rationalPrincipalGauss
    (fun t _ => (hGauss t).1) (fun t _ => rationalPrincipalGauss_norm_one t) R hR f
  obtain ⟨gχ,hgχ,htχ,hnχ⟩ := iw_quantitative_model_comparison hC hCb HB hA.le hr hk hQ hM d hbudget
    β hβ0 hβ1 (rationalInducedSquareCoefficient q χ) (fun t _ => (hGauss t).2 q χ)
    (fun t _ => rationalInducedSquareCoefficient_norm_one q χ t) R hR f
  refine ⟨g₀,gχ,fun x => ⟨hg₀ x,hgχ x⟩,?_,?_,hn₀,hnχ⟩
  · intro j x
    rw [iw_principal_width_symbol]
    exact ht₀ j x
  · intro j x
    rw [iw_induced_width_symbol d (iw_period_divisible_small d hq hqQ) χ hχ]
    exact htχ j x

end PrimeSquares
