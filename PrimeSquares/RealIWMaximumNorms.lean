import PrimeSquares.RealIWSourceHighLow

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal lp
namespace PrimeSquares

/-- Realization of the literal countable maximum on every integer lp input. -/
theorem allInputLpMaximalBound_integerLp_maximum
    (T : ℕ → (ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ))) {p : ℝ≥0∞}
    (hp : 0<p.toReal) (hp2 : p≤2) {K : ℝ} (hK : 0≤K)
    (H : AllInputLpMaximalBound T p K) (f : ℓ^p(ℤ,ℂ)) :
    ∃ G : ℓ^p(ℤ,ℝ),
      (∀ x,G x=countableCoordinateMaximum
        (fun j x => T j (lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) hp2 f) x) x) ∧
      ‖G‖≤K*‖f‖ := by
  let f2 : ℓ²(ℤ,ℂ) := lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) hp2 f
  have hf : MemLp (f2:ℤ→ℂ) p Measure.count := count_memLp_of_memℓp hp (lp.memℓp f)
  obtain ⟨hm,hn⟩ := allInputLpMaximalBound_maximum T H f2 hf
  let G : ℓ^p(ℤ,ℝ) := ⟨countableCoordinateMaximum (fun j x => T j f2 x),memℓp_of_count_memLp hp hm⟩
  have hG : eLpNorm (countableCoordinateMaximum (fun j x => T j f2 x)) p Measure.count =
      ENNReal.ofReal ‖G‖ := eLpNorm_count_eq_lp_enorm hp G
  have hF : eLpNorm (f2:ℤ→ℂ) p Measure.count=ENNReal.ofReal ‖f‖ := eLpNorm_count_eq_lp_enorm hp f
  rw [hG,hF,←ENNReal.ofReal_mul hK] at hn
  exact ⟨G,fun _ => rfl,(ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK (lp.norm_nonneg' f))).mp hn⟩

theorem allInputLp_two_maximum_norms
    (T U : ℕ → (ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ))) {p : ℝ≥0∞}
    (hp : 0<p.toReal) (hp2 : p≤2) {K L : ℝ} (hK : 0≤K) (hL : 0≤L)
    (HT : AllInputLpMaximalBound T p K) (HU : AllInputLpMaximalBound U p L)
    (f : ℓ^p(ℤ,ℂ)) :
    ∃ G₁ G₂ : ℓ^p(ℤ,ℝ),
      (∀ x,G₁ x=countableCoordinateMaximum
        (fun j x => T j (lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) hp2 f) x) x) ∧
      (∀ x,G₂ x=countableCoordinateMaximum
        (fun j x => U j (lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) hp2 f) x) x) ∧
      ‖G₁‖+‖G₂‖≤(K+L)*‖f‖ := by
  obtain ⟨G₁,h₁,hn₁⟩ := allInputLpMaximalBound_integerLp_maximum T hp hp2 hK HT f
  obtain ⟨G₂,h₂,hn₂⟩ := allInputLpMaximalBound_integerLp_maximum U hp hp2 hL HU f
  exact ⟨G₁,G₂,h₁,h₂,(add_le_add hn₁ hn₂).trans_eq (by ring)⟩

theorem real_iw_two_low_maximum_norms {c C Q Z R H S : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (hC : 2≤C) (hCe : Real.exp 1≤C) (hQ : 1≤Q)
    (hZ : 0≤Z) (hR : 0≤R) (hH : 0≤H) (hS : 0≤S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    {r k : ℕ} (hr : 2≤r) (hk : 4≤k)
    (d : TaoArcConstructionData (C^2) (iwRho k) k ⌊Q⌋₊) [NeZero d.period]
    (E₀ : Option PageZeroDatum) (hsmall : ∀ E,E₀=some E → E.conductor≤⌊Q⌋₊)
    (ha : 2≤realIWCutoffScale (C^2) r k Q)
    (f : ℓ^(ENNReal.ofReal (iwNearOneExponent r))(ℤ,ℂ)) :
    ∃ Gp Gs : ℓ^(ENNReal.ofReal (iwNearOneExponent r))(ℤ,ℝ),
      (∀ x,Gp x=countableCoordinateMaximum (fun j x =>
        iwPrimeLowOperator D (iwFrequencySet d.S k) ((2:ℕ)^j) (one_le_pow₀ (by norm_num))
          (realIWCutoffScale (C^2) r k Q) ha E₀ ⌊Q⌋₊
          (lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) (iwNearOneExponent_ennreal_le_two hr) f) x) x) ∧
      (∀ x,Gs x=countableCoordinateMaximum (fun j x =>
        iwFullSquareLowOperator d.S k d.period ((2:ℕ)^j) (one_le_pow₀ (by norm_num))
          (realIWCutoffScale (C^2) r k Q) ha
          (lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) (iwNearOneExponent_ennreal_le_two hr) f) x) x) ∧
      ‖Gp‖+‖Gs‖≤6*iwCompleteLowConstant Z R H S*realIWMaximalCost (C^2) r k Q*‖f‖ := by
  have hP := real_iw_prime_low_maximal_bound D hC hCe hQ hZ hR hH hS HIW HCZ HY HRM Hmajor
    HShannon HHL HRT hr hk d E₀ hsmall ha
  have hSqr := real_iw_full_square_low_maximal_bound hC hCe hQ hZ hR hH hS HIW HCZ HY HRM Hmajor
    HShannon HHL HRT hr hk d ha
  have hcost := realIWMaximalCost_nonneg (by nlinarith : 2≤C^2) hQ r k
  have hA := (iwCompleteLowConstant_pos hZ hR hH hS).le
  have h := allInputLp_two_maximum_norms _ _ (iwNearOneExponent_toReal_pos hr)
    (iwNearOneExponent_ennreal_le_two hr)
    (mul_nonneg (mul_nonneg (by norm_num) hA) hcost)
    (mul_nonneg (mul_nonneg (by norm_num) hA) hcost) hP hSqr f
  obtain ⟨Gp,Gs,hp,hs,hn⟩ := h
  exact ⟨Gp,Gs,hp,hs,hn.trans_eq (by ring)⟩

end PrimeSquares
