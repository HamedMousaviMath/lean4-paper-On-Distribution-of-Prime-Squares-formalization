import PrimeSquares.RealIWHighLowAssembly

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal lp Classical
namespace PrimeSquares

/-- The complete source high-low assertion on actual operator families. The
low bounds include every dyadic scale. High bounds apply above the specified
starting scale and share the same arithmetic construction and Page datum. -/
def RealIWLowHighConclusion {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (C : ℝ) (r k : ℕ) (Q : ℝ) (M : ℕ) (hM : 2 ≤ M)
    (d : TaoArcConstructionData (C^2) (iwRho k) k ⌊Q⌋₊) [NeZero d.period]
    (a : ℝ) (ha : 2 ≤ a) (Kl Kh : ℝ) : Prop :=
  ∃ E₀ : Option PageZeroDatum,
    (∀ E,E₀=some E → E.conductor ≤ ⌊Q⌋₊ ∧ E.conductor ∣ d.period) ∧
    (∀ N (hN : 1≤N),
      annularWeightedSquareAverage (P := 2) (by norm_num) N ArithmeticFunction.vonMangoldt =
        iwPrimeLowOperator D (iwFrequencySet d.S k) N hN a ha E₀ ⌊Q⌋₊+
        iwPrimeHighOperator D (iwFrequencySet d.S k) N hN a ha E₀ ⌊Q⌋₊) ∧
    (∀ N (hN : 1≤N),
      annularWeightedSquareAverage (P := 2) (by norm_num) N (fun _ => 1) =
        iwFullSquareLowOperator d.S k d.period N hN a ha+
        iwFullSquareHighOperator d.S k d.period N hN a ha) ∧
    AllInputLpMaximalBound (fun j => iwPrimeLowOperator D (iwFrequencySet d.S k) ((2:ℕ)^j)
      (one_le_pow₀ (by norm_num)) a ha E₀ ⌊Q⌋₊) (ENNReal.ofReal (iwNearOneExponent r)) Kl ∧
    AllInputLpMaximalBound (fun j => iwFullSquareLowOperator d.S k d.period ((2:ℕ)^j)
      (one_le_pow₀ (by norm_num)) a ha) (ENNReal.ofReal (iwNearOneExponent r)) Kl ∧
    (∀ f : ℓ²(ℤ,ℂ), ∃ gp gs : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,0≤gp x) ∧ (∀ x,0≤gs x) ∧
      (∀ j x,‖iwPrimeHighOperator D (iwFrequencySet d.S k) ((2:ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j; omega) a ha E₀ ⌊Q⌋₊ f x‖ ≤ gp x) ∧
      (∀ j x,‖iwFullSquareHighOperator d.S k d.period ((2:ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j; omega) a ha f x‖ ≤ gs x) ∧
      ‖gp‖+‖gs‖ ≤ Kh*Q^(-(1/4:ℝ))*‖f‖)

theorem real_iw_source_high_low {Cb c E Z R H S : ℝ} (hCb : 0≤Cb)
    (HB : SmoothCircleBourgainInput Cb) (hc : 0<c) (HP : RawPageUniquenessInput c)
    (D : PagePrimeSquareDistributionInputs c) (hE : 0≤E) (HE : RawQuadraticWeylApproximationInput E)
    (hZ : 0≤Z) (hR : 0≤R) (hH : 0≤H) (hS : 0≤S)
    (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (HShannon : RawNarrowShannonInput S)
    (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput) :
    ∃ Cstart Kh : ℝ,0<Cstart ∧ 0<Kh ∧
      ∀ (C : ℝ) (hC : 2≤C), Real.exp 1≤C → RawTaoArcConstructionInput C →
      RawIWMultiplierInput C → RawMajorArcSamplingInput C →
      ∀ (r k : ℕ) (Q : ℝ) (M : ℕ) (hr : 2≤r) (hk : 4≤k) (hQ : (2:ℝ)^k≤Q)
        (hM : 2≤M), Even M →
      Real.exp (Cstart*((Real.log Q)^2+(r:ℝ)*Real.log (realIWDenominatorBound (C^2) k Q)))≤M →
      ∃ d : TaoArcConstructionData (C^2) (iwRho k) k ⌊Q⌋₊,
        (d.period:ℝ)≤(3:ℝ)^Q ∧
        (∀ α : ℚ,α ∈ Set.Ico (0:ℚ) 1 → (α.den:ℝ)≤Q → α ∈ iwFrequencySet d.S k) ∧
        (∀ α ∈ iwFrequencySet d.S k,(α.den:ℝ)≤realIWDenominatorBound (C^2) k Q) ∧
        IWGood r k d.S (realIWWidth (C^2) r k Q) ∧
        (let : NeZero d.period := ⟨d.period_pos.ne'⟩
         RealIWLowHighConclusion D C r k Q M hM d (realIWCutoffScale (C^2) r k Q)
          (by have h := realIWCutoffScale_four_le (by nlinarith : 2≤C^2)
                ((show (0:ℝ)≤(2:ℝ)^k by positivity).trans hQ) hr k
              linarith)
          (4*iwCompleteLowConstant Z R H S*realIWMaximalCost (C^2) r k Q) Kh) := by
  obtain ⟨Cs,Kh,hCs,hKh,hHigh⟩ := real_iw_high_comparison hCb HB hc HP D hE HE
  refine ⟨Cs,Kh,hCs,hKh,?_⟩
  intro C hC hCe HT HIW Hmajor r k Q M hr hk hQ hM hEven hstart
  have hC2 : 2≤C^2 := by nlinarith
  have hCC : C≤C^2 := by nlinarith
  have hQ1 : 1≤Q := (one_le_pow₀ (by norm_num : (1:ℝ)≤2)).trans hQ
  have hQ0 : 0≤Q := by linarith
  have hT := rawTaoArcConstructionInput_mono_base (by linarith : 0≤C) hCC HT
  obtain ⟨d,hP,hcover,hden,_,hgood⟩ := quantitative_iw_real_construction_good hC2 hT hr hk hQ
  let : NeZero d.period := ⟨d.period_pos.ne'⟩
  have ha : 2≤realIWCutoffScale (C^2) r k Q :=
    (by norm_num : (2:ℝ)≤4).trans (realIWCutoffScale_four_le hC2 hQ0 hr k)
  obtain ⟨E₀,hsmall,hhigh⟩ := hHigh (C^2) hC2 (hCe.trans hCC) r k Q M hr hk hQ hM hEven d hstart
  have hprime := real_iw_prime_low_maximal_bound D hC hCe hQ1 hZ hR hH hS HIW HCZ HY HRM Hmajor
    HShannon HHL HRT hr hk d E₀ (fun E hE => (hsmall E hE).1) ha
  have hsquare := real_iw_full_square_low_maximal_bound hC hCe hQ1 hZ hR hH hS HIW HCZ HY HRM Hmajor
    HShannon HHL HRT hr hk d ha
  have hsquare' := allInputLpMaximalBound_mono_constant hsquare
    (by have hc0 := realIWMaximalCost_nonneg hC2 hQ1 r k
        have hK := (iwCompleteLowConstant_pos hZ hR hH hS).le
        nlinarith : 2*iwCompleteLowConstant Z R H S*realIWMaximalCost (C^2) r k Q ≤
          4*iwCompleteLowConstant Z R H S*realIWMaximalCost (C^2) r k Q)
  refine ⟨d,hP,hcover,hden,hgood,?_⟩
  dsimp only
  refine ⟨E₀,hsmall,?_,?_,hprime,hsquare',hhigh⟩
  · intro N hN
    exact iwPrime_decomposition D (iwFrequencySet d.S k) N hN _ ha E₀ ⌊Q⌋₊
  · intro N hN
    exact iwFullSquare_decomposition d.S k d.period N hN _ ha

end PrimeSquares
