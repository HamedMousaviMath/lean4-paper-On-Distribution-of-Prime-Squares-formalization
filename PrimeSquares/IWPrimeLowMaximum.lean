import PrimeSquares.IWFullLowMaximum
import PrimeSquares.IntegerLpMeasureBridge
import PrimeSquares.IWPrimeHighSourceScale

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal lp Classical
namespace PrimeSquares

theorem iwPrimeLowOperator_none {c C ρ : ℝ} (D : PagePrimeSquareDistributionInputs c)
    {k Q : ℕ} (d : TaoArcConstructionData C ρ k Q) [NeZero d.period]
    (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 2 ≤ a) :
    iwPrimeLowOperator D (iwFrequencySet d.S k) N hN a ha none Q =
      iwAnnularLowOperator d.S k d.period (cyclicSquareMeasure d.period 1) N hN 1 a ha := by
  unfold iwPrimeLowOperator pageIWLowSymbol fixedPageIWSymbol
  simp only [Option.elim_none, sub_zero]
  rw [←iw_principal_width_symbol d N hN 1 a ha]
  rfl

theorem iwPrimeLowOperator_some {c C ρ : ℝ} (D : PagePrimeSquareDistributionInputs c)
    {k Q : ℕ} (d : TaoArcConstructionData C ρ k Q) [NeZero d.period]
    (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 2 ≤ a) (E : PageZeroDatum) (hE : E.conductor ≤ Q) :
    iwPrimeLowOperator D (iwFrequencySet d.S k) N hN a ha (some E) Q =
      iwAnnularLowOperator d.S k d.period (cyclicSquareMeasure d.period 1) N hN 1 a ha -
        (if sourcePageDatum D N Q = some E then
          iwAnnularLowOperator d.S k d.period
            (cyclicSquareMeasure d.period (DirichletCharacter.changeLevel
              (iw_period_divisible_small d E.conductor_two hE) E.character)) N hN E.beta a ha
        else 0) := by
  unfold iwPrimeLowOperator pageIWLowSymbol
  rw [fixedPageIWSymbol_actual_measure d N hN a ha E hE,
    ←iw_principal_width_symbol d N hN 1 a ha]
  by_cases he : sourcePageDatum D N Q = some E
  · simp only [ite_eq_left he]
    rw [integerMultiplier_sub]
    rfl
  · simp only [ite_eq_right he, sub_zero]
    rfl

theorem iwPrimeLowOperator_some_norm {c C ρ : ℝ} (D : PagePrimeSquareDistributionInputs c)
    {k Q : ℕ} (d : TaoArcConstructionData C ρ k Q) [NeZero d.period]
    (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 2 ≤ a) (E : PageZeroDatum) (hE : E.conductor ≤ Q)
    (f : ℓ²(ℤ,ℂ)) (x : ℤ) :
    ‖iwPrimeLowOperator D (iwFrequencySet d.S k) N hN a ha (some E) Q f x‖ ≤
      ‖iwAnnularLowOperator d.S k d.period (cyclicSquareMeasure d.period 1) N hN 1 a ha f x‖ +
        ‖iwAnnularLowOperator d.S k d.period
          (cyclicSquareMeasure d.period (DirichletCharacter.changeLevel
            (iw_period_divisible_small d E.conductor_two hE) E.character)) N hN E.beta a ha f x‖ := by
  rw [iwPrimeLowOperator_some D d N hN a ha E hE]
  by_cases he : sourcePageDatum D N Q = some E
  · simp only [ite_eq_left he, _root_.sub_apply, lp.coeFn_sub, Pi.sub_apply]
    exact norm_sub_le _ _
  · simp only [ite_eq_right he, sub_zero]
    exact le_add_of_nonneg_right (norm_nonneg _)

theorem iw_prime_finite_low_majorant {c C Z R H S : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k) (hQ : 1 ≤ Q)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (E₀ : Option PageZeroDatum) (hsmall : ∀ E, E₀ = some E → E.conductor ≤ Q)
    (F : Finset ℤ) (f : ℤ → ℂ) (ha : 2 ≤ iwCutoffScale C r k Q) :
    ∃ G : ℤ → ℝ, (∀ x, 0 ≤ G x) ∧ MemLp G (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
      (∀ j x, ‖iwPrimeLowOperator D (iwFrequencySet d.S k) ((2 : ℕ)^j) (one_le_pow₀ (by norm_num))
        (iwCutoffScale C r k Q) ha E₀ Q (finiteInputLp F f 2) x‖ ≤ G x) ∧
      eLpNorm G (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ≤
        ENNReal.ofReal (2*iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q)*
          eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  have hpR : 0 < (ENNReal.ofReal (iwNearOneExponent r)).toReal := by
    rw [ENNReal.toReal_ofReal (by linarith [(iwNearOneExponent_bounds hr).1] : 0 ≤ iwNearOneExponent r)]
    linarith [(iwNearOneExponent_bounds hr).1]
  have hf := finiteInputLp_count_memLp F f hpR
  have hLow := iw_finite_input_low_majorant hC hCe hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
    hr hk hQ d
  obtain ⟨GP, hGP0, hGPm, hGPdom, hGPnorm⟩ := hLow (cyclicSquareMeasure d.period 1)
    (cyclicSquareMeasure_variation_le_one d.period 1) (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1)
    F f hf ha
  have hKD : 0 ≤ iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q :=
    mul_nonneg (iwCompleteLowConstant_pos hZ hR hH hS).le
      ((by positivity : 0 ≤ (r : ℝ)*(iwMultiplierConstant C r k)^2).trans (iwMaximalCost_lower_bounds hC hr k Q).1)
  cases E₀ with
  | none =>
    refine ⟨GP, hGP0, hGPm, ?_, hGPnorm.trans ?_⟩
    · intro j x
      rw [iwPrimeLowOperator_none D d]
      exact hGPdom j x
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by nlinarith :
        iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q ≤
          2*iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q)) _
  | some E =>
    have hE := hsmall E rfl
    let χ := DirichletCharacter.changeLevel (iw_period_divisible_small d E.conductor_two hE) E.character
    obtain ⟨GE, hGE0, hGEm, hGEdom, hGEnorm⟩ := hLow (cyclicSquareMeasure d.period χ)
      (cyclicSquareMeasure_variation_le_one d.period χ) E.beta_pos E.beta_lt_one.le F f hf ha
    refine ⟨fun x => GP x+GE x, fun x => add_nonneg (hGP0 x) (hGE0 x),
      (hGPm.add hGEm).ae_eq (Filter.Eventually.of_forall (fun _ => rfl)), ?_, ?_⟩
    · intro j x
      exact (iwPrimeLowOperator_some_norm D d ((2 : ℕ)^j) (one_le_pow₀ (by norm_num))
        (iwCutoffScale C r k Q) ha E hE (finiteInputLp F f 2) x).trans
          (add_le_add (hGPdom j x) (hGEdom j x))
    · change eLpNorm (GP+GE) _ _ ≤ _
      calc
        _ ≤ eLpNorm GP _ _+eLpNorm GE _ _ := eLpNorm_add_le (by
          rw [←ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (iwNearOneExponent_bounds hr).1.le)
        _ ≤ ENNReal.ofReal (iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q)*
              eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) _ _+
            ENNReal.ofReal (iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q)*
              eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) _ _ := add_le_add hGPnorm hGEnorm
        _ = _ := by
          rw [←add_mul, ←ENNReal.ofReal_add hKD hKD]
          congr 2
          ring

end PrimeSquares
