import PrimeSquares.IWNarrowCountableMaximum
import PrimeSquares.IWShortTransitionMaximum
import PrimeSquares.IWRemainderMaximum

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal lp
namespace PrimeSquares

noncomputable def iwCompleteLowConstant (Z R H S : ℝ) : ℝ :=
  iwFiniteLowConstant Z R + iwNarrowLowConstant H S + 2*annularRemainderConstant

theorem iwCompleteLowConstant_pos {Z R H S : ℝ}
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S) :
    0 < iwCompleteLowConstant Z R H S := by
  have hfin := iwFiniteLowConstant_nonneg hZ hR
  have hnar := iwNarrowLowConstant_nonneg hH hS
  have hrem := annularRemainderConstant_pos
  unfold iwCompleteLowConstant
  linarith

theorem iwMaximalCost_lower_bounds {C : ℝ} (hC : 2 ≤ C) {r : ℕ} (hr : 2 ≤ r)
    (k Q : ℕ) :
    (r : ℝ)*(iwMultiplierConstant C r k)^2 ≤ iwMaximalCost C r k Q ∧
      (r : ℝ)*iwMultiplierConstant C r k ≤ iwMaximalCost C r k Q := by
  have hlB : 0 ≤ Real.log (iwDenominatorBound C k Q) :=
    Real.log_nonneg (iwDenominatorBound_one_le hC k Q)
  have hL : 1 ≤ Real.log (Real.exp 1+(Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q)) := by
    have harg : Real.exp 1 ≤ Real.exp 1+(Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q) := by
      have hmul := mul_nonneg (Nat.cast_nonneg (α := ℝ) r) hlB
      have hq := Nat.cast_nonneg (α := ℝ) Q
      linarith
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) harg
  have hC1 := iwMultiplierConstant_one_le hC hr k
  have hC0 : 0 ≤ iwMultiplierConstant C r k := by linarith
  have hr0 := Nat.cast_nonneg (α := ℝ) r
  have hsquare : iwMultiplierConstant C r k ≤ (iwMultiplierConstant C r k)^2 := by nlinarith
  have hbase := le_mul_of_one_le_right (mul_nonneg hr0 (sq_nonneg (iwMultiplierConstant C r k))) hL
  change (r : ℝ)*(iwMultiplierConstant C r k)^2 ≤ iwMaximalCost C r k Q at hbase
  exact ⟨hbase, (mul_le_mul_of_nonneg_left hsquare hr0).trans hbase⟩

theorem integer_operator_difference_bound (A B : ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ))
    (f : ℓ²(ℤ,ℂ)) (x : ℤ) : ‖A f x‖ ≤ ‖B f x‖ + ‖(A-B) f x‖ := by
  have he : (A-B) f x = A f x-B f x := rfl
  rw [he]
  calc
    ‖A f x‖ = ‖B f x+(A f x-B f x)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

theorem iwAnnularLowOperator_scale_congr (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (ν : ZMod P → ℂ) {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (he : N = M)
    (β a : ℝ) (ha : 2 ≤ a) :
    iwAnnularLowOperator S k P ν N hN β a ha = iwAnnularLowOperator S k P ν M hM β a ha := by
  cases he
  rfl

theorem iw_finite_input_low_majorant {C Z R H S : ℝ} (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k) (hQ : 1 ≤ Q)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν ≤ 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (F : Finset ℤ) (f : ℤ → ℂ)
    (hf : MemLp (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count)
    (ha : 2 ≤ iwCutoffScale C r k Q) :
    ∃ G : ℤ → ℝ, (∀ x, 0 ≤ G x) ∧ MemLp G (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
      (∀ j x, ‖iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j) (one_le_pow₀ (by norm_num)) β
        (iwCutoffScale C r k Q) ha (finiteInputLp F f 2) x‖ ≤ G x) ∧
      eLpNorm G (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ≤
        ENNReal.ofReal (iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q)*
          eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  let δ := iwNarrowWidth (iwWidth C r k Q) d.period
  let J := iwTransitionIndex δ
  let L : ℕ → ℓ²(ℤ,ℂ) := fun j => iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j)
    (one_le_pow₀ (by norm_num)) β (iwCutoffScale C r k Q) ha (finiteInputLp F f 2)
  let U := initialTemporalMaximum L J
  have hP : 1 ≤ d.period := by have h := d.period_pos; omega
  have hδ : 0 < δ := iwNarrowWidth_pos (iwWidth_pos hC hr k Q) hP
  have hδsmall : δ ≤ 1/100 := iwNarrowWidth_small _ hP
  have hb := (iwNarrow_inverse_geometry (k := k) (Q := Q) hC hr hP).2.2
  obtain ⟨GN, hGN0, hGNm, hGNdom, hGNnorm⟩ := iw_narrow_integer_majorant hC hH hS HIW Hmajor
    HShannon HHL HY hr hk d ν hν hβ0.le hβ1 F f hf ha hb
  obtain ⟨GR, hGR0, hGRm, hGRdom, hGRnorm⟩ := iw_large_remainder_majorant hC HIW HY HRT hr hk
    d ν hν hβ0 hβ1 (finiteInputLp F f 2) hf ha hb
  have hshort := iw_short_transition_maximum hC hCe hZ hR HIW HCZ HY HRM hr hk hQ
    d ν hν hβ0 hβ1 (finiteInputLp F f 2) hf ha
  change MemLp U _ _ ∧ _ at hshort
  have hU0 (x : ℤ) : 0 ≤ U x := initialTemporalMaximum_nonneg L J x
  have hp : (1 : ENNReal) ≤ ENNReal.ofReal (iwNearOneExponent r) := by
    rw [←ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (iwNearOneExponent_bounds hr).1.le
  have hmem : MemLp (fun x => (U x+GN x)+GR x) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count :=
    ((hshort.1.add hGNm).add hGRm).ae_eq (Filter.Eventually.of_forall (fun _ => rfl))
  refine ⟨fun x => (U x+GN x)+GR x,
    fun x => add_nonneg (add_nonneg (hU0 x) (hGN0 x)) (hGR0 x), hmem, ?_, ?_⟩
  · intro j x
    by_cases hj : j ≤ J
    · have ht := initialTemporalMaximum_dominates L hj x
      change ‖L j x‖ ≤ (U x+GN x)+GR x
      nlinarith [hGN0 x, hGR0 x]
    · have hJj : J ≤ j := by omega
      have hscale : (2 : ℕ)^(j-J)*iwTransitionScale δ = (2 : ℕ)^j := by
        dsimp only [iwTransitionScale, J]
        rw [←pow_add, Nat.sub_add_cancel hJj]
      have hN2 : 2 ≤ (2 : ℕ)^j := by
        rw [←hscale]
        exact dyadic_annular_scale_lower (iwTransitionScale_two_le hδ hδsmall) (j-J)
      have hN := hGNdom ((2 : ℕ)^j) hN2 x
      have hRj := hGRdom (j-J) x
      have hprod : 1 ≤ (2 : ℕ)^(j-J)*iwTransitionScale δ := by
        have ht := dyadic_annular_scale_lower (iwTransitionScale_two_le hδ hδsmall) (j-J)
        omega
      have hw := iwAnnularLowOperator_scale_congr d.S k d.period ν hprod
        (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))) hscale β (iwCutoffScale C r k Q) ha
      have hn := iwAnnularLowOperator_scale_congr d.S k d.period ν hprod
        (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))) hscale β δ⁻¹ hb
      rw [hw, hn] at hRj
      have ht := integer_operator_difference_bound
        (iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j) (one_le_pow₀ (by norm_num)) β
          (iwCutoffScale C r k Q) ha)
        (iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j) (one_le_pow₀ (by norm_num)) β δ⁻¹ hb)
        (finiteInputLp F f 2) x
      nlinarith [hU0 x]
  · have hfin := iwFiniteLowConstant_nonneg hZ hR
    have hnar := iwNarrowLowConstant_nonneg hH hS
    have hrem := annularRemainderConstant_pos.le
    have hbD := iwMaximalCost_lower_bounds hC hr k Q
    have hD : 0 ≤ iwMaximalCost C r k Q := (by positivity : 0 ≤ (r : ℝ)*(iwMultiplierConstant C r k)^2).trans hbD.1
    have hA : 0 ≤ iwFiniteLowConstant Z R*iwMaximalCost C r k Q := mul_nonneg hfin hD
    have hB : 0 ≤ iwNarrowLowConstant H S*(r : ℝ)*(iwMultiplierConstant C r k)^2 := by positivity
    have hCrem : 0 ≤ 2*annularRemainderConstant*(r : ℝ)*iwMultiplierConstant C r k := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hrem) (Nat.cast_nonneg r))
        (iwMultiplierConstant_nonneg (by linarith) r k)
    have hcost : (iwFiniteLowConstant Z R*iwMaximalCost C r k Q+
        iwNarrowLowConstant H S*(r : ℝ)*(iwMultiplierConstant C r k)^2)+
        2*annularRemainderConstant*(r : ℝ)*iwMultiplierConstant C r k ≤
        iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q := by
      have hn := mul_le_mul_of_nonneg_left hbD.1 hnar
      have hrm := mul_le_mul_of_nonneg_left hbD.2 (show 0 ≤ 2*annularRemainderConstant by positivity)
      unfold iwCompleteLowConstant
      nlinarith only [hn, hrm]
    change eLpNorm ((U+GN)+GR) _ _ ≤ _
    calc
      _ ≤ (eLpNorm U _ _+eLpNorm GN _ _)+eLpNorm GR _ _ :=
        (eLpNorm_add_le hp).trans (add_le_add (eLpNorm_add_le hp) le_rfl)
      _ ≤ (ENNReal.ofReal (iwFiniteLowConstant Z R*iwMaximalCost C r k Q)*
          eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) _ _+
        ENNReal.ofReal (iwNarrowLowConstant H S*(r : ℝ)*(iwMultiplierConstant C r k)^2)*
          eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) _ _)+
        ENNReal.ofReal (2*annularRemainderConstant*(r : ℝ)*iwMultiplierConstant C r k)*
          eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) _ _ :=
        add_le_add (add_le_add hshort.2 hGNnorm) hGRnorm
      _ = ENNReal.ofReal ((iwFiniteLowConstant Z R*iwMaximalCost C r k Q+
          iwNarrowLowConstant H S*(r : ℝ)*(iwMultiplierConstant C r k)^2)+
          2*annularRemainderConstant*(r : ℝ)*iwMultiplierConstant C r k)*
          eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) _ _ := by
        rw [←add_mul, ←add_mul, ←ENNReal.ofReal_add hA hB,
          ←ENNReal.ofReal_add (add_nonneg hA hB) hCrem]
      _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hcost) _

end PrimeSquares
