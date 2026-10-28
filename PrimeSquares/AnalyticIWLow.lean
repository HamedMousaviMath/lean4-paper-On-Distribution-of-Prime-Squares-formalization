import PrimeSquares.IWAllInputLowMaximum

set_option autoImplicit false
open Finset MeasureTheory
open scoped ContDiff FourierTransform ENNReal lp Classical
namespace PrimeSquares

/-- Data needed by the low analytic estimates. Rational coverage is not a
field: it is a separate arithmetic property and is unused in these proofs. -/
structure AnalyticTaoArcData (C ρ : ℝ) (k Q : ℕ) where
  S : Finset ℕ
  positive : ∀ s ∈ S,0 < s
  coprime : (S : Set ℕ).Pairwise Nat.Coprime
  period : ℕ
  period_pos : 0 < period
  period_bound : period ≤ 3^Q
  periodic : ∀ a ∈ iwFrequencySet S k,a.den ∣ period
  component_bound : ∀ s ∈ S,(s:ℝ) ≤ C^((k:ℝ)*(Q:ℝ)^(ρ/2))

theorem analytic_quantitative_iw_goodness {C : ℝ} (hC : 2≤C) {r k Q : ℕ}
    (hr : 2≤r) (hk : 4≤k) (d : AnalyticTaoArcData C (iwRho k) k Q) :
    IWGood r k d.S (iwWidth C r k Q) := by
  let B := iwDenominatorBound C k Q
  let T := C^((k : ℝ)*(Q : ℝ)^(iwRho k/2))
  have hC0 : 0≤C := by linarith
  have hT : 1≤T := Real.one_le_rpow (by linarith : 1≤C) (by positivity)
  have hB : 1≤B := iwDenominatorBound_one_le hC k Q
  have hB0 : 0<B := by linarith
  obtain ⟨qmax,hq,hmax,hqT⟩ := finite_component_maximum hT d.component_bound
  have hqR : (1 : ℝ)≤qmax := by exact_mod_cast hq
  have hrR : (2 : ℝ)≤r := by exact_mod_cast hr
  have he : T^(2*r*k)=B^(2*r) := by
    dsimp [T,B,iwDenominatorBound]
    rw [←Real.rpow_natCast,←Real.rpow_mul hC0,←Real.rpow_natCast,←Real.rpow_mul hC0,iwRho_half hk]
    congr 1
    push_cast
    ring
  have hp : (qmax : ℝ)^(2*r*k)≤B^(2*r) :=
    (pow_le_pow_left₀ (by positivity) hqT _).trans_eq he
  have hpow : B^(2*r)≤B^(2*r+8) := pow_le_pow_right₀ hB (by omega)
  have hpow1 : 1≤B^(2*r+8) := one_le_pow₀ hB
  have hden : 4*(r : ℝ)*B^(2*r)<2^20*(r : ℝ)*B^(2*r+8) := by
    have h1 := mul_le_mul_of_nonneg_left hpow (show 0≤4*(r : ℝ) by positivity)
    have h2 := mul_pos (show 0<(2^20-4)*(r : ℝ) by positivity)
      (show 0<B^(2*r+8) by positivity)
    nlinarith
  have hd0 : 0<4*(r : ℝ)*B^(2*r) := by positivity
  have hq0 : 0<4*(r : ℝ)*(qmax : ℝ)^(2*r*k) := by positivity
  have hwidth : iwWidth C r k Q<1/(4*(r : ℝ)*B^(2*r)) := by
    change (2^20*(r : ℝ)*B^(2*r+8))⁻¹<_
    simpa only [one_div] using one_div_lt_one_div_of_lt hd0 hden
  refine ⟨qmax,hq,hmax,iwWidth_pos hC hr k Q,hwidth.trans_le ?_⟩
  exact one_div_le_one_div_of_le hq0
    (mul_le_mul_of_nonneg_left hp (show 0≤4*(r : ℝ) by positivity))

theorem analytic_quantitative_iw_multiplier {C : ℝ} (hC : 2≤C)
    (HIW : RawIWMultiplierInput C) {r k Q : ℕ} (hr : 2≤r) (hk : 4≤k)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
    (m : BoundedContinuousFunction ℝ ℂ) (hs : ∀ x : ℝ,1≤|x| → m x=0)
    (hε : ∀ x : ℝ,iwWidth C r k Q≤|x| → m x=0)
    (hm : ContDiff ℝ ∞ (m : ℝ → ℂ))
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν≤1)
    {p K : ℝ} (hp0 : iwNearOneExponent r≤p) (hp1 : p≤2*(r : ℝ))
    (hK : 0≤K) (hbound : RealLpMultiplierBound (ENNReal.ofReal p) m K) :
    IntegerLpMultiplierBound (ENNReal.ofReal p)
      (iwCyclicSymbol d.S k d.period ν m hs) (iwMultiplierConstant C r k*K) := by
  exact HIW r k hr (by omega) d.S d.positive d.coprime d.period d.periodic
    (iwWidth C r k Q) (analytic_quantitative_iw_goodness hC hr hk d) m hs hε hm ν hν p hp0 hp1 K hK hbound

theorem analytic_quantitative_iw_sampling {C : ℝ} (hC : 2 ≤ C)
    (HS : RawMajorArcSamplingInput C) {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
    (u : ℚ → SchwartzMap ℝ ℂ)
    (hu : ∀ α ∈ iwFrequencySet d.S k, ∀ θ : ℝ,
      iwWidth C r k Q ≤ |θ| → 𝓕 (u α : ℝ → ℂ) θ = 0)
    (hdiag : MemLp (cyclicDiagonal d.period (cyclicSynthesis (iwFrequencySet d.S k) d.period u))
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count) :
    cyclicRealLpSize d.period (ENNReal.ofReal (iwNearOneExponent r))
      (cyclicSynthesis (iwFrequencySet d.S k) d.period u) ≤
      ENNReal.ofReal (iwMultiplierConstant C r k) *
        eLpNorm (cyclicDiagonal d.period (cyclicSynthesis (iwFrequencySet d.S k) d.period u))
          (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  have hp2r : iwNearOneExponent r ≤ 2*(r : ℝ) := by
    have hp := iwNearOneExponent_bounds hr
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  exact HS r k hr (by omega) d.S d.positive d.coprime d.period d.periodic
    (iwWidth C r k Q) (analytic_quantitative_iw_goodness hC hr hk d) _ le_rfl hp2r u hu hdiag

theorem analytic_iw_finite_lift_size {C : ℝ} (hC : 2 ≤ C)
    (HIW : RawIWMultiplierInput C) (HS : RawMajorArcSamplingInput C)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
    (m : BoundedContinuousFunction ℝ ℂ) (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0)
    (hn : ∀ θ : ℝ, 1/2 ≤ |θ| → m θ = 0)
    (hε : ∀ θ : ℝ, iwWidth C r k Q ≤ |θ| → m θ = 0)
    (hm : ContDiff ℝ ∞ (m : ℝ → ℂ)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : RealLpMultiplierBound (ENNReal.ofReal (iwNearOneExponent r)) m K)
    (F : Finset ℤ) (f : ℤ → ℂ)
    (hf : MemLp (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count) :
    cyclicRealLpSize d.period (ENNReal.ofReal (iwNearOneExponent r))
      (cyclicSynthesis (iwFrequencySet d.S k) d.period (finiteLiftComponent m hs hm F f)) ≤
      ENNReal.ofReal ((iwMultiplierConstant C r k)^2*K)*
        eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  have hp2r : iwNearOneExponent r ≤ 2*(r : ℝ) := by
    have hp := iwNearOneExponent_bounds hr
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hI := analytic_quantitative_iw_multiplier hC HIW hr hk d m hs hε hm (cyclicPointMass d.period)
    (cyclicPointMass_variation d.period).le le_rfl hp2r hK hbound (finiteInputLp F f 2) hf
  have he := iw_finite_lift_diagonal d.S k d.period d.periodic m hs hn hm F f
  have hd : MemLp (cyclicDiagonal d.period (cyclicSynthesis (iwFrequencySet d.S k) d.period
      (finiteLiftComponent m hs hm F f))) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
    rw [he]
    exact hI.1
  have hband : ∀ α ∈ iwFrequencySet d.S k, ∀ θ : ℝ, iwWidth C r k Q ≤ |θ| →
      𝓕 (finiteLiftComponent m hs hm F f α : ℝ → ℂ) θ = 0 := by
    intro α _ θ hθ
    rw [finiteLiftComponent_fourier, hε θ hθ, zero_mul]
  have hS := analytic_quantitative_iw_sampling hC HS hr hk d (finiteLiftComponent m hs hm F f) hband hd
  rw [he] at hS
  refine hS.trans ?_
  calc
    _ ≤ ENNReal.ofReal (iwMultiplierConstant C r k)*
        (ENNReal.ofReal (iwMultiplierConstant C r k*K)*
          eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count) :=
      mul_le_mul_right hI.2 _
    _ = _ := by
      rw [←mul_assoc, ←ENNReal.ofReal_mul (iwMultiplierConstant_nonneg (by linarith : 0 ≤ C) r k)]
      congr 2
      ring

theorem analytic_iwFiniteCutoffLift_size {C : ℝ} (hC : 2 ≤ C)
    (HIW : RawIWMultiplierInput C) (HS : RawMajorArcSamplingInput C) (HY : RawYoungMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
    (F : Finset ℤ) (f : ℤ → ℂ)
    (hf : MemLp (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count)
    (ha : 2 ≤ iwCutoffScale C r k Q) :
    cyclicRealLpSize d.period (ENNReal.ofReal (iwNearOneExponent r))
      (fun y x => finiteCutoffLift (iwFrequencySet d.S k) d.period (iwCutoffScale C r k Q) ha F f y x) ≤
      ENNReal.ofReal ((iwMultiplierConstant C r k)^2*cutoffL1Constant)*
        eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  have ha0 : 0 ≤ iwCutoffScale C r k Q := by linarith
  have hs := continuousCutoffSymbol_boundary ha0 (by linarith : 1 ≤ iwCutoffScale C r k Q*1)
  have hn := continuousCutoffSymbol_boundary ha0 (by linarith : 1 ≤ iwCutoffScale C r k Q*(1/2))
  have hwidth : 1 ≤ iwCutoffScale C r k Q*iwWidth C r k Q := by
    rw [iwCutoffScale, inv_mul_cancel₀ (iwWidth_pos hC hr k Q).ne']
  have hε := continuousCutoffSymbol_boundary ha0 hwidth
  have hLp := continuousCutoffMultiplier_Lp HY (by linarith : 0 < iwCutoffScale C r k Q)
    (iwNearOneExponent_bounds hr).1.le
  have h := analytic_iw_finite_lift_size hC HIW HS hr hk d (continuousCutoffSymbol (iwCutoffScale C r k Q))
    hs hn hε (continuousCutoffSymbol_smooth _) cutoffL1Constant_nonneg hLp F f hf
  simpa only [finiteCutoffLift, cyclicSynthesisSchwartz_apply] using h

theorem analytic_iw_narrow_finite_maximum {C H S : ℝ} (hC : 2 ≤ C) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HY : RawYoungMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν ≤ 1)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (I : Finset ℕ) (N : ℕ → ℕ) (hN : ∀ i, 2 ≤ N i)
    (F : Finset ℤ) (f : ℤ → ℂ)
    (hf : MemLp (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count)
    (ha : 2 ≤ iwCutoffScale C r k Q)
    (hb : 2 ≤ (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹) :
    MemLp (finiteCoordinateMaximum I (fun i (n : ℤ) =>
      iwAnnularLowOperator d.S k d.period ν (N i) (by have h := hN i; omega) β
        (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹ hb (finiteInputLp F f 2) n))
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
    eLpNorm (finiteCoordinateMaximum I (fun i (n : ℤ) =>
      iwAnnularLowOperator d.S k d.period ν (N i) (by have h := hN i; omega) β
        (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹ hb (finiteInputLp F f 2) n))
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ≤
      ENNReal.ofReal (iwNarrowLowConstant H S*(r : ℝ)*(iwMultiplierConstant C r k)^2)*
        eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  let p := iwNearOneExponent r
  have hp := iwNearOneExponent_bounds hr
  have hp2 : p ≤ 2 := by dsimp only [p]; linarith [hp.2]
  have hpen : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [←ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.1.le
  let δ := iwNarrowWidth (iwWidth C r k Q) d.period
  have hP : 1 ≤ d.period := by have h := d.period_pos; omega
  have hδ : 0 < δ := iwNarrowWidth_pos (iwWidth_pos hC hr k Q) hP
  have hbgeom := iwNarrow_inverse_geometry (k := k) (Q := Q) hC hr hP
  let W := finiteCutoffLift (iwFrequencySet d.S k) d.period (iwCutoffScale C r k Q) ha F f
  let E := cyclicConvolutionSchwartz d.period ν W
  let G : ℕ → ZMod d.period → SchwartzMap ℝ ℂ := fun i y =>
    annularSchwartzOutput (N i) (by have h := hN i; omega) β hβ0 hβ1 δ⁻¹ hb (E y)
  have hband : ∀ i ∈ I, ∀ y : ZMod d.period, ∀ θ : ℝ, δ ≤ |θ| → 𝓕 (G i y : ℝ → ℂ) θ = 0 := by
    intro i _ y θ hθ
    apply annularSchwartzOutput_band (N i) (by have h := hN i; omega) β hβ0 hβ1 hb _ (E y) θ hθ
    rw [inv_mul_cancel₀ hδ.ne']
  have hSh := HShannon d.period δ hδ (iwNarrowWidth_le_period _ _) p hp.1.le hp2 I G hband
  have hpoint (i : ℕ) (n : ℤ) : G i (n : ZMod d.period) (n : ℝ) =
      iwAnnularLowOperator d.S k d.period ν (N i) (by have h := hN i; omega) β δ⁻¹ hb (finiteInputLp F f 2) n := by
    exact iw_narrow_lift_diagonal d.S k d.period d.periodic ν (N i) (by have h := hN i; omega)
      β hβ0 hβ1 ha hb hbgeom.2.1 F f n
  simp_rw [hpoint] at hSh
  refine ⟨hSh.1, hSh.2.trans ?_⟩
  have hW := analytic_iwFiniteCutoffLift_size hC HIW Hmajor HY hr hk d F f hf ha
  have hE := cyclicConvolutionSchwartz_Lp d.period hpen ENNReal.ofReal_ne_top ν W
  have hEW : cyclicRealLpSize d.period (ENNReal.ofReal p) (fun y x => E y x) ≤
      cyclicRealLpSize d.period (ENNReal.ofReal p) (fun y x => W y x) := by
    refine hE.trans ?_
    have htv : ENNReal.ofReal (cyclicVariation d.period ν) ≤ 1 := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hν
    simpa only [one_mul] using mul_le_mul_left htv
      (cyclicRealLpSize d.period (ENNReal.ofReal p) (fun y x => W y x))
  have hreal := cyclic_annularSchwartzOutput_maximum hH HHL HY d.period hp.1 hp2 hβ0 hβ1 hb I N hN E
  have hA : 0 ≤ (H/(p-1))*cutoffL1Constant := mul_nonneg (div_nonneg hH (by linarith [hp.1])) cutoffL1Constant_nonneg
  have hcoef : S*((H/(p-1))*cutoffL1Constant)*((iwMultiplierConstant C r k)^2*cutoffL1Constant) ≤
      iwNarrowLowConstant H S*(r : ℝ)*(iwMultiplierConstant C r k)^2 := by
    have hnear := iwNearOneExponent_cost hr hH
    have hmult := mul_le_mul_of_nonneg_left hnear
      (mul_nonneg (mul_nonneg hS (sq_nonneg cutoffL1Constant)) (sq_nonneg (iwMultiplierConstant C r k)))
    unfold iwNarrowLowConstant
    dsimp only [p]
    nlinarith only [hmult]
  calc
    _ ≤ ENNReal.ofReal S *
        (ENNReal.ofReal ((H/(p-1))*cutoffL1Constant)*
          cyclicRealLpSize d.period (ENNReal.ofReal p) (fun y x => E y x)) :=
      mul_le_mul_right hreal _
    _ ≤ ENNReal.ofReal S *
        (ENNReal.ofReal ((H/(p-1))*cutoffL1Constant)*
          (ENNReal.ofReal ((iwMultiplierConstant C r k)^2*cutoffL1Constant)*
            eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal p) Measure.count)) := by
      apply mul_le_mul_right
      exact mul_le_mul_right (hEW.trans hW) _
    _ = ENNReal.ofReal (S*((H/(p-1))*cutoffL1Constant)*((iwMultiplierConstant C r k)^2*cutoffL1Constant))*
        eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
      rw [←mul_assoc, ←mul_assoc, ←ENNReal.ofReal_mul hS, ←ENNReal.ofReal_mul (mul_nonneg hS hA)]
    _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hcoef) _

theorem analytic_iw_narrow_integer_majorant {C H S : ℝ} (hC : 2 ≤ C) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HY : RawYoungMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν ≤ 1)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (F : Finset ℤ) (f : ℤ → ℂ)
    (hf : MemLp (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count)
    (ha : 2 ≤ iwCutoffScale C r k Q)
    (hb : 2 ≤ (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹) :
    ∃ G : ℤ → ℝ, (∀ x, 0 ≤ G x) ∧
      MemLp G (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
      (∀ (N : ℕ) (hN : 2 ≤ N) (x : ℤ),
        ‖iwAnnularLowOperator d.S k d.period ν N (by omega) β
          (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹ hb (finiteInputLp F f 2) x‖ ≤ G x) ∧
      eLpNorm G (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ≤
        ENNReal.ofReal (iwNarrowLowConstant H S*(r : ℝ)*(iwMultiplierConstant C r k)^2)*
          eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  let g : ℕ → ℤ → ℂ := fun j x =>
    iwAnnularLowOperator d.S k d.period ν (j+2) (by omega) β
      (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹ hb (finiteInputLp F f 2) x
  have hp0 : ENNReal.ofReal (iwNearOneExponent r) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one (iwNearOneExponent_bounds hr).1))
  have hB : ENNReal.ofReal (iwNarrowLowConstant H S*(r : ℝ)*(iwMultiplierConstant C r k)^2)*
      eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  obtain ⟨G, hG0, hGm, hGdom, hGnorm⟩ := uniform_finite_integer_Lp_majorant hp0 g hB
    (fun I => analytic_iw_narrow_finite_maximum hC hH hS HIW Hmajor HShannon HHL HY hr hk d ν hν hβ0 hβ1
      I (fun j => j+2) (fun _ => by omega) F f hf ha hb)
  refine ⟨G, hG0, hGm, ?_, hGnorm⟩
  intro N hN x
  have h := hGdom (N-2) x
  simpa only [g, Nat.sub_add_cancel hN] using h

theorem analytic_iw_annular_remainder_multiplier {C : ℝ} (hC : 2 ≤ C)
    (HIW : RawIWMultiplierInput C) (HY : RawYoungMultiplierInput)
    (HRT : RawRieszThorinMultiplierInput)
    {r k Q N : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k) (hN : 2 ≤ N)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν ≤ 1)
    {β b : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hb : 0 < b)
    (hab : 2 * iwCutoffScale C r k Q ≤ b) (hb2 : 2 ≤ b) :
    IntegerLpMultiplierBound (ENNReal.ofReal (iwNearOneExponent r))
      (weightedWidthAnnularBlock (iwFrequencySet d.S k) N (by omega) β
          (iwCutoffScale C r k Q)
          (by have h := iwCutoffScale_four_le hC hr k Q; linarith)
          (cyclicRationalCoefficient d.period ν) -
        weightedWidthAnnularBlock (iwFrequencySet d.S k) N (by omega) β b hb2
          (cyclicRationalCoefficient d.period ν))
      (iwMultiplierConstant C r k *
        (annularRemainderConstant * (b / (N : ℝ)^2)^((r : ℝ)⁻¹))) := by
  have ha4 := iwCutoffScale_four_le hC hr k Q
  have ha : 0 < iwCutoffScale C r k Q := by linarith
  have hw := iwWidth_pos hC hr k Q
  have haw : 1 ≤ iwCutoffScale C r k Q * iwWidth C r k Q := by
    rw [iwCutoffScale, inv_mul_cancel₀ hw.ne']
  have ha1 : 1 ≤ iwCutoffScale C r k Q * 1 := by linarith
  have hb1 : 1 ≤ b * 1 := by linarith
  have hbw : 1 ≤ b * iwWidth C r k Q := by
    have hm := mul_le_mul_of_nonneg_right hab hw.le
    linarith
  have hsa := allAnnularBoundedSymbol_boundary N (by omega) β hβ0.le hβ1 ha.le ha1
  have hsb := allAnnularBoundedSymbol_boundary N (by omega) β hβ0.le hβ1 hb.le hb1
  have hεa := allAnnularBoundedSymbol_boundary N (by omega) β hβ0.le hβ1 ha.le haw
  have hεb := allAnnularBoundedSymbol_boundary N (by omega) β hβ0.le hβ1 hb.le hbw
  have hs : ∀ x : ℝ, 1 ≤ |x| →
      annularCutoffRemainderSymbol N (by omega) β hβ0.le hβ1 (iwCutoffScale C r k Q) b x = 0 := by
    intro x hx
    change _ - _ = (0 : ℂ)
    rw [hsa x hx, hsb x hx, sub_self]
  have hε : ∀ x : ℝ, iwWidth C r k Q ≤ |x| →
      annularCutoffRemainderSymbol N (by omega) β hβ0.le hβ1 (iwCutoffScale C r k Q) b x = 0 := by
    intro x hx
    change _ - _ = (0 : ℂ)
    rw [hεa x hx, hεb x hx, sub_self]
  have hp := iwNearOneExponent_bounds hr
  have hp2r : iwNearOneExponent r ≤ 2 * (r : ℝ) := by
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith [hp.2]
  have hcont := annularCutoffRemainder_Lp HY HRT hN hr hβ0 hβ1 ha hb hab
  have hiw := analytic_quantitative_iw_multiplier hC HIW hr hk d _ hs hε
    (annularCutoffRemainderSymbol_smooth N (by omega) β hβ0.le hβ1 (iwCutoffScale C r k Q) b)
    ν hν le_rfl hp2r
    (mul_nonneg annularRemainderConstant_pos.le (Real.rpow_nonneg (by positivity) _)) hcont
  change IntegerLpMultiplierBound _ (iwCyclicSymbol _ _ _ _ (_ - _) hs) _ at hiw
  rw [iwCyclicSymbol_sub _ _ _ _ _ _ hsa hsb hs,
    iwCyclicSymbol_all_annular d.S k d.period ν N (by omega) β hβ0.le hβ1
      (iwCutoffScale C r k Q) (by linarith) hsa,
    iwCyclicSymbol_all_annular d.S k d.period ν N (by omega) β hβ0.le hβ1 b hb2 hsb] at hiw
  exact hiw

theorem analytic_iw_large_remainder_majorant {C : ℝ} (hC : 2 ≤ C)
    (HIW : RawIWMultiplierInput C) (HY : RawYoungMultiplierInput)
    (HRT : RawRieszThorinMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν ≤ 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (f : ℓ²(ℤ,ℂ))
    (hf : MemLp (f : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count)
    (ha : 2 ≤ iwCutoffScale C r k Q)
    (hb : 2 ≤ (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹) :
    ∃ H : ℤ → ℝ, (∀ x, 0 ≤ H x) ∧
      MemLp H (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
      (∀ j x, ‖(iwAnnularLowOperator d.S k d.period ν
          ((2 : ℕ)^j * iwTransitionScale (iwNarrowWidth (iwWidth C r k Q) d.period))
          (by apply Nat.one_le_iff_ne_zero.mpr; dsimp [iwTransitionScale]; positivity) β (iwCutoffScale C r k Q) ha -
        iwAnnularLowOperator d.S k d.period ν
          ((2 : ℕ)^j * iwTransitionScale (iwNarrowWidth (iwWidth C r k Q) d.period))
          (by apply Nat.one_le_iff_ne_zero.mpr; dsimp [iwTransitionScale]; positivity) β
          (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹ hb) f x‖ ≤ H x) ∧
      eLpNorm H (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ≤
        ENNReal.ofReal (2*annularRemainderConstant*(r : ℝ)*iwMultiplierConstant C r k)*
          eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  let δ := iwNarrowWidth (iwWidth C r k Q) d.period
  have hP : 1 ≤ d.period := by have h := d.period_pos; omega
  have hδ0 : 0 < δ := iwNarrowWidth_pos (iwWidth_pos hC hr k Q) hP
  have hδsmall : δ ≤ 1/100 := iwNarrowWidth_small _ hP
  have hδ1 : δ ≤ 1 := by linarith
  have hM := iwTransitionScale_two_le hδ0 hδsmall
  have hbgeom := iwNarrow_inverse_geometry (k := k) (Q := Q) hC hr hP
  let g : ℕ → ℤ → ℂ := fun j =>
    ((iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j * iwTransitionScale δ)
        (by apply Nat.one_le_iff_ne_zero.mpr; dsimp [iwTransitionScale]; positivity) β (iwCutoffScale C r k Q) ha -
      iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j * iwTransitionScale δ)
        (by apply Nat.one_le_iff_ne_zero.mpr; dsimp [iwTransitionScale]; positivity) β δ⁻¹ hb) f : ℤ → ℂ)
  have hC0 : 0 ≤ iwMultiplierConstant C r k := iwMultiplierConstant_nonneg (by linarith) r k
  have hA : 0 ≤ iwMultiplierConstant C r k * annularRemainderConstant :=
    mul_nonneg hC0 annularRemainderConstant_pos.le
  have hj (j : ℕ) : MemLp (g j) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
      eLpNorm (g j) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ≤
        ENNReal.ofReal ((iwMultiplierConstant C r k*annularRemainderConstant)*iwRemainderRatio r^j)*
          eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
    have hN : 2 ≤ (2 : ℕ)^j * iwTransitionScale δ := dyadic_annular_scale_lower hM j
    have h := analytic_iw_annular_remainder_multiplier hC HIW HY HRT hr hk hN d ν hν hβ0 hβ1
      hbgeom.1 hbgeom.2.1 hb f hf
    rw [integerMultiplier_sub] at h
    change MemLp (g j) _ _ ∧ _ at h
    refine ⟨h.1, h.2.trans ?_⟩
    apply mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_)
    have hd := iw_transition_remainder_decay hr hδ0 hδ1 j
    calc
      _ ≤ iwMultiplierConstant C r k * (annularRemainderConstant*iwRemainderRatio r^j) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd annularRemainderConstant_pos.le) hC0
      _ = _ := by ring
  have hp : (1 : ENNReal) ≤ ENNReal.ofReal (iwNearOneExponent r) := by
    rw [←ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (iwNearOneExponent_bounds hr).1.le
  obtain ⟨H, hH0, hHm, hHdom, hHnorm⟩ := geometric_integer_Lp_majorant hp g (fun j => (hj j).1)
    hA (iwRemainderRatio_bounds hr).1.le (iwRemainderRatio_bounds hr).2
    (iwRemainderRatio_sum_bound hr) _ hf.eLpNorm_ne_top (fun j => (hj j).2)
  refine ⟨H, hH0, hHm, hHdom, ?_⟩
  convert hHnorm using 1; congr 2; ring

theorem analytic_iw_annular_single_multiplier {C : ℝ} (hC : 2≤ C)
    (HIW : RawIWMultiplierInput C) (HY : RawYoungMultiplierInput)
    {r k Q : ℕ} (hr : 2≤ r) (hk : 4≤ k)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period→ℂ) (hν : cyclicVariation d.period ν≤1)
    (N : ℕ) (hN : 1≤ N) {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) :
    IntegerLpMultiplierBound (ENNReal.ofReal (iwNearOneExponent r))
      (weightedWidthAnnularBlock (iwFrequencySet d.S k) N hN β (iwCutoffScale C r k Q)
        (by have h := iwCutoffScale_four_le hC hr k Q;linarith) (cyclicRationalCoefficient d.period ν))
      (iwMultiplierConstant C r k*cutoffL1Constant) := by
  have ha4 := iwCutoffScale_four_le hC hr k Q
  have ha : 0 < iwCutoffScale C r k Q := by linarith
  have hw := iwWidth_pos hC hr k Q
  have haw : 1≤ iwCutoffScale C r k Q*iwWidth C r k Q := by
    rw [iwCutoffScale,inv_mul_cancel₀ hw.ne']
  have ha1 : 1≤ iwCutoffScale C r k Q*1 := by linarith
  have hs := allAnnularBoundedSymbol_boundary N hN β hβ0.le hβ1 ha.le ha1
  have hε := allAnnularBoundedSymbol_boundary N hN β hβ0.le hβ1 ha.le haw
  have hpr := iwNearOneExponent_bounds hr
  have hp2r : iwNearOneExponent r≤2*(r : ℝ) := by
    have hrR : (2 : ℝ)≤ r := by exact_mod_cast hr
    linarith [hpr.2]
  have hcont := annularCutoffYoungMultiplier_Lp HY hN hβ0 hβ1 ha hpr.1.le
  have hiw := analytic_quantitative_iw_multiplier hC HIW hr hk d _ hs hε
    (annularCutoffSymbol_contDiff hN β (iwCutoffScale C r k Q)) ν hν
    le_rfl hp2r cutoffL1Constant_nonneg hcont
  rw [iwCyclicSymbol_all_annular d.S k d.period ν N hN β hβ0.le hβ1
    (iwCutoffScale C r k Q) (by linarith) hs] at hiw
  exact hiw

theorem analytic_iw_signed_annular_multiplier {C Z : ℝ} (hC : 2≤ C) (hZ : 0≤ Z)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    {r k Q : ℕ} (hr : 2≤ r) (hk : 4≤ k)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period→ℂ) (hν : cyclicVariation d.period ν≤1)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1)
    (J : ℕ) (σ : ℕ→ℂ) (hσ : ∀ j∈range J,‖σ j‖≤1)
    (hs : ∀ x : ℝ,1≤|x| →
      continuousAnnularSignedSymbol β hβ0.le hβ1 (iwCutoffScale C r k Q) J σ x=0) :
    IntegerLpMultiplierBound (ENNReal.ofReal (iwNearOneExponent r))
      (iwCyclicSymbol d.S k d.period ν
        (continuousAnnularSignedSymbol β hβ0.le hβ1 (iwCutoffScale C r k Q) J σ) hs)
      (iwAnnularIncrementCost Z*(r : ℝ)*iwMultiplierConstant C r k) := by
  have ha4 := iwCutoffScale_four_le hC hr k Q
  have ha : 0< iwCutoffScale C r k Q := by linarith
  have hw := iwWidth_pos hC hr k Q
  have haw : 1≤ iwCutoffScale C r k Q*iwWidth C r k Q := by
    rw [iwCutoffScale,inv_mul_cancel₀ hw.ne']
  have hpr := iwNearOneExponent_bounds hr
  have hp2 : iwNearOneExponent r≤2 := by linarith
  have hp2r : iwNearOneExponent r≤2*(r : ℝ) := by
    have hrR : (2 : ℝ)≤ r := by exact_mod_cast hr
    linarith
  have hcont := continuousAnnularCutoffSignedMultiplier_Lp hZ HCZ HY hβ0 hβ1 ha J σ hσ hpr.1 hp2
  have hK : 0≤(Z*(continuousAnnularIncrementConstant+2+50)/(iwNearOneExponent r-1))*cutoffL1Constant := by
    have hp : 0< iwNearOneExponent r-1 := by linarith [hpr.1]
    have h := continuousAnnularIncrementConstant_pos
    have hcut := cutoffL1Constant_nonneg
    positivity
  have hiw := analytic_quantitative_iw_multiplier hC HIW hr hk d _ hs
    (continuousAnnularSignedSymbol_boundary β hβ0.le hβ1 J σ ha.le haw)
    (continuousAnnularSignedSymbol_contDiff β hβ0.le hβ1 (iwCutoffScale C r k Q) J σ)
    ν hν le_rfl hp2r hK hcont
  apply integerLpMultiplierBound_mono hiw
  have hA : 0≤ Z*(continuousAnnularIncrementConstant+2+50) := by
    have h := continuousAnnularIncrementConstant_pos
    positivity
  have hb := mul_le_mul_of_nonneg_right (iwNearOneExponent_cost hr hA) cutoffL1Constant_nonneg
  have hm := mul_le_mul_of_nonneg_left hb (iwMultiplierConstant_nonneg (by linarith : 0≤ C) r k)
  exact hm.trans_eq (by unfold iwAnnularIncrementCost;ring)

theorem analytic_iw_annular_signed_increments {C Z : ℝ} (hC : 2≤ C) (hZ : 0≤ Z)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    {r k Q : ℕ} (hr : 2≤ r) (hk : 4≤ k)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period→ℂ) (hν : cyclicVariation d.period ν≤1)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (J : ℕ) (σ : ℕ→ℂ)
    (hσ : ∀ j∈range J,‖σ j‖≤1) (f : ℓ²(ℤ,ℂ))
    (hf : MeasureTheory.MemLp (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) MeasureTheory.Measure.count) :
    MeasureTheory.MemLp (iwAnnularSignedOperator d.S k d.period ν β (iwCutoffScale C r k Q)
      (by have h := iwCutoffScale_four_le hC hr k Q;linarith) J σ f : ℤ→ℂ)
      (ENNReal.ofReal (iwNearOneExponent r)) MeasureTheory.Measure.count ∧
    MeasureTheory.eLpNorm (iwAnnularSignedOperator d.S k d.period ν β (iwCutoffScale C r k Q)
      (by have h := iwCutoffScale_four_le hC hr k Q;linarith) J σ f : ℤ→ℂ)
      (ENNReal.ofReal (iwNearOneExponent r)) MeasureTheory.Measure.count≤
      ENNReal.ofReal (iwAnnularIncrementCost Z*(r : ℝ)*iwMultiplierConstant C r k)*
        MeasureTheory.eLpNorm (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) MeasureTheory.Measure.count := by
  have ha4 := iwCutoffScale_four_le hC hr k Q
  have ha0 : 0≤ iwCutoffScale C r k Q := by linarith
  have ha1 : 1≤ iwCutoffScale C r k Q*1 := by linarith
  have hs := continuousAnnularSignedSymbol_boundary β hβ0.le hβ1 J σ ha0 ha1
  have h := analytic_iw_signed_annular_multiplier hC hZ HIW HCZ HY hr hk d ν hν hβ0 hβ1 J σ hσ hs f hf
  rw [iw_signed_annular_operator_identity d.S k d.period ν β hβ0.le hβ1
    (iwCutoffScale C r k Q) (by linarith) J σ hs] at h
  exact h

theorem analytic_iw_short_scale_increment_maximum {C Z R : ℝ} (hC : 2≤ C) (hZ : 0≤ Z)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) {r k Q : ℕ} (hr : 2≤ r) (hk : 4≤ k)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period→ℂ) (hν : cyclicVariation d.period ν≤1)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (J : ℕ) (f : ℓ²(ℤ,ℂ))
    (hf : MemLp (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count)
    (ha : 2≤ iwCutoffScale C r k Q) :
    MemLp (finitePartialSumMaximum
      (iwAnnularIncrementSequence d.S k d.period ν β (iwCutoffScale C r k Q) ha f) J)
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
    eLpNorm (finitePartialSumMaximum
      (iwAnnularIncrementSequence d.S k d.period ν β (iwCutoffScale C r k Q) ha f) J)
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count≤
      ENNReal.ofReal (R*Real.log (2+(J : ℝ)))*
        (ENNReal.ofReal (iwAnnularIncrementCost Z*(r : ℝ)*iwMultiplierConstant C r k)*
          eLpNorm (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count) := by
  have hp := iwNearOneExponent_bounds hr
  apply finite_signed_maximal HRM hp.1.le (by linarith [hp.2])
  intro σ hσ
  rw [iwAnnularIncrementSequence_signed]
  exact analytic_iw_annular_signed_increments hC hZ HIW HCZ HY hr hk d ν hν hβ0 hβ1 J σ hσ f hf

theorem analytic_iw_short_scale_maximum {C Z R : ℝ} (hC : 2≤ C) (hZ : 0≤ Z) (hR : 0≤ R)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) {r k Q : ℕ} (hr : 2≤ r) (hk : 4≤ k)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period→ℂ) (hν : cyclicVariation d.period ν≤1)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (J : ℕ) (f : ℓ²(ℤ,ℂ))
    (hf : MemLp (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count)
    (ha : 2≤ iwCutoffScale C r k Q) :
    MemLp (initialTemporalMaximum (fun j => iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j)
      (one_le_pow₀ (by norm_num)) β (iwCutoffScale C r k Q) ha f) J)
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
    eLpNorm (initialTemporalMaximum (fun j => iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j)
      (one_le_pow₀ (by norm_num)) β (iwCutoffScale C r k Q) ha f) J)
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count≤
      ENNReal.ofReal (iwShortScaleCost C Z R r k J)*
        eLpNorm (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  let F : ℕ→ℓ²(ℤ,ℂ) := fun j => iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j)
    (one_le_pow₀ (by norm_num)) β (iwCutoffScale C r k Q) ha f
  have h0 := analytic_iw_annular_single_multiplier hC HIW HY hr hk d ν hν 1 (by norm_num) hβ0 hβ1 f hf
  change MemLp (F 0 : ℤ→ℂ) _ _ ∧ eLpNorm (F 0 : ℤ→ℂ) _ _≤_ at h0
  have hm := analytic_iw_short_scale_increment_maximum hC hZ HIW HCZ HY HRM hr hk d ν hν hβ0 hβ1 J f hf ha
  change MemLp (finitePartialSumMaximum (finiteDifferenceSequence F) J) _ _ ∧
    eLpNorm (finitePartialSumMaximum (finiteDifferenceSequence F) J) _ _≤_ at hm
  have hp := iwNearOneExponent_bounds hr
  have hpen : (1 : ENNReal)≤ ENNReal.ofReal (iwNearOneExponent r) := by
    rw [←ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.1.le
  obtain ⟨hmem,hnorm⟩ := finiteDifferenceSequence_maximum_Lp F J hpen h0.1 hm.1
  refine ⟨hmem,hnorm.trans ((add_le_add h0.2 hm.2).trans_eq ?_)⟩
  have hmult := iwMultiplierConstant_nonneg (by linarith : 0≤ C) r k
  have hinc := iwAnnularIncrementCost_nonneg hZ
  have hcut := cutoffL1Constant_nonneg
  have hlog : 0≤ Real.log (2+(J : ℝ)) :=
    Real.log_nonneg (by have hJ : (0 : ℝ)≤ J := Nat.cast_nonneg J;linarith)
  unfold iwShortScaleCost
  rw [ENNReal.ofReal_add (mul_nonneg hmult hcut)
    (mul_nonneg (mul_nonneg hR hlog) (by positivity)),add_mul,
    ENNReal.ofReal_mul (mul_nonneg hR hlog),mul_assoc]
  simp only [mul_assoc]

theorem analytic_iw_period_log_bound {C ρ : ℝ} {k Q : ℕ}
    (d : AnalyticTaoArcData C ρ k Q) : Real.log (d.period : ℝ)≤2*(Q : ℝ) := by
  have hP : (0 : ℝ)< d.period := by exact_mod_cast d.period_pos
  have hb : (d.period : ℝ)≤(3 : ℝ)^Q := by exact_mod_cast d.period_bound
  have h := Real.log_le_log hP hb
  rw [Real.log_pow] at h
  have h3 : Real.log (3 : ℝ)≤2 := by
    simpa only [show (3 : ℝ)-1=2 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<3)
  have hm := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg Q : (0 : ℝ)≤ Q)
  nlinarith

theorem analytic_iw_narrow_log_inverse_budget {C : ℝ} (hC : 2≤ C) {r k Q : ℕ}
    (hr : 2≤ r) (hQ : 1≤ Q) (hL : 1≤ Real.log (iwDenominatorBound C k Q))
    (d : AnalyticTaoArcData C (iwRho k) k Q) :
    -Real.log (iwNarrowWidth (iwWidth C r k Q) d.period)≤
      100*((Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q)) := by
  have hε := iwWidth_pos hC hr k Q
  have hP : 1≤ d.period := by have h := d.period_pos;omega
  have hp := iwNarrowWidth_log_inverse hε hP
  have hloga := iwCutoffScale_log_bound hC hr hL
  have he : -Real.log (iwWidth C r k Q)=Real.log (iwCutoffScale C r k Q) := by
    rw [iwCutoffScale,Real.log_inv]
  have h16 : Real.log (16 : ℝ)≤15 := by
    simpa only [show (16 : ℝ)-1=15 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<16)
  have h100 : Real.log (100 : ℝ)≤99 := by
    simpa only [show (100 : ℝ)-1=99 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<100)
  have hperiod := analytic_iw_period_log_bound d
  have hrR : (2 : ℝ)≤ r := by exact_mod_cast hr
  have hQR : (1 : ℝ)≤ Q := by exact_mod_cast hQ
  have hRL : 2≤(r : ℝ)*Real.log (iwDenominatorBound C k Q) := by nlinarith
  apply hp.trans
  apply max_le
  · rw [sub_eq_add_neg,he]
    nlinarith
  · nlinarith

theorem analytic_iw_transition_index_linear_budget {C : ℝ} (hC : 2≤ C) {r k Q : ℕ}
    (hr : 2≤ r) (hQ : 1≤ Q) (hL : 1≤ Real.log (iwDenominatorBound C k Q))
    (d : AnalyticTaoArcData C (iwRho k) k Q) :
    (iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period) : ℝ)+2≤
      101*((Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q)) := by
  let δ := iwNarrowWidth (iwWidth C r k Q) d.period
  have hδ0 : 0<δ := iwNarrowWidth_pos (iwWidth_pos hC hr k Q) (by have h := d.period_pos;omega)
  have hδ1 : δ≤1 := (iwNarrowWidth_small _ (by have h := d.period_pos;omega)).trans (by norm_num)
  have hj := (iwTransitionIndex_bounds hδ0 hδ1).2
  have hD : 0≤-Real.log δ := neg_nonneg.mpr (Real.log_nonpos hδ0.le hδ1)
  have hden : 1≤2*Real.log (2 : ℝ) := by linarith [real_log_two_half_le]
  have hdiv : (-Real.log δ)/(2*Real.log 2)≤-Real.log δ := by
    apply (div_le_iff₀ (by linarith : 0<2*Real.log (2 : ℝ))).mpr
    nlinarith
  have hb := analytic_iw_narrow_log_inverse_budget hC hr hQ hL d
  have hrR : (2 : ℝ)≤ r := by exact_mod_cast hr
  have hQR : (1 : ℝ)≤ Q := by exact_mod_cast hQ
  have hRL : 2≤(r : ℝ)*Real.log (iwDenominatorBound C k Q) := by nlinarith
  dsimp only [δ] at hj hdiv
  linarith

theorem analytic_iw_transition_log_cost_budget {C : ℝ} (hC : 2≤ C) {r k Q : ℕ}
    (hr : 2≤ r) (hQ : 1≤ Q) (hL : 1≤ Real.log (iwDenominatorBound C k Q))
    (d : AnalyticTaoArcData C (iwRho k) k Q) :
    Real.log (2+(iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period) : ℝ))≤
      101*Real.log (Real.exp 1+(Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q)) := by
  let U : ℝ := (Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q)
  have hrR : (2 : ℝ)≤ r := by exact_mod_cast hr
  have hQR : (1 : ℝ)≤ Q := by exact_mod_cast hQ
  have hRL : 2≤(r : ℝ)*Real.log (iwDenominatorBound C k Q) := by nlinarith
  have hU : 0< U := by dsimp [U];linarith
  have hb := analytic_iw_transition_index_linear_budget hC hr hQ hL d
  have hj : (0 : ℝ)<2+(iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period) : ℝ) := by positivity
  have ht := Real.log_le_log hj (by simpa only [add_comm] using hb)
  rw [Real.log_mul (by norm_num : (101 : ℝ)≠0) hU.ne'] at ht
  have hc : Real.log (101 : ℝ)≤100 := by
    simpa only [show (101 : ℝ)-1=100 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<101)
  have hu : Real.log U≤ Real.log (Real.exp 1+U) := Real.log_le_log hU (by linarith [Real.exp_pos 1])
  have hl : 1≤ Real.log (Real.exp 1+U) := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1≤ Real.exp 1+U by linarith)
    simpa only [Real.log_exp] using h
  dsimp [U] at hu hl ht
  rw [←add_assoc] at hu hl
  linarith

theorem analytic_iw_short_transition_cost_bound {C Z R : ℝ} (hC : 2≤ C) (hZ : 0≤ Z) (hR : 0≤ R)
    {r k Q : ℕ} (hr : 2≤ r) (hQ : 1≤ Q) (hL : 1≤ Real.log (iwDenominatorBound C k Q))
    (d : AnalyticTaoArcData C (iwRho k) k Q) :
    iwShortScaleCost C Z R r k (iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period))≤
      iwFiniteLowConstant Z R*iwMaximalCost C r k Q := by
  have hc := iw_short_scale_cost_bound (by linarith : 0≤ C) hr Z R k
    (iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period))
  have hj := analytic_iw_transition_log_cost_budget hC hr hQ hL d
  have hi := iwAnnularIncrementCost_nonneg hZ
  have hcut := cutoffL1Constant_nonneg
  have hA : 0≤ cutoffL1Constant+R*iwAnnularIncrementCost Z := by positivity
  have hmult := iwMultiplierConstant_one_le hC hr k
  have hmult0 := iwMultiplierConstant_nonneg (by linarith : 0≤ C) r k
  have hrR : (2 : ℝ)≤ r := by exact_mod_cast hr
  have hQR : (1 : ℝ)≤ Q := by exact_mod_cast hQ
  have hRL : 2≤(r : ℝ)*Real.log (iwDenominatorBound C k Q) := by nlinarith
  have hlog : 0≤ Real.log (Real.exp 1+(Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q)) :=
    Real.log_nonneg (by have he := Real.add_one_le_exp (1 : ℝ);linarith)
  calc
    _ ≤ (cutoffL1Constant+R*iwAnnularIncrementCost Z)*(r : ℝ)*iwMultiplierConstant C r k*
        Real.log (2+(iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period) : ℝ)) := hc
    _ ≤ (cutoffL1Constant+R*iwAnnularIncrementCost Z)*(r : ℝ)*iwMultiplierConstant C r k*
        (101*Real.log (Real.exp 1+(Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q))) := by
      gcongr
    _ = (101*(cutoffL1Constant+R*iwAnnularIncrementCost Z))*(r : ℝ)*iwMultiplierConstant C r k*
        Real.log (Real.exp 1+(Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q)) := by ring
    _ ≤ (101*(cutoffL1Constant+R*iwAnnularIncrementCost Z))*(r : ℝ)*(iwMultiplierConstant C r k)^2*
        Real.log (Real.exp 1+(Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q)) := by
      gcongr
      nlinarith
    _ = _ := by unfold iwFiniteLowConstant iwMaximalCost;ring

theorem analytic_iw_short_transition_maximum {C Z R : ℝ} (hC : 2≤ C) (hCe : Real.exp 1≤ C)
    (hZ : 0≤ Z) (hR : 0≤ R)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) {r k Q : ℕ} (hr : 2≤ r) (hk : 4≤ k) (hQ : 1≤ Q)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period→ℂ) (hν : cyclicVariation d.period ν≤1)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (f : ℓ²(ℤ,ℂ))
    (hf : MemLp (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count)
    (ha : 2≤ iwCutoffScale C r k Q) :
    MemLp (initialTemporalMaximum (fun j => iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j)
      (one_le_pow₀ (by norm_num)) β (iwCutoffScale C r k Q) ha f)
      (iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period)))
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
    eLpNorm (initialTemporalMaximum (fun j => iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j)
      (one_le_pow₀ (by norm_num)) β (iwCutoffScale C r k Q) ha f)
      (iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period)))
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count≤
      ENNReal.ofReal (iwFiniteLowConstant Z R*iwMaximalCost C r k Q)*
        eLpNorm (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  have hc : 1≤ Real.log C := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hCe
  have hL := iwDenominatorBound_log_one_le hC hc hk hQ
  obtain ⟨hm,hn⟩ := analytic_iw_short_scale_maximum hC hZ hR HIW HCZ HY HRM hr hk d ν hν hβ0 hβ1
    (iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period)) f hf ha
  refine ⟨hm,hn.trans ?_⟩
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (analytic_iw_short_transition_cost_bound hC hZ hR hr hQ hL d)) _

theorem analytic_iw_finite_input_low_majorant {C Z R H S : ℝ} (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k) (hQ : 1 ≤ Q)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
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
  obtain ⟨GN, hGN0, hGNm, hGNdom, hGNnorm⟩ := analytic_iw_narrow_integer_majorant hC hH hS HIW Hmajor
    HShannon HHL HY hr hk d ν hν hβ0.le hβ1 F f hf ha hb
  obtain ⟨GR, hGR0, hGRm, hGRdom, hGRnorm⟩ := analytic_iw_large_remainder_majorant hC HIW HY HRT hr hk
    d ν hν hβ0 hβ1 (finiteInputLp F f 2) hf ha hb
  have hshort := analytic_iw_short_transition_maximum hC hCe hZ hR HIW HCZ HY HRM hr hk hQ
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

theorem analytic_iw_full_low_maximal_bound {C Z R H S : ℝ} (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k) (hQ : 1 ≤ Q)
    (d : AnalyticTaoArcData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν ≤ 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (ha : 2 ≤ iwCutoffScale C r k Q) :
    AllInputLpMaximalBound (fun j => iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j)
      (one_le_pow₀ (by norm_num)) β (iwCutoffScale C r k Q) ha)
      (ENNReal.ofReal (iwNearOneExponent r)) (iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q) := by
  apply finite_input_maximal_extension _ (iwNearOneExponent_toReal_pos hr)
  intro F f
  exact analytic_iw_finite_input_low_majorant hC hCe hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
    hr hk hQ d ν hν hβ0 hβ1 F f (finiteInputLp_count_memLp F f (iwNearOneExponent_toReal_pos hr)) ha

end PrimeSquares
