import PrimeSquares.CyclicFullSquareCoefficients
import PrimeSquares.IWAllInputLowMaximum

set_option autoImplicit false
open Finset MeasureTheory
open scoped ENNReal lp
namespace PrimeSquares

noncomputable def iwFullSquareLowOperator (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 2 ≤ a) : ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ) :=
  iwAnnularLowOperator S k P (cyclicFullSquareMeasure P) N hN 1 a ha

noncomputable def iwFullSquareHighOperator (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 2 ≤ a) : ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ) :=
  annularWeightedSquareAverage (P := 2) (by norm_num) N (fun _ => 1)-
    iwFullSquareLowOperator S k P N hN a ha

theorem iwFullSquare_decomposition (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 2 ≤ a) :
    annularWeightedSquareAverage (P := 2) (by norm_num) N (fun _ => 1) =
      iwFullSquareLowOperator S k P N hN a ha+iwFullSquareHighOperator S k P N hN a ha := by
  unfold iwFullSquareHighOperator
  abel

theorem iw_full_square_width_symbol {C ρ : ℝ} {k Q : ℕ}
    (d : TaoArcConstructionData C ρ k Q) [NeZero d.period]
    (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 2 ≤ a) :
    weightedWidthAnnularBlock (iwFrequencySet d.S k) N hN 1 a ha
      (cyclicRationalCoefficient d.period (cyclicFullSquareMeasure d.period)) =
      weightedWidthAnnularBlock (iwFrequencySet d.S k) N hN 1 a ha rationalFullSquareGauss := by
  unfold weightedWidthAnnularBlock
  apply sum_congr rfl
  intro r hr
  rw [cyclicRationalCoefficient_fullSquare r (d.periodic r hr)]

theorem iw_full_square_low_maximal_bound {C Z R H S : ℝ} (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k) (hQ : 1 ≤ Q)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (ha : 2 ≤ iwCutoffScale C r k Q) :
    AllInputLpMaximalBound (fun j => iwFullSquareLowOperator d.S k d.period ((2 : ℕ)^j)
      (one_le_pow₀ (by norm_num)) (iwCutoffScale C r k Q) ha)
      (ENNReal.ofReal (iwNearOneExponent r)) (iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q) := by
  exact iw_full_low_maximal_bound hC hCe hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
    hr hk hQ d (cyclicFullSquareMeasure d.period) (cyclicFullSquareMeasure_variation_le_one d.period)
    (by norm_num) (by norm_num) ha

noncomputable def iwFullSquareModelConstant (Cb : ℝ) : ℝ :=
  4*annularPowerConstant Cb (1/8)+24/Real.pi

theorem iwFullSquareModelConstant_pos {Cb : ℝ} (hCb : 0 ≤ Cb) :
    0 < iwFullSquareModelConstant Cb := by
  have h := annularPowerConstant_pos hCb (1/8)
  unfold iwFullSquareModelConstant
  positivity

theorem iw_full_square_model_comparison {C Cb : ℝ} (hC : 2 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) {r k Q M : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (hQ : 2^k ≤ Q) (hM : 2 ≤ M) (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (hbudget : ((Q : ℝ)+1)^2*iwCutoffScale C r k Q*(Q : ℝ) ≤ (M : ℝ)^2)
    (R : ℕ → ℝ) (hR : ∀ j, (Q : ℝ) ≤ R j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2, (∀ x, 0 ≤ g x) ∧
      (∀ j x, ‖(integerMultiplier
        (varyingIndexAnnularBlock (sourceRationalCenters (R j)) ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j; omega) 1 rationalFullSquareGauss)-
        iwFullSquareLowOperator d.S k d.period ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j; omega) (iwCutoffScale C r k Q)
          (by have h := iwCutoffScale_four_le hC hr k Q; linarith)) f x‖ ≤ g x) ∧
      ‖g‖ ≤ iwFullSquareModelConstant Cb*(Q : ℝ)^(-(1/4 : ℝ))*‖f‖ := by
  obtain ⟨g, hg, ht, hn⟩ := iw_quantitative_model_comparison hC hCb HB (by norm_num : (0 : ℝ) ≤ 2)
    hr hk hQ hM d hbudget (fun _ => 1) (fun _ => by norm_num) (fun _ => le_rfl)
    rationalFullSquareGauss (fun t _ => rationalFullSquareGauss_decay t)
    (fun t _ => rationalFullSquareGauss_norm_one t) R hR f
  refine ⟨g, hg, ?_, ?_⟩
  · intro j x
    rw [iwFullSquareLowOperator, iwAnnularLowOperator, iw_full_square_width_symbol, ←integerMultiplier_sub]
    exact ht j x
  · convert hn using 1
    unfold iwFullSquareModelConstant
    ring

end PrimeSquares
