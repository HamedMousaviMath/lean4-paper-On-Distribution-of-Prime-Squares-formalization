import PrimeSquares.PositiveAverageStrongExtension
import PrimeSquares.TheoremSevenTwo

set_option autoImplicit false
open scoped ENNReal lp
namespace PrimeSquares

def PositiveStrongMaximalBound (A : PositiveAverageFamily) (p B : ℝ) : Prop :=
  ∀ f : ℓ^(ENNReal.ofReal p)(ℤ,ℂ), ∃ g : ℓ^(ENNReal.ofReal p)(ℤ,ℝ),
    (g : ℤ → ℝ) = positiveMaximal A (f : ℤ → ℂ) ∧ ‖g‖ ≤ B*‖f‖

theorem section7_strong_assembly {C C₀ K : ℝ} (hC : 1 ≤ C) (hC₀ : 1 ≤ C₀) (hK : 1 ≤ K)
    (H : SectionSevenOrliczConclusion C C₀ K) :
    ∃ D : ℝ, 0 < D ∧ ∀ A : PositiveAverageFamily, IsSectionSevenFamily A →
      ∀ p : ℝ, 1 < p → p ≤ 2 →
      PositiveStrongMaximalBound A p (Real.exp (D/(p-1)*Real.log (Real.exp 1/(p-1)))) := by
  refine ⟨nearOneStrongConstant C C₀ K, nearOneStrongConstant_pos hC hC₀ hK, ?_⟩
  intro A hA p hp hp2
  exact positiveAverage_finite_strong_extension A hp hp2 (Real.exp_pos _).le
    (fun F f hf => actual_finite_strong_maximal_norm A hC hC₀ hK (H A hA).1 F f hf hp hp2)

theorem corollary_7_6 {c C Cb E Z R H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput) :
    ∃ Cnorm : ℝ, 0 < Cnorm ∧ ∀ A : PositiveAverageFamily, IsSectionSevenFamily A →
      ∀ p : ℝ, 1 < p → p ≤ 2 →
      PositiveStrongMaximalBound A p (Real.exp (Cnorm/(p-1)*Real.log (Real.exp 1/(p-1)))) := by
  obtain ⟨Cg, C₀, K, hCg, hC₀, hK, hT⟩ := theorem_7_2 D hC hCe hCb HB hE HE hc HP HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
  exact section7_strong_assembly hCg hC₀ hK hT

end PrimeSquares
