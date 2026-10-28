import PrimeSquares.TheoremSevenTwo

set_option autoImplicit false
open Finset
namespace PrimeSquares

def SourceSectionSevenOrliczConclusion (C C₀ K : ℝ) : Prop :=
  ∀ A : PositiveAverageFamily, IsSectionSevenFamily A →
    (∀ f : ℤ → ℂ, (Function.support f).Finite → ∀ level : ℝ, 0 < level →
      {x | level < positiveMaximal A f x}.Finite ∧
      ({x | level < positiveMaximal A f x}.ncard : ℝ) ≤
        K*∑' x : ℤ, if level/C₀ < ‖f x‖ then nearOnePsi C (‖f x‖/level) else 0) ∧
    (∀ f : ℤ → ℂ, (Function.support f).Finite → ∀ level : ℝ, 0 < level →
      {x | level < positiveMaximal A f x}.Finite ∧
      ({x | level < positiveMaximal A f x}.ncard : ℝ) ≤
        K*∑' x : ℤ, nearOnePsi C (‖f x‖/level)) ∧
    (∀ (F : Finset ℤ) (t : ℝ), 1 ≤ t →
      {x | 1/t < positiveMaximal A (finiteIndicator F) x}.Finite ∧
      ({x | 1/t < positiveMaximal A (finiteIndicator F) x}.ncard : ℝ) ≤
        K*(F.card : ℝ)*nearOnePsi C t)

theorem section7_source_sum_assembly {C C₀ K : ℝ} (H : SectionSevenOrliczConclusion C C₀ K) :
    SourceSectionSevenOrliczConclusion C C₀ K := by
  classical
  intro A hA
  obtain ⟨htruncated, hmodular, hrestricted⟩ := H A hA
  refine ⟨?_, ?_, hrestricted⟩
  · intro f hfs level hl
    let F := hfs.toFinset
    have hf : ∀ x, x ∉ F → f x = 0 := by
      intro x hx
      simpa only [F, Set.Finite.mem_toFinset, Function.mem_support, not_not] using hx
    have he : (∑' x : ℤ, if level/C₀ < ‖f x‖ then nearOnePsi C (‖f x‖/level) else 0) =
        ∑ x ∈ F.filter (fun x => level/C₀ < ‖f x‖), nearOnePsi C (‖f x‖/level) := by
      rw [tsum_eq_sum (s := F) (fun x hx => by
        rw [hf x hx, norm_zero, zero_div, nearOnePsi_zero]
        simp)]
      rw [sum_filter]
    rw [he]
    exact htruncated F f hf level hl
  · intro f hfs level hl
    let F := hfs.toFinset
    have hf : ∀ x, x ∉ F → f x = 0 := by
      intro x hx
      simpa only [F, Set.Finite.mem_toFinset, Function.mem_support, not_not] using hx
    have he : (∑' x : ℤ, nearOnePsi C (‖f x‖/level)) =
        ∑ x ∈ F, nearOnePsi C (‖f x‖/level) := by
      apply tsum_eq_sum
      intro x hx
      rw [hf x hx, norm_zero, zero_div, nearOnePsi_zero]
    rw [he]
    exact hmodular F f hf level hl

theorem theorem_7_2_finitely_supported {c C Cb E Z R H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput) :
    ∃ Cg C₀ K : ℝ, 1 ≤ Cg ∧ 1 ≤ C₀ ∧ 1 ≤ K ∧ SourceSectionSevenOrliczConclusion Cg C₀ K := by
  obtain ⟨Cg, C₀, K, hCg, hC₀, hK, hT⟩ := theorem_7_2 D hC hCe hCb HB hE HE hc HP HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
  exact ⟨Cg, C₀, K, hCg, hC₀, hK, section7_source_sum_assembly hT⟩

end PrimeSquares
