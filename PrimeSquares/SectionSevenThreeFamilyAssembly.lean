import PrimeSquares.IWThreeFamilyRestrictedGauge
import PrimeSquares.SectionSevenDeductions

set_option autoImplicit false
open Finset
namespace PrimeSquares

def SectionSevenOrliczConclusion (C C₀ K : ℝ) : Prop :=
  ∀ A : PositiveAverageFamily, IsSectionSevenFamily A →
    (∀ (F : Finset ℤ) (f : ℤ → ℂ), (∀ x, x ∉ F → f x = 0) →
      ∀ level : ℝ, 0 < level →
      {x | level < positiveMaximal A f x}.Finite ∧
      ({x | level < positiveMaximal A f x}.ncard : ℝ) ≤
        K*∑ x ∈ F.filter (fun x => level/C₀ < ‖f x‖), nearOnePsi C (‖f x‖/level)) ∧
    (∀ (F : Finset ℤ) (f : ℤ → ℂ), (∀ x, x ∉ F → f x = 0) →
      ∀ level : ℝ, 0 < level →
      {x | level < positiveMaximal A f x}.Finite ∧
      ({x | level < positiveMaximal A f x}.ncard : ℝ) ≤
        K*∑ x ∈ F, nearOnePsi C (‖f x‖/level)) ∧
    (∀ (F : Finset ℤ) (t : ℝ), 1 ≤ t →
      {x | 1/t < positiveMaximal A (finiteIndicator F) x}.Finite ∧
      ({x | 1/t < positiveMaximal A (finiteIndicator F) x}.ncard : ℝ) ≤
        K*(F.card : ℝ)*nearOnePsi C t)

theorem sectionSevenFamily_mass_cases {A : PositiveAverageFamily} (hA : IsSectionSevenFamily A) :
    A.mass = primeSquareChebyshevConstant ∨ A.mass = 1 := by
  rcases hA with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

theorem sectionSevenFamily_mass_le {A : PositiveAverageFamily} (hA : IsSectionSevenFamily A) :
    A.mass ≤ primeSquareChebyshevConstant := by
  rcases sectionSevenFamily_mass_cases hA with hm | hm
  · rw [hm]
  · rw [hm]
    exact mangoldtPositiveFamily.mass_one_le

theorem section7_three_family_assembly {Cg Rg : ℝ} (hC : 1 ≤ Cg) (hR : 1 ≤ Rg)
    (H : ∀ A : PositiveAverageFamily, IsSectionSevenFamily A → PositiveRestrictedGauge A Cg Rg) :
    ∃ C C₀ K : ℝ, 1 ≤ C ∧ 1 ≤ C₀ ∧ 1 ≤ K ∧ SectionSevenOrliczConclusion C C₀ K := by
  classical
  let C := 9*Cg+4
  let C₀ := 2*primeSquareChebyshevConstant
  let Lm := layerGaugeConstant Cg (2*primeSquareChebyshevConstant)
  let Lo := layerGaugeConstant Cg 2
  let K := 1+Rg+Rg*Lm+Rg*Lo
  have hC0 : 0 ≤ Cg := by linarith
  have hR0 : 0 ≤ Rg := by linarith
  have hmass : 1 ≤ primeSquareChebyshevConstant := mangoldtPositiveFamily.mass_one_le
  have hLm : 0 < Lm := layerGaugeConstant_pos _ _
  have hLo : 0 < Lo := layerGaugeConstant_pos _ _
  have hRm : 0 ≤ Rg*Lm := mul_nonneg hR0 hLm.le
  have hRo : 0 ≤ Rg*Lo := mul_nonneg hR0 hLo.le
  have hK1 : 1 ≤ K := by dsimp [K]; linarith
  have hKR : Rg ≤ K := by dsimp [K]; linarith
  have hCm : Cg ≤ C := by dsimp [C]; linarith
  refine ⟨C, C₀, K, by dsimp [C]; linarith, by dsimp [C₀]; linarith, hK1, ?_⟩
  intro A hA
  have hAg := H A hA
  have hcoef : Rg*layerGaugeConstant Cg (2*A.mass) ≤ K := by
    rcases sectionSevenFamily_mass_cases hA with hm | hm
    · rw [hm]
      change Rg*Lm ≤ K
      dsimp [K]
      linarith
    · rw [hm, mul_one]
      change Rg*Lo ≤ K
      dsimp [K]
      linarith
  have hcoef0 : 0 ≤ Rg*layerGaugeConstant Cg (2*A.mass) :=
    mul_nonneg hR0 (layerGaugeConstant_pos _ _).le
  refine ⟨?_, ?_, ?_⟩
  · intro F f hf level hl
    obtain ⟨hfinite, hbound⟩ := section7_truncated_modular_finite_card A hC0 hR0 hAg F f hf hl
    refine ⟨hfinite, hbound.trans ?_⟩
    have hthreshold : level/C₀ ≤ level/(2*A.mass) := by
      apply div_le_div_of_nonneg_left hl.le
      · have := A.mass_one_le
        linarith
      · dsimp [C₀]
        linarith [sectionSevenFamily_mass_le hA]
    have hsum : (∑ x ∈ F.filter (fun x => level/(2*A.mass) < ‖f x‖), nearOnePsi C (‖f x‖/level)) ≤
        ∑ x ∈ F.filter (fun x => level/C₀ < ‖f x‖), nearOnePsi C (‖f x‖/level) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        obtain ⟨hx, hval⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨hx, hthreshold.trans_lt hval⟩
      · intro x _ _
        exact nearOnePsi_nonneg _ (div_nonneg (norm_nonneg _) hl.le)
    exact (mul_le_mul_of_nonneg_left hsum hcoef0).trans
      (mul_le_mul_of_nonneg_right hcoef (sum_nonneg (fun x _ => nearOnePsi_nonneg _ (div_nonneg (norm_nonneg _) hl.le))))
  · intro F f hf level hl
    obtain ⟨hfinite, hbound⟩ := section7_modular_finite_card A hC0 hR0 hAg F f hf hl
    refine ⟨hfinite, hbound.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hcoef
      (sum_nonneg (fun x _ => nearOnePsi_nonneg C (div_nonneg (norm_nonneg _) hl.le)))
  · intro F t ht
    have hlarge := positiveRestrictedGauge_enlarge A hCm hKR hR0 hAg
    exact testedDistribution_iff.mp (hlarge F t ht)

end PrimeSquares
