import PrimeSquares.ContinuousAnnularSignedKernel

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

def KernelHormanderBound (K : ℝ→ℂ) (H : ℝ) : Prop :=
  ∀ h : ℝ,Integrable (farKernelTranslation K h) volume ∧
    (∫ x,farKernelTranslation K h x)≤H

theorem continuousAnnularSignedKernel_hormander {β : ℝ}
    (hβ0 : 0<β) (hβ1 : β≤1) (J : ℕ) (σ : ℕ→ℂ)
    (hσ : ∀ j∈range J,‖σ j‖≤1) :
    KernelHormanderBound (continuousAnnularSignedKernel β J σ) 50 := by
  intro h
  have hi := farKernelTranslation_integrable (continuousAnnularSignedKernel_integrable β J σ) h
  refine ⟨hi,?_⟩
  have hs (j : ℕ) (_hj : j∈range J) :
      Integrable (fun x => annularFarTranslation ((2 : ℕ)^(j+1)) β h x+
        annularFarTranslation ((2 : ℕ)^j) β h x) volume :=
    (annularFarTranslation_integrable (N := (2 : ℕ)^(j+1)) (one_le_pow₀ (by norm_num)) β h).fun_add
      (annularFarTranslation_integrable (N := (2 : ℕ)^j) (one_le_pow₀ (by norm_num)) β h)
  calc
    _ ≤ ∫ x,∑ j∈range J,(annularFarTranslation ((2 : ℕ)^(j+1)) β h x+
        annularFarTranslation ((2 : ℕ)^j) β h x) :=
      integral_mono hi (integrable_finsetSum (range J) hs)
        (continuousAnnularSignedKernel_far_bound β J σ hσ h)
    _ = ∑ j∈range J,((∫ x,annularFarTranslation ((2 : ℕ)^(j+1)) β h x)+
        ∫ x,annularFarTranslation ((2 : ℕ)^j) β h x) := by
      rw [integral_finsetSum (range J) hs]
      apply sum_congr rfl
      intro j _
      exact integral_add
        (annularFarTranslation_integrable (one_le_pow₀ (by norm_num)) β h)
        (annularFarTranslation_integrable (one_le_pow₀ (by norm_num)) β h)
    _ = (∑ j∈range J,∫ x,annularFarTranslation ((2 : ℕ)^(j+1)) β h x)+
        ∑ j∈range J,∫ x,annularFarTranslation ((2 : ℕ)^j) β h x := sum_add_distrib
    _ ≤ 50 := by
      have h1 := annularFarTranslation_dyadic_sum hβ0.le hβ1 h J
      have h2 := annularFarTranslation_all_dyadic_sum hβ0 hβ1 h J
      linarith

end PrimeSquares
