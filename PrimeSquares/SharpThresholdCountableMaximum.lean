import PrimeSquares.SharpThresholdFiniteMaximum
import PrimeSquares.FiniteFamilyCountableCriterion

open Finset
open scoped lp
namespace PrimeSquares

theorem sharpThreshold_countable_maximum {C : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C)
    {M : ℕ} (hM : 2 ≤ M) (P : ℚ → Prop) [DecidablePred P]
    {A B Q W : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hQ : 0<Q) (hW : 16 ≤ W)
    (hL : 2 ≤ Real.log Q) (hSlope : gaussThresholdSlope (Real.log Q) ≤ 1/4)
    (d : ℚ → ℕ) (hd : ∀ r,r ∈ Set.Ico (0 : ℚ) 1 → P r → 0<d r)
    (hscale : ∀ r,r ∈ Set.Ico (0 : ℚ) 1 → P r → (r.den : ℝ)/W=(d r : ℝ)*B/Q)
    (c : ℚ → ℂ) (hc : ∀ r,r ∈ Set.Ico (0 : ℚ) 1 → P r →
      ‖c r‖ ≤ A*(d r : ℝ)^(-(1/2 : ℝ))*conductorRho (d r))
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (R : ℕ → ℝ) (hR : ∀ j,0 ≤ R j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (thresholdAnnularBlock ((sourceRationalCenters (R j)).filter P)
        ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) (β j) W c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (sharpThresholdMaximalConstant C*sharpThresholdAmplitude A B Q*(1+Real.log W)^3)*‖f‖ := by
  classical
  have hK := sharpThresholdMaximalConstant_nonneg hC
  have hD := sharpThresholdAmplitude_nonneg hA (by linarith : (0 : ℝ) ≤ B) hQ.le
  have hlW : 0 ≤ Real.log W := Real.log_nonneg (by linarith)
  apply finite_family_countable_maximum _ (by positivity)
  intro J
  let K := J.sup (fun j => ⌊R j⌋₊)
  let Γ := (canonicalRationalCenters K).filter P
  have hcan : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 := fun r hr =>
    ((mem_canonicalRationalCenters _ _).mp (mem_filter.mp hr).1).1
  have hcap : ∀ r ∈ Γ,r.den ≤ K := fun r hr =>
    ((mem_canonicalRationalCenters _ _).mp (mem_filter.mp hr).1).2
  obtain ⟨g,hg,ht,hn⟩ := sharpThreshold_finiteCenters_maximum hC hBourgain hM Γ hcan hcap
    hA hB hQ hW hL hSlope d (fun r hr => hd r (hcan r hr) (mem_filter.mp hr).2)
    (fun r hr => hscale r (hcan r hr) (mem_filter.mp hr).2) c
    (fun r hr => hc r (hcan r hr) (mem_filter.mp hr).2) β hβ0 hβ1 R hR f
  refine ⟨g,hg,?_,hn⟩
  intro j hj x
  have he : Γ.filter (fun r => (r.den : ℝ) ≤ R j)=(sourceRationalCenters (R j)).filter P := by
    ext r
    simp only [Γ,mem_filter,mem_canonicalRationalCenters,mem_sourceRationalCenters (hR j)]
    constructor
    · rintro ⟨⟨⟨hc,_⟩,hp⟩,hr⟩
      exact ⟨⟨hc,hr⟩,hp⟩
    · rintro ⟨⟨hc,hr⟩,hp⟩
      exact ⟨⟨⟨hc,(Nat.le_floor hr).trans (le_sup (f := fun j => ⌊R j⌋₊) hj)⟩,hp⟩,hr⟩
  rw [←he]
  exact ht j x

end PrimeSquares
