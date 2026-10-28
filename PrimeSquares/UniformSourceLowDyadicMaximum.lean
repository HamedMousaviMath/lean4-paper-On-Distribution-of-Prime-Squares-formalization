import PrimeSquares.DyadicActualLowMaximum

open scoped lp
namespace PrimeSquares

theorem actualSourceLow_uniform_dyadic_maximum {c : ℝ} (hc : 0 < c) :
    ∃ M₀ : ℕ,4 ≤ M₀ ∧ ∀ (M : ℕ),M₀ ≤ M → ∀ (hM : 2 ≤ M) (Q : ℝ),2 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log M) →
    ∀ (q₀ : ℕ → ℕ),(∀ j,0 < q₀ j) → ∀ χ : ∀ j,DirichletCharacter ℂ (q₀ j),
      (∀ j,(χ j).IsQuadratic) → ∀ (active : ℕ → Bool) (β : ℕ → ℝ),(∀ j,β j ≤ 1) → ∀ f : ℓ¹(ℤ,ℂ),
      ∃ g : lp (fun _ : ℤ => ℝ) ⊤,
        (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (circleLowModel
          (sourceRationalCenters (sourceMajorArcScale (((2 : ℕ)^j*M : ℕ) : ℝ) Q)) ((2 : ℕ)^j*M)
          (by have hh := dyadic_annular_scale_lower hM j;omega) (q₀ j) Q (conductorMajorant (q₀ j))
          (sourceInducedCharacter (q₀ j) (χ j)) (sourceExceptionalSelector (q₀ j) (active j)) (β j))
          (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x‖) ∧
        ‖g‖ ≤ 2*realLowAmplitude M Q*‖f‖ := by
  obtain ⟨M₀,hM₀,hh⟩ := sourceRadius_uniform_dyadic_fourth hc
  refine ⟨M₀,hM₀,?_⟩
  intro M hm hM Q hQ hlog q₀ hq₀ χ hχ active β hβ f
  exact dyadicActualLow_countable_maximum hM hQ (hh M hm Q (by linarith) hlog) q₀ hq₀ χ hχ active β hβ f

end PrimeSquares
