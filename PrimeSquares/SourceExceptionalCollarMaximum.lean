import PrimeSquares.SourceExceptionalCollarEnergy
open scoped lp
namespace PrimeSquares
theorem sourceExceptionalCollar_maximum {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε) (hhalf : η+ε < 1/2) :
    ∃ H : ℝ,0 < H ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),0 < Q → ∀ (q₀ : ℕ),0 < q₀ →
    ∀ (R : ℕ → ℝ),(∀ j,effectiveCollarCutoff Q q₀ ≤ R j) →
    ∀ (active : ℕ → Bool) (χ : ∀ _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℕ → ℝ),
      (∀ j,0 ≤ β j) → (∀ j,β j ≤ 1) → ∀ f : ℓ²(ℤ,ℂ),∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (circleExceptionalHighModel ((sourceRationalCenters (R j)).filter
        (fun r => (r.den : ℝ) ≤ effectiveCollarCutoff Q q₀)) ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) q₀ Q (conductorMajorant q₀) (χ j)
        (sourceExceptionalSelector q₀ (active j)) (β j)) f x‖) ∧
      ‖g‖ ≤ H*Q^(-η)*(q₀ : ℝ)^(-ε)*‖f‖ := by
  obtain ⟨H,hH,h⟩ := sourceExceptionalCollar_energy hη hε hhalf
  refine ⟨H,hH,?_⟩
  intro M hM Q hQ q₀ hq₀ R hR active χ β hβ0 hβ1 f
  obtain ⟨g,hg,_,_,hn⟩ := circle_energy_maximal_witness _ (by positivity)
    (h M hM Q hQ q₀ hq₀ R hR active χ β hβ0 hβ1) f
  exact ⟨g,hg,hn⟩
end PrimeSquares
