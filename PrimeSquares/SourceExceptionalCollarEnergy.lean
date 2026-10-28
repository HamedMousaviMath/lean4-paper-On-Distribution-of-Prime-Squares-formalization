import PrimeSquares.SourceExceptionalCollarIdentity
open Finset
namespace PrimeSquares
theorem sourceExceptionalCollar_energy {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε) (hhalf : η+ε < 1/2) :
    ∃ H : ℝ,0 < H ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),0 < Q → ∀ (q₀ : ℕ),0 < q₀ →
    ∀ (R : ℕ → ℝ),(∀ j,effectiveCollarCutoff Q q₀ ≤ R j) →
    ∀ (active : ℕ → Bool) (χ : ∀ _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℕ → ℝ),
      (∀ j,0 ≤ β j) → (∀ j,β j ≤ 1) → ∀ (J : Finset ℕ) (θ : PrimeCircle),
      (∑ j ∈ J,‖circleExceptionalHighModel ((sourceRationalCenters (R j)).filter
        (fun r => (r.den : ℝ) ≤ effectiveCollarCutoff Q q₀)) ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) q₀ Q (conductorMajorant q₀) (χ j)
        (sourceExceptionalSelector q₀ (active j)) (β j) θ‖^2) ≤ (H*Q^(-η)*(q₀ : ℝ)^(-ε))^2 := by
  obtain ⟨H,hH,h⟩ := refinedTwistedCollar_energy hη hε hhalf
  refine ⟨H,hH,?_⟩
  intro M hM Q hQ q₀ hq₀ R hR active χ β hβ0 hβ1 J θ
  simp_rw [source_exceptional_collar_identity _ _ hQ hq₀ (hR _)]
  exact h M hM Q hQ q₀ hq₀ (fun j _ => β j) (fun j _ _ => hβ0 j) (fun j _ _ => hβ1 j)
    χ (fun j => sourceExceptionalSelector q₀ (active j)) (fun j r _ => sourceExceptionalSelector_norm q₀ (active j) r) J θ
end PrimeSquares
