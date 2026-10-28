import PrimeSquares.CombinedSourceCollarMaximum
open Finset
namespace PrimeSquares
theorem combinedSourceCollar_indicator_pairing {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 < ε) (hhalf : η+ε < 1/2) :
    ∃ K : ℝ,0 < K ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),1 ≤ Q →
    ∀ (q₀ : ℕ → ℕ),(∀ i,2^i ≤ q₀ i) → ∀ (R : ℕ → ℝ),(∀ j,0 ≤ R j) →
    ∀ (active : ℕ → ℕ → Bool) (χ : ∀ _i _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den)
      (β : ℕ → ℕ → ℝ),(∀ i j,0 ≤ β i j) → (∀ i j,β i j ≤ 1) →
    ∀ (σ : ℕ → ℕ) (F : Finset ℤ),∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (sourceCollarDifference ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) Q (R j) (q₀ (σ j))
        (active (σ j) j) (χ (σ j) j) (β (σ j) j)) (finiteIndicatorLp F 2) x‖) ∧
      ∀ G : Finset ℤ,(∑ x ∈ G,g x) ≤ K*Q^(-η)*Real.sqrt F.card*Real.sqrt G.card := by
  obtain ⟨K,hK,h⟩ := combinedSourceCollar_energy hη hε hhalf
  refine ⟨K,hK,?_⟩
  intro M hM Q hQ q₀ hclass R hR active χ β hβ0 hβ1 σ F
  obtain ⟨g,hg,_,hb⟩ := circle_energy_indicator_maximal_pairing _ (by positivity)
    (h M hM Q hQ q₀ hclass R hR active χ β hβ0 hβ1 σ) F
  exact ⟨g,hg,hb⟩
end PrimeSquares
