import PrimeSquares.ClippedSourceCollarMaximum
open Finset
namespace PrimeSquares
theorem changingSourceCollar_energy {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 < ε) (hhalf : η+ε < 1/2) :
    ∃ K : ℝ,0 < K ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),0 < Q →
    ∀ (q₀ : ℕ → ℕ),(∀ i,2^i ≤ q₀ i) → ∀ (R : ℕ → ℝ),(∀ j,0 ≤ R j) →
    ∀ (active : ℕ → ℕ → Bool) (χ : ∀ _i _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den)
      (β : ℕ → ℕ → ℝ),(∀ i j,0 ≤ β i j) → (∀ i j,β i j ≤ 1) →
    ∀ (σ : ℕ → ℕ) (J : Finset ℕ) (θ : PrimeCircle),
      (∑ j ∈ J,‖circleExceptionalHighModel ((sourceRationalCenters (R j)).filter
        (fun r => (r.den : ℝ) ≤ effectiveCollarCutoff Q (q₀ (σ j)))) ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) (q₀ (σ j)) Q (conductorMajorant (q₀ (σ j)))
        (χ (σ j) j) (sourceExceptionalSelector (q₀ (σ j)) (active (σ j) j)) (β (σ j) j) θ‖^2) ≤ (K*Q^(-η))^2 := by
  obtain ⟨H,hH,h⟩ := clippedSourceCollar_energy hη hε.le hhalf
  refine ⟨H*conductorClassEnergyConstant ε,mul_pos hH (conductorClassEnergyConstant_pos hε),?_⟩
  intro M hM Q hQ q₀ hclass R hR active χ β hβ0 hβ1 σ J θ
  have he := mixed_circle_square_energy hε q₀ hclass (fun j i =>
    circleExceptionalHighModel ((sourceRationalCenters (R j)).filter
      (fun r => (r.den : ℝ) ≤ effectiveCollarCutoff Q (q₀ i))) ((2 : ℕ)^j*M)
      (by have hh := dyadic_annular_scale_lower hM j;omega) (q₀ i) Q (conductorMajorant (q₀ i))
      (χ i j) (sourceExceptionalSelector (q₀ i) (active i j)) (β i j))
    (fun i => h M hM Q hQ (q₀ i) (conductor_class_positive q₀ hclass i) R hR (active i) (χ i) (β i) (hβ0 i) (hβ1 i)) σ J θ
  convert he using 1; ring
end PrimeSquares
