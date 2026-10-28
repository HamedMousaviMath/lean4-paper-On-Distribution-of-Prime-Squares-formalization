import PrimeSquares.DyadicConductorCollar
open Finset
namespace PrimeSquares
theorem changingConductorCollar_energy {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 < ε) (hhalf : η+ε < 1/2) :
    ∃ K : ℝ,0 < K ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),0 < Q →
    ∀ (q₀ : ℕ → ℕ),(∀ i,2^i ≤ q₀ i) →
    ∀ (β : ℕ → ℕ → ℚ → ℝ),
      (∀ i j,∀ r ∈ conductorCollarCenters Q (q₀ i),0 ≤ β i j r) →
      (∀ i j,∀ r ∈ conductorCollarCenters Q (q₀ i),β i j r ≤ 1) →
    ∀ (χ : ∀ _i _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℕ → ℕ → ℚ → ℂ),
      (∀ i j,∀ r ∈ conductorCollarCenters Q (q₀ i),‖κ i j r‖ ≤ 1) →
    ∀ (σ : ℕ → ℕ) (J : Finset ℕ) (θ : PrimeCircle),
      (∑ j ∈ J,‖dyadicConductorCollar M hM Q (q₀ (σ j)) (β (σ j)) (χ (σ j)) (κ (σ j)) j θ‖^2) ≤
        (K*Q^(-η))^2 := by
  obtain ⟨H,hH,h⟩ := dyadicConductorCollar_energy hη hε.le hhalf
  refine ⟨H*conductorClassEnergyConstant ε,mul_pos hH (conductorClassEnergyConstant_pos hε),?_⟩
  intro M hM Q hQ q₀ hclass β hβ0 hβ1 χ κ hk σ J θ
  have he := mixed_circle_square_energy hε q₀ hclass
    (fun j i => dyadicConductorCollar M hM Q (q₀ i) (β i) (χ i) (κ i) j)
    (fun i => h M hM Q hQ (q₀ i) (conductor_class_positive q₀ hclass i) (β i) (hβ0 i) (hβ1 i) (χ i) (κ i) (hk i)) σ J θ
  convert he using 1; ring
end PrimeSquares
