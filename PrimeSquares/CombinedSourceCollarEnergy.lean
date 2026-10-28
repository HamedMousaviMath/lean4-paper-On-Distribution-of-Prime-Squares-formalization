import PrimeSquares.SourceCollarDifference
open Finset
namespace PrimeSquares
theorem combinedSourceCollar_energy {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 < ε) (hhalf : η+ε < 1/2) :
    ∃ K : ℝ,0 < K ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),1 ≤ Q →
    ∀ (q₀ : ℕ → ℕ),(∀ i,2^i ≤ q₀ i) → ∀ (R : ℕ → ℝ),(∀ j,0 ≤ R j) →
    ∀ (active : ℕ → ℕ → Bool) (χ : ∀ _i _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den)
      (β : ℕ → ℕ → ℝ),(∀ i j,0 ≤ β i j) → (∀ i j,β i j ≤ 1) →
    ∀ (σ : ℕ → ℕ) (J : Finset ℕ) (θ : PrimeCircle),
      (∑ j ∈ J,‖sourceCollarDifference ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) Q (R j) (q₀ (σ j))
        (active (σ j) j) (χ (σ j) j) (β (σ j) j) θ‖^2) ≤ (K*Q^(-η))^2 := by
  have hηhalf : η < 1/2 := by linarith
  obtain ⟨O,hO,ho⟩ := ordinaryGaussCollar_uniform_energy hη hηhalf
  obtain ⟨E,hE,he⟩ := changingSourceCollar_energy hη hε hhalf
  refine ⟨2*(O+E),by positivity,?_⟩
  intro M hM Q hQ q₀ hclass R hR active χ β hβ0 hβ1 σ J θ
  have hordinary := ho M hM Q hQ (canonicalRationalCenters ⌊Q⌋₊)
    (fun r hr => (mem_canonicalRationalCenters ⌊Q⌋₊ r).mp hr)
    (fun _ _ => 1) (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num)
    (fun _ _ => 1) (fun _ _ _ => by norm_num)
  simp only [one_mul] at hordinary
  have hexception := he M hM Q (by linarith) q₀ hclass R hR active χ β hβ0 hβ1 σ
  have hb := difference_circle_energy _ _ (by positivity : 0 ≤ O*Q^(-η)) (by positivity : 0 ≤ E*Q^(-η))
    hordinary hexception J θ
  unfold sourceCollarDifference
  convert hb using 1; ring
end PrimeSquares
