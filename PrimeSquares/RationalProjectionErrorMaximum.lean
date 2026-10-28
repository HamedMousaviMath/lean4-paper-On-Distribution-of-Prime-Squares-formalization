import PrimeSquares.RationalProjectionErrorEnergy
import PrimeSquares.CircleAnnularErrorMaximum
open scoped lp
namespace PrimeSquares
theorem rationalProjectionErrorBlock_maximum {M : ℕ} (hM : 2 ≤ M) {s : ℕ} (hs : 2 ≤ s)
    (Γ : Finset ℚ) (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (β : ℕ → ℚ → ℝ) (hβ0 : ∀ j,∀ r ∈ Γ,0 ≤ β j r) (hβ1 : ∀ j,∀ r ∈ Γ,β j r ≤ 1)
    (c : ℕ → ℚ → ℂ) {A : ℝ} (hA : 0 ≤ A) (hb : ∀ j,∀ r ∈ Γ,‖c j r‖ ≤ A)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (rationalProjectionErrorBlock Γ ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) (c j)) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (A*annularProjectionErrorL2Constant)*‖f‖ := by
  obtain ⟨g,_,hg,ht,hn⟩ := circle_energy_maximal_witness
    (fun j => rationalProjectionErrorBlock Γ ((2 : ℕ)^j*M)
      (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) (c j))
    (mul_nonneg hA annularProjectionErrorL2Constant_pos.le) (fun J θ => by
      rw [mul_pow,annularProjectionErrorL2Constant_sq]
      exact rationalProjectionErrorBlock_finite_energy hM hs Γ hc hd β hβ0 hβ1 c hA hb J θ) f
  exact ⟨g,hg,ht,hn⟩
end PrimeSquares
