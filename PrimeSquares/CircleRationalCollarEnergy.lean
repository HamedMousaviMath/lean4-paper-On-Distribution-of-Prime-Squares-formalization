import PrimeSquares.CircleRationalCollarBlock

open Finset
namespace PrimeSquares

theorem rationalCollarBlock_finite_energy {M : ℕ} (hM : 2 ≤ M) (Γ : Finset ℚ) (s : ℕ)
    (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) (hlog : ∀ r ∈ Γ,Nat.log2 r.den=s)
    {Q b U : ℝ} (hQ : 0 < Q) (hden : ∀ r ∈ Γ,(r.den : ℝ) ≤ U)
    (β : ℕ → ℚ → ℝ) (hβ0 : ∀ j,∀ r ∈ Γ,0 ≤ β j r) (hβ1 : ∀ j,∀ r ∈ Γ,β j r ≤ 1)
    (c : ℕ → ℚ → ℂ) (hc : ∀ j,∀ r ∈ Γ,‖c j r‖ ≤ b) (J : Finset ℕ) (θ : PrimeCircle) :
    (∑ j ∈ J,‖rationalCollarBlock Γ ((2 : ℕ)^j*M)
      (by have hh := dyadic_annular_scale_lower hM j;omega) Q (β j) (c j) θ‖^2) ≤
      (96*b*U/(Real.pi*Q))^2 := by
  obtain ⟨ξ,hξ,rfl⟩ := primeCircle_representative θ
  have hw (j : ℕ) := rationalCollarBlock_real_window Γ ((2 : ℕ)^j*M)
    (by have hh := dyadic_annular_scale_lower hM j;omega) Q (β j) (c j) hΓ ⟨hξ.1,hξ.2.le⟩
  have h1 := rationalCollarBlock_real_energy hM Γ s hΓ hlog hQ hden β hβ0 hβ1 c hc J (ξ-1)
  have h2 := rationalCollarBlock_real_energy hM Γ s hΓ hlog hQ hden β hβ0 hβ1 c hc J ξ
  have h3 := rationalCollarBlock_real_energy hM Γ s hΓ hlog hQ hden β hβ0 hβ1 c hc J (ξ+1)
  calc
    _ = ∑ j ∈ J,‖(∑ r ∈ Γ,c j r*annularCollarSymbol ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega)
        (β j r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ-1-(r : ℝ)))+
        (∑ r ∈ Γ,c j r*annularCollarSymbol ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega)
        (β j r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ-(r : ℝ)))+
        (∑ r ∈ Γ,c j r*annularCollarSymbol ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega)
        (β j r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ+1-(r : ℝ)))‖^2 :=
      sum_congr rfl (fun j _ => by rw [hw j])
    _ ≤ ∑ j ∈ J,3*(‖∑ r ∈ Γ,c j r*annularCollarSymbol ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega)
        (β j r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ-1-(r : ℝ))‖^2+
        ‖∑ r ∈ Γ,c j r*annularCollarSymbol ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega)
        (β j r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ-(r : ℝ))‖^2+
        ‖∑ r ∈ Γ,c j r*annularCollarSymbol ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega)
        (β j r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ+1-(r : ℝ))‖^2) :=
      sum_le_sum (fun _ _ => norm_three_sum_square _ _ _)
    _ ≤ (96*b*U/(Real.pi*Q))^2 := by
      rw [←mul_sum,sum_add_distrib,sum_add_distrib]
      have he : (96*b*U/(Real.pi*Q))^2=9*(32*b*U/(Real.pi*Q))^2 := by ring
      rw [he]
      linarith

end PrimeSquares
