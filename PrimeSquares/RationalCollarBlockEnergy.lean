import PrimeSquares.SourceBroadCutoffNorm

open Finset
namespace PrimeSquares

theorem rationalCollarBlock_real_energy {M : ℕ} (hM : 2 ≤ M) (Γ : Finset ℚ) (s : ℕ)
    (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) (hlog : ∀ r ∈ Γ,Nat.log2 r.den=s)
    {Q b U : ℝ} (hQ : 0 < Q) (hden : ∀ r ∈ Γ,(r.den : ℝ) ≤ U)
    (β : ℕ → ℚ → ℝ) (hβ0 : ∀ j,∀ r ∈ Γ,0 ≤ β j r) (hβ1 : ∀ j,∀ r ∈ Γ,β j r ≤ 1)
    (c : ℕ → ℚ → ℂ) (hc : ∀ j,∀ r ∈ Γ,‖c j r‖ ≤ b) (J : Finset ℕ) (ξ : ℝ) :
    (∑ j ∈ J,‖∑ r ∈ Γ,c j r*annularCollarSymbol ((2 : ℕ)^j*M)
      (by have hh := dyadic_annular_scale_lower hM j;omega) (β j r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ-(r : ℝ))‖^2) ≤
      (32*b*U/(Real.pi*Q))^2 := by
  have hE := dyadic_sparse_square_energy Γ ξ s J
    (fun j r => c j r*annularCollarSymbol ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega)
      (β j r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ-(r : ℝ))) (b*(8*U/(Real.pi*Q))) hΓ hlog
  have hh : (∑ j ∈ J,‖∑ r ∈ Γ,c j r*annularCollarSymbol ((2 : ℕ)^j*M)
      (by have hh := dyadic_annular_scale_lower hM j;omega) (β j r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ-(r : ℝ))‖^2) ≤
      (4*(b*(8*U/(Real.pi*Q))))^2 := by
    apply hE
    · intro j _ r _ hz
      rw [annularCollarSymbol_zero_of_broad _ _ _ _ _ _ _ hz,mul_zero]
    · intro r hr
      have hq : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
      have hU : 0 < U := hq.trans_le (hden r hr)
      have hs := collarFactor_weighted_energy hM (fun j => β j r) (fun j => hβ0 j r hr)
        (fun j => hβ1 j r hr) hq hQ
        (fun j => c j r*Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ))))
        (fun j => (sourceBroadCutoff_mul_norm _ _ _).trans (hc j r hr)) J (ξ-(r : ℝ))
      have heq : (∑ j ∈ J,‖c j r*annularCollarSymbol ((2 : ℕ)^j*M)
          (by have hh := dyadic_annular_scale_lower hM j;omega) (β j r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ-(r : ℝ))‖^2)=
          ∑ j ∈ J,‖(c j r*Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ))))*
            annularCollarFactor ((2 : ℕ)^j*M) (β j r) (r.den : ℝ) Q (ξ-(r : ℝ))‖^2 := by
        apply sum_congr rfl
        intro j _
        congr 2
        change c j r*(annularCollarFactor _ _ _ _ _*Complex.ofReal _)=_
        ring
      rw [heq]
      have hu : (8*(r.den : ℝ)/(Real.pi*Q))^2 ≤ (8*U/(Real.pi*Q))^2 :=
        pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hden r hr) (by norm_num)) (by positivity)) 2
      exact hs.trans (by simpa only [mul_pow] using mul_le_mul_of_nonneg_left hu (sq_nonneg b))
  exact hh.trans_eq (by ring)

end PrimeSquares
