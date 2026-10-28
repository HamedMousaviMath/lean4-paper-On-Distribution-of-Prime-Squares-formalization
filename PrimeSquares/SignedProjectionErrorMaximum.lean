import PrimeSquares.RationalProjectionErrorMaximum
open scoped lp
namespace PrimeSquares
theorem signedProjectionErrorBlock_maximum {M : ℕ} (hM : 2 ≤ M) {s : ℕ} (hs : 2 ≤ s)
    (Γ : Finset ℚ) (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (β : ℕ → ℚ → ℝ) (hβ0 : ∀ j,∀ r ∈ Γ,0 ≤ β j r) (hβ1 : ∀ j,∀ r ∈ Γ,β j r ≤ 1)
    (c₀ c₁ : ℕ → ℚ → ℂ) {A₀ A₁ : ℝ} (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hb₀ : ∀ j,∀ r ∈ Γ,‖c₀ j r‖ ≤ A₀) (hb₁ : ∀ j,∀ r ∈ Γ,‖c₁ j r‖ ≤ A₁)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier
        (rationalProjectionErrorBlock Γ ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) s (fun _ => 1) (c₀ j)-
         rationalProjectionErrorBlock Γ ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) (c₁ j)) f x‖ ≤ g x) ∧
      ‖g‖ ≤ ((A₀+A₁)*annularProjectionErrorL2Constant)*‖f‖ := by
  obtain ⟨g₀,hg₀,ht₀,hn₀⟩ := rationalProjectionErrorBlock_maximum hM hs Γ hc hd
    (fun _ _ => 1) (fun _ _ _ => by norm_num) (fun _ _ _ => le_rfl) c₀ hA₀ hb₀ f
  obtain ⟨g₁,hg₁,ht₁,hn₁⟩ := rationalProjectionErrorBlock_maximum hM hs Γ hc hd β hβ0 hβ1 c₁ hA₁ hb₁ f
  refine ⟨g₀+g₁,fun x => add_nonneg (hg₀ x) (hg₁ x),?_,?_⟩
  · intro j x
    rw [integerMultiplier_sub]
    change ‖integerMultiplier _ f x-integerMultiplier _ f x‖ ≤ g₀ x+g₁ x
    exact (norm_sub_le _ _).trans (add_le_add (ht₀ j x) (ht₁ j x))
  · exact (norm_add_le _ _).trans ((add_le_add hn₀ hn₁).trans_eq (by ring))
end PrimeSquares
