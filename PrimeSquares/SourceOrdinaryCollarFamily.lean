import PrimeSquares.OrdinarySourceFilter

open scoped lp
namespace PrimeSquares

theorem sourceOrdinaryCollar_family_maximum {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ < 1/2) :
    ∃ H : ℝ,0 < H ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),1 ≤ Q →
    ∀ R : ℕ → ℝ,(∀ j,Q ≤ R j) → ∀ q₀ : ℕ → ℕ,(∀ j,0 < q₀ j) →
    ∀ B : ℕ → ℝ,(∀ j,0 < B j) →
    ∀ (χ : ∀ _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℕ → ℝ) (f : ℓ²(ℤ,ℂ)),
      ∃ g : lp (fun _ : ℤ => ℝ) 2,
        (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (circleHighModel
          ((sourceRationalCenters (R j)).filter (fun r => (r.den : ℝ) ≤ Q)) ((2 : ℕ)^j*M)
          (by have hh := dyadic_annular_scale_lower hM j;omega) (q₀ j) Q (B j) (χ j) (fun _ => 0) (β j)) f x‖) ∧
        ‖g‖ ≤ H*Q^(-δ)*‖f‖ := by
  obtain ⟨H,hH,hh⟩ := ordinaryCollar_uniform_maximum hδ0 hδhalf
  refine ⟨H,hH,?_⟩
  intro M hM Q hQ R hQR q₀ hq₀ B hB χ β f
  have hΓ : ∀ r ∈ canonicalRationalCenters ⌊Q⌋₊,r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ ⌊Q⌋₊ :=
    fun r hr => (mem_canonicalRationalCenters _ r).mp hr
  obtain ⟨g,hg,hn⟩ := hh M hM Q hQ _ hΓ (fun _ _ => 1) (by intros;norm_num) (by intros;norm_num)
    (fun _ _ => 1) (by intros;norm_num) f
  refine ⟨g,?_,hn⟩
  intro x
  rw [hg x]
  apply iSup_congr
  intro j
  rw [ordinaryHigh_filtered_source _ _ (q₀ j) (hq₀ j) (by linarith : 0 < Q) (hQR j) (hB j) (χ j) (β j)]
  simp only [one_mul]

end PrimeSquares
