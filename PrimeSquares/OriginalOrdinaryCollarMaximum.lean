import PrimeSquares.OrdinaryHighCollarSum

open scoped lp
namespace PrimeSquares

theorem originalOrdinaryCollar_countable_maximum {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ < 1/2) :
    ∃ H : ℝ,0 < H ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),1 ≤ Q →
    ∀ (q₀ : ℕ),0 < q₀ → ∀ B : ℝ,0 < B →
    ∀ (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) (f : ℓ²(ℤ,ℂ)),
      ∃ g : lp (fun _ : ℤ => ℝ) 2,
        (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (circleHighModel (canonicalRationalCenters ⌊Q⌋₊) ((2 : ℕ)^j*M)
          (by have hh := dyadic_annular_scale_lower hM j;omega) q₀ Q B χ (fun _ => 0) β) f x‖) ∧
        ‖g‖ ≤ H*Q^(-δ)*‖f‖ := by
  obtain ⟨H,hH,hh⟩ := ordinaryCollar_uniform_maximum hδ0 hδhalf
  refine ⟨H,hH,?_⟩
  intro M hM Q hQ q₀ hq₀ B hB χ β f
  have hΓ : ∀ r ∈ canonicalRationalCenters ⌊Q⌋₊,r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ ⌊Q⌋₊ :=
    fun r hr => (mem_canonicalRationalCenters _ r).mp hr
  obtain ⟨g,hg,hgn⟩ := hh M hM Q hQ _ hΓ (fun _ _ => 1) (by intros;norm_num) (by intros;norm_num)
    (fun _ _ => 1) (by intros;norm_num) f
  refine ⟨g,?_,hgn⟩
  intro x
  rw [hg x]
  apply iSup_congr
  intro j
  rw [circleHighModel_ordinary_collar _ _ _ q₀ hq₀ (by linarith : 0 < Q) hB χ β
    (fun r hr => (by exact_mod_cast (hΓ r hr).2 : (r.den : ℝ) ≤ ⌊Q⌋₊).trans (Nat.floor_le (by linarith)))]
  simp only [one_mul]

end PrimeSquares
