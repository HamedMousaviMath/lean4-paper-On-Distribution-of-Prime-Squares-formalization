import PrimeSquares.IWGoodness
import PrimeSquares.RawPageUniqueness
import Mathlib.Data.Rat.Lemmas

set_option autoImplicit false
namespace PrimeSquares

theorem iw_period_divisible_small {C ρ : ℝ} {k Q q : ℕ}
    (d : TaoArcConstructionData C ρ k Q) (hq : 2≤q) (hqQ : q≤Q) : q∣d.period := by
  have hqp : (0 : ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have hden : (q : ℚ)⁻¹.den=q := Rat.inv_natCast_den_of_pos (by omega)
  have hmem : (q : ℚ)⁻¹∈canonicalRationalCenters Q := by
    apply (mem_canonicalRationalCenters _ _).mpr
    refine ⟨⟨(inv_pos.mpr hqp).le,?_⟩,by simpa only [hden] using hqQ⟩
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (show 1<q by omega))
  simpa only [hden] using d.periodic _ (d.covered hmem)

theorem page_zero_in_fixed_region {c Q R : ℝ} (hc : 0<c) (hQ : 2≤Q) (hQR : Q≤R)
    (F : PageZeroDatum) (hβ : 1-(c/2)/Real.log R<F.beta) :
    1-c/Real.log Q<F.beta := by
  have hlogQ : 0<Real.log Q := Real.log_pos (by linarith)
  have hlog : Real.log Q≤Real.log R := Real.log_le_log (by linarith) hQR
  have hdiv : (c/2)/Real.log R≤c/Real.log Q := by
    calc
      _ ≤ (c/2)/Real.log Q := div_le_div_of_nonneg_left (by positivity) hlogQ hlog
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hlogQ.le
  exact lt_of_le_of_lt (by linarith) hβ

/-- The fixed exceptional datum is extracted from genuine Page data, rather
than imposed as a source-specific selection hypothesis. It may be inactive at
arbitrarily many scales; activity remains the original optional datum. -/
theorem fixed_small_page_datum {c Q : ℝ} (hc : 0<c) (HP : RawPageUniquenessInput c)
    (hQ : 2≤Q) (E : ℕ → Option PageZeroDatum) (R : ℕ → ℝ) (hR : ∀ j,Q≤R j)
    (hβ : ∀ j F,E j=some F → 1-(c/2)/Real.log (R j)<F.beta) :
    ∃ E₀ : Option PageZeroDatum,
      (∀ F,E₀=some F → (F.conductor : ℝ)≤Q ∧ ∃ j,E j=some F) ∧
      (∀ j F,E j=some F → (F.conductor : ℝ)≤Q → E₀=some F) := by
  classical
  by_cases he : ∃ j F,E j=some F ∧ (F.conductor : ℝ)≤Q
  · obtain ⟨j₀,F₀,hE₀,hF₀⟩ := he
    refine ⟨some F₀,?_,?_⟩
    · intro F hF
      have hf : F₀=F := Option.some.inj hF
      subst F
      exact ⟨hF₀,j₀,hE₀⟩
    · intro j F hE hF
      have hFF : F₀=F := HP Q hQ F₀ F hF₀ hF
        (page_zero_in_fixed_region hc hQ (hR j₀) F₀ (hβ j₀ F₀ hE₀))
        (page_zero_in_fixed_region hc hQ (hR j) F (hβ j F hE))
      rw [hFF]
  · refine ⟨none,?_,?_⟩
    · intro F hF
      cases hF
    · intro j F hE hF
      exact (he ⟨j,F,hE,hF⟩).elim

theorem fixed_small_page_conductor_period {C ρ : ℝ} {k Q : ℕ}
    (d : TaoArcConstructionData C ρ k Q) (F : PageZeroDatum) (hF : (F.conductor : ℝ)≤Q) :
    F.conductor∣d.period :=
  iw_period_divisible_small d F.conductor_two (by exact_mod_cast hF)

end PrimeSquares
