import PrimeSquares.NoL2UnitMassMajorant
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem uniformMultiplier_norm_not_maximal :
    (∀ j : ℕ,‖integerMultiplier (negativeFourierCharacter (j : ℤ))‖ ≤ 1) ∧
    ¬ ∃ g : lp (fun _ : ℤ => ℝ) 2,∀ (j : ℕ) (x : ℤ),
      ‖integerMultiplier (negativeFourierCharacter (j : ℤ))
        (lp.single 2 (0 : ℤ) (1 : ℂ)) x‖ ≤ g x := by
  constructor
  · intro j
    simpa only [negativeFourierCharacter_sup_norm] using
      integerMultiplier_opNorm_le (negativeFourierCharacter (j : ℤ))
  · rintro ⟨g,hg⟩
    apply no_l2_unit_mass_majorant
    refine ⟨g,?_⟩
    intro j
    have hh := hg j (j : ℤ)
    rw [characterMultiplier_unit_mass,lp.single_apply_self,norm_one] at hh
    exact hh
end PrimeSquares
