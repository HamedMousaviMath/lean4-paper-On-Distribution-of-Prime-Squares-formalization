import PrimeSquares.CharacterMultiplierUnitMass
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem unitMass_majorant_square_lower (g : lp (fun _ : ℤ => ℝ) 2)
    (hg : ∀ j : ℕ,1 ≤ g (j : ℤ)) (N : ℕ) : (N : ℝ) ≤ ‖g‖^2 := by
  classical
  let S : Finset ℤ := (range N).image (fun j : ℕ => (j : ℤ))
  have hinj : Function.Injective (fun j : ℕ => (j : ℤ)) := by
    intro a b hab
    dsimp only at hab
    omega
  have hcard : S.card=N := by
    simp only [S,card_image_of_injective (range N) hinj,card_range]
  have h1 : (S.card : ℝ) ≤ ∑ x ∈ S,‖g x‖^2 := by
    calc
      _ = ∑ x ∈ S,(1 : ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro x hx
        obtain ⟨j,_,rfl⟩ := mem_image.mp hx
        have hh := hg j
        rw [Real.norm_eq_abs,sq_abs]
        nlinarith
  have h2 : (∑ x ∈ S,‖g x‖^2) ≤ ‖g‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.sum_rpow_le_norm_rpow (by norm_num : (0 : ℝ)<(2 : ENNReal).toReal) g S
  rw [hcard] at h1
  exact h1.trans h2
end PrimeSquares
