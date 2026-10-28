import PrimeSquares.CircleRationalModelOrthogonality
import PrimeSquares.FiniteOrthogonalEnergy
open Finset
open scoped lp
namespace PrimeSquares
theorem circleRationalModel_finite_energy {s : ℕ} (hs : 2 ≤ s) (S : Finset ℚ)
    (hc : ∀ r ∈ S,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ S,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (hl : ∀ r ∈ S,Nat.log2 r.den=s)
    (N : ℕ) (hN : 1 ≤ N) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (κ : ℚ → ℂ) (β : ℝ) (F : ℚ → ℓ²(ℤ,ℂ)) :
    ‖∑ r ∈ S,integerMultiplier (circleRationalModelTerm N hN χ κ β r) (F r)‖^2=
      ∑ r ∈ S,‖integerMultiplier (circleRationalModelTerm N hN χ κ β r) (F r)‖^2 := by
  exact finite_orthogonal_energy S _ (fun r hr t ht hrt =>
    circleRationalModel_orthogonal hs (hc r hr) (hc t ht) hrt (hd r hr) (hd t ht)
      (hl r hr) (hl t ht) N N hN hN χ χ κ κ β β (F r) (F t))
end PrimeSquares
