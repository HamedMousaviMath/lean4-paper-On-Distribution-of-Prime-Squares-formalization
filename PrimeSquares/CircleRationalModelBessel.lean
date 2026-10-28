import PrimeSquares.CircleRationalModelDisjoint
import PrimeSquares.FiniteDisjointMultiplierBessel
open Finset
open scoped lp
namespace PrimeSquares
theorem circleRationalModel_bessel {s : ℕ} (hs : 2 ≤ s) (S : Finset ℚ)
    (hc : ∀ r ∈ S,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ S,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (hl : ∀ r ∈ S,Nat.log2 r.den=s)
    (N : ℕ) (hN : 1 ≤ N) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (κ : ℚ → ℂ) (β : ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ r ∈ S,∀ θ,‖circleRationalModelTerm N hN χ κ β r θ‖ ≤ A) (f : ℓ²(ℤ,ℂ)) :
    (∑ r ∈ S,‖integerMultiplier (circleRationalModelTerm N hN χ κ β r) f‖^2) ≤ A^2*‖f‖^2 :=
  finite_disjoint_multiplier_bessel S _ (fun r hr t ht hrt =>
    circleRationalModel_disjoint hs (hc r hr) (hc t ht) hrt (hd r hr) (hd t ht)
      (hl r hr) (hl t ht) N N hN hN χ χ κ κ β β) hA hb f
end PrimeSquares
