import PrimeSquares.CircleRationalModelDisjoint
import PrimeSquares.DisjointIntegerMultipliers
open scoped lp
namespace PrimeSquares
theorem circleRationalModel_orthogonal {s : ℕ} (hs : 2 ≤ s) {r t : ℚ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (ht : t ∈ Set.Ico (0 : ℚ) 1) (hne : r ≠ t)
    (hrD : (r.den : ℝ) ≤ (2 : ℝ)^(s+1)) (htD : (t.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (hrs : Nat.log2 r.den=s) (hts : Nat.log2 t.den=s)
    (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (χ ψ : ∀ a : ℚ, DirichletCharacter ℂ a.den) (κ μ : ℚ → ℂ) (β γ : ℝ)
    (f g : ℓ²(ℤ,ℂ)) :
    inner ℂ (integerMultiplier (circleRationalModelTerm N hN χ κ β r) f)
      (integerMultiplier (circleRationalModelTerm M hM ψ μ γ t) g)=0 :=
  integerMultiplier_disjoint_inner _ _
    (circleRationalModel_disjoint hs hr ht hne hrD htD hrs hts N M hN hM χ ψ κ μ β γ) f g
end PrimeSquares
