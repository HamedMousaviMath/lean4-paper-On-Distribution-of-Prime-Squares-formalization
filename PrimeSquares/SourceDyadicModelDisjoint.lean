import PrimeSquares.SourceDyadicDenominatorBounds
import PrimeSquares.CircleRationalModelDisjoint
namespace PrimeSquares
theorem sourceDyadic_model_disjoint {s : ℕ} (hs : 2 ≤ s) {r t : ℚ}
    (hr : r ∈ sourceDyadicRationalCenters s) (ht : t ∈ sourceDyadicRationalCenters s) (hrt : r ≠ t)
    (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (χ ψ : ∀ a : ℚ,DirichletCharacter ℂ a.den) (κ μ : ℚ → ℂ) (β γ : ℝ)
    (θ : PrimeCircle) :
    circleRationalModelTerm N hN χ κ β r θ=0 ∨ circleRationalModelTerm M hM ψ μ γ t θ=0 :=
  circleRationalModel_disjoint hs ((mem_sourceDyadicRationalCenters s r).mp hr).1
    ((mem_sourceDyadicRationalCenters s t).mp ht).1 hrt
    (sourceDyadicRationalCenters_den_bounds hr).2.le (sourceDyadicRationalCenters_den_bounds ht).2.le
    ((mem_sourceDyadicRationalCenters s r).mp hr).2 ((mem_sourceDyadicRationalCenters s t).mp ht).2
    N M hN hM χ ψ κ μ β γ θ
end PrimeSquares
