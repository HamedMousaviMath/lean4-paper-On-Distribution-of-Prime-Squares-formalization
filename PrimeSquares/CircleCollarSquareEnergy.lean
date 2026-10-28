import PrimeSquares.ThreeTermSquareBound
import PrimeSquares.CircleSquareMaximal

open Finset
namespace PrimeSquares

theorem circleAnnularCollar_finite_energy {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) {q Q : ℝ} (hq : 0 < q) (hQ : 0 < Q)
    (s : ℕ) (center : ℝ) (J : Finset ℕ) (θ : PrimeCircle) :
    (∑ j ∈ J,‖circleAnnularCollar ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega) (β j) q Q s center θ‖^2) ≤
      (24*q/(Real.pi*Q))^2 := by
  obtain ⟨ξ,hξ,he⟩ := primeCircle_representative (θ-(center : PrimeCircle))
  have hw (j : ℕ) := circleAnnularCollar_representative ((2 : ℕ)^j*M)
    (by have hh := dyadic_annular_scale_lower hM j;omega) (β j) q Q s center θ ξ hξ he
  have h1 := annularCollarSymbol_finite_energy hM β hβ0 hβ1 hq hQ s J (ξ-1)
  have h2 := annularCollarSymbol_finite_energy hM β hβ0 hβ1 hq hQ s J ξ
  have h3 := annularCollarSymbol_finite_energy hM β hβ0 hβ1 hq hQ s J (ξ+1)
  calc
    _ = ∑ j ∈ J,‖compactPeriodWindow (annularCollarSymbol ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega) (β j) q Q s) ξ‖^2 := by
      apply sum_congr rfl
      intro j _
      rw [hw j]
    _ ≤ ∑ j ∈ J,3*(‖annularCollarSymbol ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega) (β j) q Q s (ξ-1)‖^2+
        ‖annularCollarSymbol ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega) (β j) q Q s ξ‖^2+
        ‖annularCollarSymbol ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega) (β j) q Q s (ξ+1)‖^2) :=
      sum_le_sum (fun j _ => compactPeriodWindow_square _ ξ)
    _ ≤ (24*q/(Real.pi*Q))^2 := by
      rw [←mul_sum,sum_add_distrib,sum_add_distrib]
      have heq : (24*q/(Real.pi*Q))^2=9*(8*q/(Real.pi*Q))^2 := by ring
      rw [heq]
      linarith

end PrimeSquares
