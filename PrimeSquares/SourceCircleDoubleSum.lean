import PrimeSquares.SourceExceptionalUnitData
import PrimeSquares.FiniteCircleHighLow

open Finset
namespace PrimeSquares

theorem circleLowModel_denominator_sum (M N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    circleLowModel (canonicalRationalCenters M) N hN q₀ Q B₀ χ κ β=
      ∑ q ∈ Icc 1 M,denominatorUnitSum q (fun r => circleLowTerm N hN q₀ Q B₀ χ κ β r) := by
  exact canonicalCenters_sum_units M _

theorem sourceRationalCenters_sum_units {A : Type*} [AddCommMonoid A]
    (R : ℝ) (F : ℚ → A) :
    (∑ r ∈ sourceRationalCenters R,F r)=∑ q ∈ Icc 1 ⌊R⌋₊,denominatorUnitSum q F :=
  canonicalCenters_sum_units ⌊R⌋₊ F

end PrimeSquares
