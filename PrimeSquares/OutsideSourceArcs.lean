import PrimeSquares.CanonicalApproximationLift
import PrimeSquares.BalancedEffectiveDenominator
import PrimeSquares.PeriodizedModelTails

namespace PrimeSquares

def OutsideSourceMajorArcs (N : ℕ) (R ξ : ℝ) : Prop :=
  ∀ r ∈ sourceRationalCenters R, ∀ k : ℤ,
    R/((r.den : ℝ)*(N : ℝ)^2) ≤ |ξ+(k : ℝ)-(r : ℝ)|

theorem outsideSourceMajorArcs_rational {N : ℕ} {R ξ : ℝ} (hR : 0 ≤ R)
    (hout : OutsideSourceMajorArcs N R ξ) (r : ℚ) (hd : (r.den : ℝ) ≤ R) :
    R/((r.den : ℝ)*(N : ℝ)^2) ≤ |ξ-(r : ℝ)| := by
  have h := hout (Int.fract r) (ratFract_mem_sourceRationalCenters hR r hd) (-⌊r⌋)
  rw [Rat.den_intFract,←rational_offset_canonical_lift] at h
  exact h

theorem outsideSourceMajorArcs_effective_lower {N : ℕ} (hN : 1 ≤ N)
    {R ξ : ℝ} (hR : 0 < R) (hout : OutsideSourceMajorArcs N R ξ) (r : ℚ) :
    R/4 ≤ renEffectiveDenominator r.den ((N : ℝ)/2) (ξ-(r : ℝ)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  apply renEffectiveDenominator_lower_from_arc (by positivity) hR.le r.den r.den_pos
  by_cases hd : (r.den : ℝ) ≤ R
  · right
    have h := outsideSourceMajorArcs_rational hR.le hout r hd
    convert h using 2; ring
  · exact Or.inl (le_of_not_ge hd)

theorem outsideSourceMajorArcs_circleModel_norm {N : ℕ} (hN : 2 ≤ N)
    {R ξ β : ℝ} (hR : 1 ≤ R)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hκ : ∀ r ∈ sourceRationalCenters R, ‖κ r‖ ≤ 1)
    (hξ : ξ ∈ Set.Icc (-1 : ℝ) 2) (hout : OutsideSourceMajorArcs N R ξ) :
    ‖circleMajorArcModel (sourceRationalCenters R) N (by omega) χ κ β (ξ : PrimeCircle)‖ ≤
      circleModelTailBudget R := by
  have hindex := fun r hr => (mem_sourceRationalCenters (by linarith : 0 ≤ R) r).mp hr
  exact circleMajorArcModel_outside_norm hN _ χ κ hβ0 hβ1 hR
    (fun r hr => (hindex r hr).1) (fun r hr => (hindex r hr).2) hκ hξ
    (fun r hr k _ => hout r hr k)

end PrimeSquares
