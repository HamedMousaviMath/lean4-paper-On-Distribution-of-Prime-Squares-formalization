import PrimeSquares.CircleAnnularCollar

namespace PrimeSquares

theorem circleAnnularCollar_window (N : ℕ) (hN : 1 ≤ N) (β q Q : ℝ) (s : ℕ) (center ξ : ℝ)
    (hξ : ξ-center ∈ Set.Icc (-1 : ℝ) 1) :
    circleAnnularCollar N hN β q Q s center (ξ : PrimeCircle)=
      compactPeriodWindow (annularCollarSymbol N hN β q Q s) (ξ-center) := by
  rw [circleAnnularCollar_real]
  exact integerPeriodSum_unit_window _ (annularCollarSymbol_support N hN β q Q s) hξ

theorem circleAnnularCollar_representative (N : ℕ) (hN : 1 ≤ N) (β q Q : ℝ) (s : ℕ) (center : ℝ)
    (θ : PrimeCircle) (ξ : ℝ) (hξ : ξ ∈ Set.Ico (0 : ℝ) 1)
    (he : (ξ : PrimeCircle)=θ-(center : PrimeCircle)) :
    circleAnnularCollar N hN β q Q s center θ=compactPeriodWindow (annularCollarSymbol N hN β q Q s) ξ := by
  change compactCircleLift (annularCollarSymbol N hN β q Q s) (annularCollarSymbol_support N hN β q Q s)
    (θ-(center : PrimeCircle))=_
  rw [←he,compactCircleLift_all_real]
  exact integerPeriodSum_unit_window _ (annularCollarSymbol_support N hN β q Q s) ⟨by linarith [hξ.1],hξ.2.le⟩

end PrimeSquares
