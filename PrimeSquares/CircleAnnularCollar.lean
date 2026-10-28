import PrimeSquares.CollarBroadEnergy
import PrimeSquares.IntegerWindowSupport
import PrimeSquares.CircleFundamentalBounds

namespace PrimeSquares

noncomputable def circleAnnularCollar (N : ℕ) (hN : 1 ≤ N) (β q Q : ℝ) (s : ℕ) (center : ℝ) : C(PrimeCircle,ℂ) :=
  (compactCircleLift (annularCollarSymbol N hN β q Q s) (annularCollarSymbol_support N hN β q Q s)).comp
    ⟨fun θ => θ-(center : PrimeCircle),continuous_id.sub continuous_const⟩

theorem circleAnnularCollar_real (N : ℕ) (hN : 1 ≤ N) (β q Q : ℝ) (s : ℕ) (center ξ : ℝ) :
    circleAnnularCollar N hN β q Q s center (ξ : PrimeCircle)=
      ∑' k : ℤ,annularCollarSymbol N hN β q Q s (ξ-center+k) := by
  change compactCircleLift (annularCollarSymbol N hN β q Q s) (annularCollarSymbol_support N hN β q Q s)
    ((ξ : PrimeCircle)-(center : PrimeCircle))=_
  rw [←AddCircle.coe_sub]
  exact compactCircleLift_all_real _ _ _

end PrimeSquares
