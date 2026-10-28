import PrimeSquares.CircleModelOperators

namespace PrimeSquares

theorem primeCircle_representative (θ : PrimeCircle) :
    ∃ ξ ∈ Set.Ico (0 : ℝ) 1, (ξ : PrimeCircle) = θ := by
  exact AddCircle.eq_coe_Ico θ

theorem circleBound_from_fundamental_interval (F : C(PrimeCircle, ℂ)) {B : ℝ}
    (hF : ∀ ξ ∈ Set.Icc (0 : ℝ) 1, ‖F (ξ : PrimeCircle)‖ ≤ B) :
    ∀ θ : PrimeCircle, ‖F θ‖ ≤ B := by
  intro θ
  obtain ⟨ξ,hξ,rfl⟩ := primeCircle_representative θ
  exact hF ξ ⟨hξ.1,hξ.2.le⟩

theorem integerMultiplier_bound_fundamental_interval (F : C(PrimeCircle, ℂ)) {B : ℝ}
    (hB : 0 ≤ B) (hF : ∀ ξ ∈ Set.Icc (0 : ℝ) 1, ‖F (ξ : PrimeCircle)‖ ≤ B) :
    ‖integerMultiplier F‖ ≤ B :=
  integerMultiplier_opNorm_le_of_bound F hB (circleBound_from_fundamental_interval F hF)

end PrimeSquares
