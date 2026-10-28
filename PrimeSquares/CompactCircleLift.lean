import PrimeSquares.CompactPeriodWindow

namespace PrimeSquares

noncomputable def compactCircleLift (f : C(ℝ, ℂ))
    (hs : ∀ x, 1 ≤ |x| → f x = 0) : C(PrimeCircle, ℂ) :=
  ⟨AddCircle.liftIco 1 (-(1/2)) (compactPeriodWindow f),
    AddCircle.liftIco_continuous (by
      norm_num
      exact compactPeriodWindow_endpoints f hs)
      (compactPeriodWindow_continuous f.continuous).continuousOn⟩

theorem compactCircleLift_real (f : C(ℝ, ℂ))
    (hs : ∀ x, 1 ≤ |x| → f x = 0) {x : ℝ}
    (hx : x ∈ Set.Ico (-(1/2) : ℝ) (1/2)) :
    compactCircleLift f hs (x : PrimeCircle) = compactPeriodWindow f x := by
  change AddCircle.liftIco 1 (-(1/2) : ℝ) (compactPeriodWindow f) (x : PrimeCircle) = _
  apply AddCircle.liftIco_coe_apply
  convert hx using 1
  norm_num

theorem compactCircleLift_norm_bound (f : C(ℝ, ℂ))
    (hs : ∀ x, 1 ≤ |x| → f x = 0) {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B)
    (θ : PrimeCircle) : ‖compactCircleLift f hs θ‖ ≤ 3*B := by
  change ‖compactPeriodWindow f _‖ ≤ 3*B
  exact compactPeriodWindow_bound f hf _

end PrimeSquares
