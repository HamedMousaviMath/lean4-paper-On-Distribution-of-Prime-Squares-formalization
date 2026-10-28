import PrimeSquares.CompactPeriodSum

namespace PrimeSquares

theorem compactCircleLift_eq_periodization (f : C(ℝ, ℂ))
    (hs : ∀ x, 1 ≤ |x| → f x = 0) :
    (compactCircleLift f hs : PrimeCircle → ℂ) = (integerPeriodSum_periodic f).lift := by
  funext θ
  let x := (AddCircle.equivIco 1 (-(1/2) : ℝ) θ : ℝ)
  have hx : x ∈ Set.Ico (-(1/2) : ℝ) (1/2) := by
    have h := (AddCircle.equivIco 1 (-(1/2) : ℝ) θ).property
    convert h using 1
    norm_num
  have he : (x : PrimeCircle) = θ := AddCircle.coe_equivIco
  rw [← he, compactCircleLift_real f hs hx, Function.Periodic.lift_coe]
  exact (integerPeriodSum_window f hs ⟨hx.1,hx.2.le⟩).symm

theorem compactCircleLift_all_real (f : C(ℝ, ℂ))
    (hs : ∀ x, 1 ≤ |x| → f x = 0) (x : ℝ) :
    compactCircleLift f hs (x : PrimeCircle) = ∑' k : ℤ, f (x+k) := by
  rw [compactCircleLift_eq_periodization, Function.Periodic.lift_coe]
  rfl

end PrimeSquares
