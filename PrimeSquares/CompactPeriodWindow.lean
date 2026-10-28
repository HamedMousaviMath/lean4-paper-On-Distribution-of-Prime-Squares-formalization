import PrimeSquares.CircleFourier
import Mathlib.Tactic.Linarith

namespace PrimeSquares

noncomputable def compactPeriodWindow (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  f (x-1) + f x + f (x+1)

theorem compactPeriodWindow_continuous {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (compactPeriodWindow f) := by
  exact ((hf.comp (continuous_id.sub continuous_const)).add hf).add
    (hf.comp (continuous_id.add continuous_const))

/-- The endpoint equality is what makes the quotient construction continuous. -/
theorem compactPeriodWindow_endpoints (f : ℝ → ℂ)
    (hs : ∀ x, 1 ≤ |x| → f x = 0) :
    compactPeriodWindow f (-(1/2)) = compactPeriodWindow f (1/2) := by
  have hl := hs (-(3/2)) (by norm_num)
  have hr := hs (3/2) (by norm_num)
  norm_num [compactPeriodWindow] at *
  rw [hl, hr]
  ring

theorem compactPeriodWindow_bound (f : ℝ → ℂ) {B : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ B) (x : ℝ) : ‖compactPeriodWindow f x‖ ≤ 3*B := by
  have h1 := norm_add_le (f (x-1)+f x) (f (x+1))
  have h2 := norm_add_le (f (x-1)) (f x)
  have ha := hf (x-1)
  have hb := hf x
  have hc := hf (x+1)
  dsimp [compactPeriodWindow]
  linarith

end PrimeSquares
