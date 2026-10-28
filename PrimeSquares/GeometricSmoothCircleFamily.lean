import PrimeSquares.CircleSmoothNorm
open Finset
namespace PrimeSquares
noncomputable def smoothCircleScale (a : ℝ) (j : ℕ) : ℝ := a*4^j
theorem smoothCircleScale_ge {a : ℝ} (ha : 0 ≤ a) (j : ℕ) : a ≤ smoothCircleScale a j := by
  have h : (1 : ℝ) ≤ 4^j := one_le_pow₀ (by norm_num)
  unfold smoothCircleScale
  nlinarith
theorem smoothCircleScale_four {a : ℝ} (ha : 4 ≤ a) (j : ℕ) : 4 ≤ smoothCircleScale a j :=
  ha.trans (smoothCircleScale_ge (by linarith) j)
theorem smoothCircleScale_one {a : ℝ} (ha : 4 ≤ a) (j : ℕ) : 1 ≤ smoothCircleScale a j :=
  le_trans (by norm_num) (smoothCircleScale_four ha j)
noncomputable def unweightedSmoothCircleFamily (Γ : Finset ℚ) (a : ℝ) (ha : 4 ≤ a)
    (j : ℕ) : C(PrimeCircle,ℂ) :=
  ∑ r ∈ Γ,circleSmoothCutoff (smoothCircleScale a j) (smoothCircleScale_one ha j) r
end PrimeSquares
