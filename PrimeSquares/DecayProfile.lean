import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

namespace PrimeSquares

noncomputable def decayProfile (H : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ((1+|x|/H)^K)⁻¹

theorem decayProfile_pos {H : ℝ} (hH : 0 < H) (K : ℕ) (x : ℝ) :
    0 < decayProfile H K x := by
  unfold decayProfile
  positivity

theorem decayProfile_le_one {H : ℝ} (hH : 0 < H) (K : ℕ) (x : ℝ) :
    decayProfile H K x ≤ 1 := by
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by have h := div_nonneg (abs_nonneg x) hH.le; linarith : 1 ≤ 1+|x|/H)

theorem decayProfile_even (H : ℝ) (K : ℕ) (x : ℝ) :
    decayProfile H K (-x) = decayProfile H K x := by simp [decayProfile]

theorem decayProfile_mono_abs {H x y : ℝ} (hH : 0 < H) (K : ℕ)
    (hxy : |x| ≤ |y|) : decayProfile H K y ≤ decayProfile H K x := by
  unfold decayProfile
  exact inv_anti₀ (by positivity)
    (pow_le_pow_left₀ (by positivity) (by gcongr) K)

end PrimeSquares
