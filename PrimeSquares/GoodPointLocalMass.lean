import PrimeSquares.IntegerIntervalGeometry
import PrimeSquares.SourceLocalMass

/-!
# A good nearby point controls the literal real-radius local average

The estimate covers every real M>=N. No finite or dyadic supremum is used
in place of the local quantity in Proposition 4.19.
-/

open Finset
open scoped lp
namespace PrimeSquares

def integerCenteredBall (x : ℤ) (r : ℕ) : SparseIntegerInterval where
  left := x-r
  length := 2*r+1
  length_pos := by omega

theorem integerCenteredBall_mem (x y : ℤ) (r : ℕ) :
    y ∈ (integerCenteredBall x r).points ↔ |x-y| ≤ (r : ℤ) := by
  simp only [integerInterval_mem_points, integerCenteredBall, Nat.cast_add, Nat.cast_mul,
    Nat.cast_one, Nat.cast_ofNat, abs_le]
  omega

theorem integerCenteredBall_subset_five (R : SparseIntegerInterval) {x : ℤ}
    (hx : x ∈ R.points) {r : ℕ} (hr : r ≤ R.length) :
    (integerCenteredBall x r).points ⊆ R.five.points := by
  intro y hy
  rw [integerCenteredBall_mem, abs_le] at hy
  rw [integerInterval_mem_points] at hx ⊢
  simp only [SparseIntegerInterval.five, Nat.cast_mul, Nat.cast_ofNat]
  constructor <;> omega

theorem sourceBallMass_finiteIndicator (F : Finset ℤ) (x : ℤ) (M : ℝ) :
    sourceBallMass (finiteIndicatorLp F 1) x M =
      (M^2)⁻¹ * ((F.filter (fun y => |((x-y : ℤ) : ℝ)| ≤ M^2)).card : ℝ) := by
  unfold sourceBallMass
  rw [tsum_eq_sum (s := F) (fun y hy => by
    simp [finiteIndicatorLp, finiteIndicator, hy])]
  congr 1
  rw [← sum_boole]
  apply sum_congr rfl
  intro y hy
  simp [finiteIndicatorLp, finiteIndicator, hy]

theorem sourceBallMass_le_interval_count (F : Finset ℤ) (x : ℤ) (M : ℝ)
    (J : SparseIntegerInterval)
    (hJ : ∀ y ∈ F, |((x-y : ℤ) : ℝ)| ≤ M^2 → y ∈ J.points) :
    sourceBallMass (finiteIndicatorLp F 1) x M ≤
      (M^2)⁻¹ * ((F ∩ J.points).card : ℝ) := by
  rw [sourceBallMass_finiteIndicator]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast (card_le_card (show F.filter (fun y => |((x-y : ℤ) : ℝ)| ≤ M^2) ⊆
      F ∩ J.points by
    intro y hy
    have hh := mem_filter.mp hy
    exact mem_inter.mpr ⟨hh.1, hJ y hh.1 hh.2⟩))

theorem goodPoint_sourceLocalMass (R : SparseIntegerInterval) (F : Finset ℤ) {t : ℝ}
    (ht : (F.card : ℝ) / R.length ≤ t) {N : ℕ} (hN : 1 ≤ N) {x z : ℤ}
    (hx : x ∈ R.points) (hclose : |((x-z : ℤ) : ℝ)| ≤ (N : ℝ)^2)
    (hgood : ∀ J : SparseIntegerInterval, J.points ⊆ R.five.points → z ∈ J.points →
      ((F ∩ J.points).card : ℝ) ≤ t * (J.length : ℝ)) :
    sourceLocalMass N (finiteIndicatorLp F 1) x ≤ 5*t := by
  have hR : (0 : ℝ) < R.length := by exact_mod_cast R.length_pos
  have ht0 : 0 ≤ t := (div_nonneg (Nat.cast_nonneg _) hR.le).trans ht
  apply ciSup_le
  intro M
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hM : (1 : ℝ) ≤ M.val := hNr.trans M.property
  have hs : (N : ℝ)^2 ≤ M.val^2 := (sq_le_sq₀ (by linarith) (by linarith)).mpr M.property
  have hMs : 1 ≤ M.val^2 := by nlinarith
  have hMpos : 0 < M.val^2 := by linarith
  by_cases hlarge : (R.length : ℝ) ≤ M.val^2
  · have hcount : sourceBallMass (finiteIndicatorLp F 1) x M.val ≤
        (M.val^2)⁻¹ * (F.card : ℝ) := by
      rw [sourceBallMass_finiteIndicator]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card (filter_subset _ _)) (by positivity)
    have hi := inv_anti₀ hR hlarge
    calc
      _ ≤ (M.val^2)⁻¹ * (F.card : ℝ) := hcount
      _ ≤ (R.length : ℝ)⁻¹ * (F.card : ℝ) :=
        mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg _)
      _ = (F.card : ℝ) / R.length := by ring
      _ ≤ t := ht
      _ ≤ 5*t := by linarith
  · let r := Nat.ceil (M.val^2)
    have hr : M.val^2 ≤ (r : ℝ) := Nat.le_ceil _
    have hrR : r ≤ R.length := Nat.ceil_le.mpr (le_of_not_ge hlarge)
    let J := integerCenteredBall x r
    have hJsub : J.points ⊆ R.five.points := integerCenteredBall_subset_five R hx hrR
    have hzJ : z ∈ J.points := by
      rw [integerCenteredBall_mem]
      exact_mod_cast (hclose.trans hs).trans hr
    have hcount := sourceBallMass_le_interval_count F x M.val J (fun y _ hy => by
      rw [integerCenteredBall_mem]
      exact_mod_cast hy.trans hr)
    have hsize : (J.length : ℝ) ≤ 5*M.val^2 := by
      have hrup : (r : ℝ) < M.val^2+1 := Nat.ceil_lt_add_one (sq_nonneg _)
      change ((2*r+1 : ℕ) : ℝ) ≤ _
      push_cast
      nlinarith
    have hd : ((F ∩ J.points).card : ℝ) ≤ 5*t*M.val^2 :=
      (hgood J hJsub hzJ).trans (by nlinarith [mul_le_mul_of_nonneg_left hsize ht0])
    calc
      _ ≤ (M.val^2)⁻¹ * ((F ∩ J.points).card : ℝ) := hcount
      _ ≤ (M.val^2)⁻¹ * (5*t*M.val^2) := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by field_simp

end PrimeSquares
