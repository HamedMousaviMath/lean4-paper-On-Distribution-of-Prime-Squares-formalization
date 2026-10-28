import PrimeSquares.FiniteSchur
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform geometric weights for the strong interpolation argument

The actual minimum of the restricted and l2 block bounds is summable, with
an explicit bound independent of the positive scale X. Taking X=N^2 gives
the intended interpolation weight. No geometric bound is an external input.
-/

open Finset

namespace PrimeSquares

noncomputable def interpolationWeight (A B a b X : ℝ) (n : ℕ) : ℝ :=
  min (A * ((2 : ℝ)^n / X)^a) (B * ((2 : ℝ)^n / X)^(-b))

noncomputable def interpolationWeightConstant (A B a b : ℝ) : ℝ :=
  A / (1 - (2 : ℝ)^(-a)) + (2 : ℝ)^b * B / (1 - (2 : ℝ)^(-b))

theorem dyadic_pow_rpow (n : ℕ) (a : ℝ) :
    ((2 : ℝ)^n)^a = ((2 : ℝ)^a)^n := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
    mul_comm (n : ℝ) a, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]

theorem dyadic_decay_ratio {a : ℝ} (ha : 0 < a) :
    0 < (2 : ℝ)^(-a) ∧ (2 : ℝ)^(-a) < 1 :=
  ⟨Real.rpow_pos_of_pos (by norm_num) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ha)⟩

theorem interpolationWeight_nonneg {A B a b X : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hX : 0 < X) (n : ℕ) : 0 ≤ interpolationWeight A B a b X n := by
  unfold interpolationWeight
  exact le_min (by positivity) (by positivity)

theorem dyadic_negative_ratio_factor {X : ℝ} (hX : 0 < X) (b : ℝ) (n : ℕ) :
    ((2 : ℝ)^n / X)^(-b) = X^b * ((2 : ℝ)^(-b))^n := by
  rw [Real.div_rpow (by positivity) hX.le, dyadic_pow_rpow,
    Real.rpow_neg hX.le b, div_inv_eq_mul, mul_comm]

theorem interpolationWeight_summable {A B a b X : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : 0 < b) (hX : 0 < X) :
    Summable (interpolationWeight A B a b X) := by
  obtain ⟨hr0, hr1⟩ := dyadic_decay_ratio hb
  apply Summable.of_nonneg_of_le (interpolationWeight_nonneg hA hB hX)
    (f := fun n => (B * X^b) * ((2 : ℝ)^(-b))^n)
  · intro n
    calc
      _ ≤ B * ((2 : ℝ)^n / X)^(-b) := min_le_right _ _
      _ = _ := by rw [dyadic_negative_ratio_factor hX]; ring
  · exact (summable_geometric_of_lt_one hr0.le hr1).mul_left _

theorem finite_reversed_geometric_sum_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    (∑ n ∈ range k, r^(k-n)) ≤ (1-r)⁻¹ := by
  have he : (∑ n ∈ range k, r^(k-n)) = ∑ m ∈ (range k).image (fun n => k-n), r^m := by
    rw [sum_image]
    intro i hi j hj hij
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    change k-i = k-j at hij
    omega
  rw [he, ← tsum_geometric_of_lt_one hr0 hr1]
  exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun n _ => pow_nonneg hr0 n)

theorem dyadic_ratio_low_bound {X a : ℝ} (hX : 0 < X) (ha : 0 ≤ a)
    {k n : ℕ} (hn : n ≤ k) (hk : (2 : ℝ)^k ≤ X) :
    ((2 : ℝ)^n / X)^a ≤ ((2 : ℝ)^(-a))^(k-n) := by
  have hratio : (2 : ℝ)^n / X ≤ (2 : ℝ)^n / (2 : ℝ)^k :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hk
  calc
    _ ≤ ((2 : ℝ)^n / (2 : ℝ)^k)^a := Real.rpow_le_rpow (by positivity) hratio ha
    _ = ((2 : ℝ)^a)^n / ((2 : ℝ)^a)^k := by
      rw [Real.div_rpow (by positivity) (by positivity), dyadic_pow_rpow, dyadic_pow_rpow]
    _ = _ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_pow]
      have he : ((2 : ℝ)^a)^k = ((2 : ℝ)^a)^n * ((2 : ℝ)^a)^(k-n) := by
        rw [← pow_add, Nat.add_sub_of_le hn]
      rw [he]
      field_simp

theorem dyadic_ratio_high_bound {X b : ℝ} (hX : 0 < X) (hb : 0 ≤ b)
    {k : ℕ} (hk : X ≤ 2 * (2 : ℝ)^k) (n : ℕ) :
    ((2 : ℝ)^(n+k) / X)^(-b) ≤ (2 : ℝ)^b * ((2 : ℝ)^(-b))^n := by
  have hratio : (2 : ℝ)^(n+k) / (2 * (2 : ℝ)^k) ≤ (2 : ℝ)^(n+k) / X :=
    div_le_div_of_nonneg_left (by positivity) hX hk
  have he : (2 : ℝ)^(n+k) / (2 * (2 : ℝ)^k) = (2 : ℝ)^n / 2 := by
    rw [pow_add]
    field_simp
  calc
    _ ≤ ((2 : ℝ)^(n+k) / (2 * (2 : ℝ)^k))^(-b) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hratio (neg_nonpos.mpr hb)
    _ = _ := by
      rw [he, Real.div_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 2), dyadic_pow_rpow,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) b, div_inv_eq_mul, mul_comm]

theorem interpolationWeightConstant_nonneg {A B a b : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ interpolationWeightConstant A B a b := by
  obtain ⟨_, hra⟩ := dyadic_decay_ratio ha
  obtain ⟨_, hrb⟩ := dyadic_decay_ratio hb
  unfold interpolationWeightConstant
  exact add_nonneg (div_nonneg hA (sub_nonneg.mpr hra.le))
    (div_nonneg (mul_nonneg (by positivity) hB) (sub_nonneg.mpr hrb.le))

theorem interpolationWeight_tsum_le_at_pivot {A B a b X : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 < b) (hX : 0 < X)
    (k : ℕ) (hlow : k = 0 ∨ (2 : ℝ)^k ≤ X) (hhigh : X ≤ 2 * (2 : ℝ)^k) :
    (∑' n, interpolationWeight A B a b X n) ≤ interpolationWeightConstant A B a b := by
  obtain ⟨hra0, hra1⟩ := dyadic_decay_ratio ha
  obtain ⟨hrb0, hrb1⟩ := dyadic_decay_ratio hb
  have hsum := interpolationWeight_summable hA hB hb hX (a := a)
  have hhead : (∑ n ∈ range k, interpolationWeight A B a b X n) ≤
      A / (1 - (2 : ℝ)^(-a)) := by
    calc
      _ ≤ ∑ n ∈ range k, A * ((2 : ℝ)^(-a))^(k-n) := by
        apply sum_le_sum
        intro n hn
        rcases hlow with hz | hlo
        · subst k
          simp at hn
        · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left
            (dyadic_ratio_low_bound hX ha.le (le_of_lt (mem_range.mp hn)) hlo) hA)
      _ = A * ∑ n ∈ range k, ((2 : ℝ)^(-a))^(k-n) := (mul_sum _ _ _).symm
      _ ≤ A * (1 - (2 : ℝ)^(-a))⁻¹ := mul_le_mul_of_nonneg_left
        (finite_reversed_geometric_sum_le hra0.le hra1 k) hA
      _ = _ := (div_eq_mul_inv _ _).symm
  have htail_point (n : ℕ) : interpolationWeight A B a b X (n+k) ≤
      ((2 : ℝ)^b * B) * ((2 : ℝ)^(-b))^n := by
    calc
      _ ≤ B * ((2 : ℝ)^(n+k) / X)^(-b) := min_le_right _ _
      _ ≤ B * ((2 : ℝ)^b * ((2 : ℝ)^(-b))^n) :=
        mul_le_mul_of_nonneg_left (dyadic_ratio_high_bound hX hb.le hhigh n) hB
      _ = _ := by ring
  have htail : (∑' n, interpolationWeight A B a b X (n+k)) ≤
      (2 : ℝ)^b * B / (1 - (2 : ℝ)^(-b)) := by
    calc
      _ ≤ ∑' n : ℕ, ((2 : ℝ)^b * B) * ((2 : ℝ)^(-b))^n :=
        Summable.tsum_le_tsum htail_point ((summable_nat_add_iff k).mpr hsum)
          ((summable_geometric_of_lt_one hrb0.le hrb1).mul_left _)
      _ = _ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hrb0.le hrb1, div_eq_mul_inv]
  rw [← Summable.sum_add_tsum_nat_add k hsum]
  exact add_le_add hhead htail

/-- The scale is arbitrary and positive; the bound does not depend on it. -/
theorem interpolationWeight_tsum_le {A B a b X : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) :
    (∑' n, interpolationWeight A B a b X n) ≤ interpolationWeightConstant A B a b := by
  by_cases hX1 : 1 ≤ X
  · obtain ⟨k, hk, hkup⟩ := exists_nat_pow_near hX1 (by norm_num : (1 : ℝ) < 2)
    apply interpolationWeight_tsum_le_at_pivot hA hB ha hb hX k (Or.inr hk)
    simpa only [pow_succ, mul_comm] using hkup.le
  · apply interpolationWeight_tsum_le_at_pivot hA hB ha hb hX 0 (Or.inl rfl)
    calc
      X ≤ 1 := le_of_lt (lt_of_not_ge hX1)
      _ ≤ 2 * (2 : ℝ)^0 := by norm_num

theorem interpolationWeight_N_squared {A B a b N : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    Summable (interpolationWeight A B a b (N^2)) ∧
      (∑' n, interpolationWeight A B a b (N^2) n) ≤ interpolationWeightConstant A B a b :=
  ⟨interpolationWeight_summable hA hB hb (sq_pos_of_pos hN),
    interpolationWeight_tsum_le hA hB ha hb (sq_pos_of_pos hN)⟩

theorem interpolationWeight_finite_schur {A B a b N : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (S T : Finset ℕ) (c d : ℕ → ℝ) :
    (∑ i ∈ S, ∑ j ∈ T, interpolationWeight A B a b (N^2) (i+j) * c i * d j) ≤
      interpolationWeightConstant A B a b * Real.sqrt (∑ i ∈ S, (c i)^2) *
        Real.sqrt (∑ j ∈ T, (d j)^2) := by
  obtain ⟨hsum, hbound⟩ := interpolationWeight_N_squared hA hB ha hb hN
  exact finite_hankel_schur S T _ c d
    (interpolationWeight_nonneg hA hB (sq_pos_of_pos hN)) hsum
    (interpolationWeightConstant_nonneg hA hB ha hb) hbound

theorem interpolationWeight_finite_schur_lp {P : ENNReal} [Fact (1 ≤ P)] (hP2 : P ≤ 2)
    {A B a b N : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (S T : Finset ℕ) (c d : ℕ → ℝ) :
    (∑ i ∈ S, ∑ j ∈ T, interpolationWeight A B a b (N^2) (i+j) * c i * d j) ≤
      interpolationWeightConstant A B a b *
        (∑ i ∈ S, |c i|^P.toReal)^(1/P.toReal) *
        (∑ j ∈ T, |d j|^P.toReal)^(1/P.toReal) := by
  obtain ⟨hsum, hbound⟩ := interpolationWeight_N_squared hA hB ha hb hN
  have hnonneg := interpolationWeight_nonneg hA hB (sq_pos_of_pos hN) (a := a) (b := b)
  apply finite_weighted_schur_lp hP2 S T _ c d (interpolationWeightConstant_nonneg hA hB ha hb)
  · exact fun i _ j _ => hnonneg (i+j)
  · exact fun i _ => (finite_hankel_row_sum_le _ hnonneg hsum i T).trans hbound
  · intro j _
    simpa only [Nat.add_comm] using (finite_hankel_row_sum_le _ hnonneg hsum j S).trans hbound

theorem interpolation_gaps_pos {q p : ℝ} (hq : 0 < q) (hqp : q < p) (hp2 : p < 2) :
    0 < 1/q - 1/p ∧ 0 < 1/p - (1/2 : ℝ) := by
  constructor
  · exact sub_pos.mpr (one_div_lt_one_div_of_lt hq hqp)
  · exact sub_pos.mpr (one_div_lt_one_div_of_lt (hq.trans hqp) hp2)

end PrimeSquares
