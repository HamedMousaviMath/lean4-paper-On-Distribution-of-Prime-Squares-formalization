import PrimeSquares.LpInclusion

/-!
# A finite weighted Schur estimate

The proof retains the l2 norms of coefficient sequences and is uniform in
the number of blocks. Nonnegative Hankel weights h(i+j) have their row and
column sums bounded by the full sum of h. No interpolation or decomposition
theorem is assumed here.
-/

open Finset

namespace PrimeSquares

variable {α β : Type*}

theorem finite_weighted_cauchy (S : Finset α) (T : Finset β)
    (w : α → β → ℝ) (c : α → ℝ) (d : β → ℝ)
    (hw : ∀ i ∈ S, ∀ j ∈ T, 0 ≤ w i j) :
    (∑ i ∈ S, ∑ j ∈ T, w i j * c i * d j) ≤
      Real.sqrt (∑ i ∈ S, ∑ j ∈ T, w i j * (c i)^2) *
      Real.sqrt (∑ i ∈ S, ∑ j ∈ T, w i j * (d j)^2) := by
  have he (i : α) (hi : i ∈ S) (j : β) (hj : j ∈ T) :
      (Real.sqrt (w i j))^2 = w i j := Real.sq_sqrt (hw i hi j hj)
  have h := Real.sum_mul_le_sqrt_mul_sqrt (S ×ˢ T)
    (fun z => Real.sqrt (w z.1 z.2) * c z.1)
    (fun z => Real.sqrt (w z.1 z.2) * d z.2)
  simp only [sum_product] at h
  have hcd : (∑ i ∈ S, ∑ j ∈ T,
      (Real.sqrt (w i j) * c i) * (Real.sqrt (w i j) * d j)) =
      ∑ i ∈ S, ∑ j ∈ T, w i j * c i * d j := by
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    calc
      _ = (Real.sqrt (w i j))^2 * c i * d j := by ring
      _ = _ := by rw [he i hi j hj]
  have hc : (∑ i ∈ S, ∑ j ∈ T, (Real.sqrt (w i j) * c i)^2) =
      ∑ i ∈ S, ∑ j ∈ T, w i j * (c i)^2 := by
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [mul_pow, he i hi j hj]
  have hd : (∑ i ∈ S, ∑ j ∈ T, (Real.sqrt (w i j) * d j)^2) =
      ∑ i ∈ S, ∑ j ∈ T, w i j * (d j)^2 := by
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [mul_pow, he i hi j hj]
  rwa [hcd, hc, hd] at h

theorem finite_weighted_schur (S : Finset α) (T : Finset β)
    (w : α → β → ℝ) (c : α → ℝ) (d : β → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ i ∈ S, ∀ j ∈ T, 0 ≤ w i j)
    (hrow : ∀ i ∈ S, ∑ j ∈ T, w i j ≤ C)
    (hcol : ∀ j ∈ T, ∑ i ∈ S, w i j ≤ C) :
    (∑ i ∈ S, ∑ j ∈ T, w i j * c i * d j) ≤
      C * Real.sqrt (∑ i ∈ S, (c i)^2) * Real.sqrt (∑ j ∈ T, (d j)^2) := by
  have hc : (∑ i ∈ S, ∑ j ∈ T, w i j * (c i)^2) ≤ C * ∑ i ∈ S, (c i)^2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg _)
  have hd : (∑ i ∈ S, ∑ j ∈ T, w i j * (d j)^2) ≤ C * ∑ j ∈ T, (d j)^2 := by
    rw [sum_comm, mul_sum]
    apply sum_le_sum
    intro j hj
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right (hcol j hj) (sq_nonneg _)
  calc
    _ ≤ _ := finite_weighted_cauchy S T w c d hw
    _ ≤ Real.sqrt (C * ∑ i ∈ S, (c i)^2) * Real.sqrt (C * ∑ j ∈ T, (d j)^2) :=
      mul_le_mul (Real.sqrt_le_sqrt hc) (Real.sqrt_le_sqrt hd) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul hC, Real.sqrt_mul hC]
      calc
        _ = (Real.sqrt C)^2 * Real.sqrt (∑ i ∈ S, (c i)^2) *
            Real.sqrt (∑ j ∈ T, (d j)^2) := by ring
        _ = _ := by rw [Real.sq_sqrt hC]

theorem finite_hankel_row_sum_le (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n)
    (hsum : Summable h) (i : ℕ) (T : Finset ℕ) :
    (∑ j ∈ T, h (i+j)) ≤ ∑' n, h n := by
  have he : (∑ j ∈ T, h (i+j)) = ∑ n ∈ T.image (fun j => i+j), h n := by
    rw [sum_image]
    intro a _ b _ hab
    exact Nat.add_left_cancel hab
  rw [he]
  exact hsum.sum_le_tsum _ (fun n _ => hh n)

theorem finite_hankel_schur (S T : Finset ℕ) (h : ℕ → ℝ) (c d : ℕ → ℝ)
    (hh : ∀ n, 0 ≤ h n) (hsum : Summable h) {C : ℝ} (hC : 0 ≤ C)
    (hbound : (∑' n, h n) ≤ C) :
    (∑ i ∈ S, ∑ j ∈ T, h (i+j) * c i * d j) ≤
      C * Real.sqrt (∑ i ∈ S, (c i)^2) * Real.sqrt (∑ j ∈ T, (d j)^2) := by
  apply finite_weighted_schur S T (fun i j => h (i+j)) c d hC
  · exact fun i _ j _ => hh (i+j)
  · exact fun i _ => (finite_hankel_row_sum_le h hh hsum i T).trans hbound
  · intro j _
    simpa only [Nat.add_comm] using (finite_hankel_row_sum_le h hh hsum j S).trans hbound

theorem finite_energy_le_lp [DecidableEq α] {P : ENNReal} [Fact (1 ≤ P)]
    (hP2 : P ≤ 2) (S : Finset α) (c : α → ℝ) :
    Real.sqrt (∑ i ∈ S, (c i)^2) ≤
      (∑ i ∈ S, |c i| ^ P.toReal) ^ (1 / P.toReal) := by
  have hP : P ≠ ⊤ := ne_top_of_le_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hP2
  have hp : 0 < P.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : 1 ≤ P)).ne' hP
  let v : lp (fun _ : α => ℂ) P := ∑ i ∈ S, lp.single P i (c i : ℂ)
  have he : ‖v‖ ^ P.toReal = ∑ i ∈ S, |c i| ^ P.toReal := by
    simpa only [v, Complex.norm_real, Real.norm_eq_abs] using
      lp.norm_sum_single (E := fun _ : α => ℂ) hp (fun i => (c i : ℂ)) S
  have hinc := lp_inclusion_norm hP2 (by norm_num : (2 : ENNReal) ≠ ⊤) v
  have he2 : ‖lp.linearMapOfLE ℂ (fun _ : α => ℂ) hP2 v‖ ^ 2 = ∑ i ∈ S, (c i)^2 := by
    have hmap : lp.linearMapOfLE ℂ (fun _ : α => ℂ) hP2 v =
        ∑ i ∈ S, lp.single 2 i (c i : ℂ) := by
      apply lp.ext
      funext x
      simp only [lp.coe_linearMapOfLE_apply, v, lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
    rw [hmap]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real,
      Real.norm_eq_abs, sq_abs] using
      lp.norm_sum_single (E := fun _ : α => ℂ)
        (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (fun i => (c i : ℂ)) S
  calc
    _ = ‖lp.linearMapOfLE ℂ (fun _ : α => ℂ) hP2 v‖ := by
      rw [← he2, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ ‖v‖ := hinc
    _ = (‖v‖ ^ P.toReal) ^ (1 / P.toReal) := by
      simpa only [one_div] using (Real.rpow_rpow_inv (norm_nonneg v) hp.ne').symm
    _ = _ := by rw [he]

theorem finite_weighted_schur_lp [DecidableEq α] [DecidableEq β]
    {P : ENNReal} [Fact (1 ≤ P)] (hP2 : P ≤ 2)
    (S : Finset α) (T : Finset β) (w : α → β → ℝ) (c : α → ℝ) (d : β → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ i ∈ S, ∀ j ∈ T, 0 ≤ w i j)
    (hrow : ∀ i ∈ S, ∑ j ∈ T, w i j ≤ C)
    (hcol : ∀ j ∈ T, ∑ i ∈ S, w i j ≤ C) :
    (∑ i ∈ S, ∑ j ∈ T, w i j * c i * d j) ≤
      C * (∑ i ∈ S, |c i| ^ P.toReal) ^ (1 / P.toReal) *
        (∑ j ∈ T, |d j| ^ P.toReal) ^ (1 / P.toReal) := by
  calc
    _ ≤ _ := finite_weighted_schur S T w c d hC hw hrow hcol
    _ ≤ _ := mul_le_mul
      (mul_le_mul_of_nonneg_left (finite_energy_le_lp hP2 S c) hC)
      (finite_energy_le_lp hP2 T d) (Real.sqrt_nonneg _)
      (mul_nonneg hC (Real.rpow_nonneg (sum_nonneg fun i _ =>
        Real.rpow_nonneg (abs_nonneg (c i)) _) _))

end PrimeSquares
