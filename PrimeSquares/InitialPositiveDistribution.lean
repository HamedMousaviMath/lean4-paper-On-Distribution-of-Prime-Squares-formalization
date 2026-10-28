import PrimeSquares.PositiveAverageMaximum

open Finset
open scoped lp
set_option autoImplicit false

namespace PrimeSquares

theorem finite_shift_indicator_sum (D F : Finset ℤ) (s : ℤ) :
    (∑ x∈D,if x-s∈F then (1 : ℝ) else 0)≤F.card := by
  classical
  rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one]
  apply Nat.cast_le.mpr
  exact card_le_card_of_injOn (fun x : ℤ => x-s)
    (fun x hx => (mem_filter.mp hx).2) (fun a _ b _ h => by
      have he := congrArg (fun z : ℤ => z+s) h
      simpa only [sub_add_cancel] using he)

theorem positiveAverage_indicator_l1 (A : PositiveAverageFamily) (n : ℕ) (F D : Finset ℤ) :
    (∑ x∈D,‖positiveAverage A n (finiteIndicator F) x‖)≤A.mass*F.card := by
  classical
  simp_rw [positiveAverage_indicator_real]
  rw [sum_comm]
  calc
    _ = ∑ j∈A.indices n,A.weight n j*(∑ x∈D,if x-A.shift j∈F then (1 : ℝ) else 0) := by
      simp only [mul_sum]
    _ ≤ ∑ j∈A.indices n,A.weight n j*F.card :=
      sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (finite_shift_indicator_sum D F _) (A.nonnegative n j hj))
    _ = (∑ j∈A.indices n,A.weight n j)*F.card := (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (A.mass_bound n) (Nat.cast_nonneg _)

noncomputable def initialPositiveSum (A : PositiveAverageFamily) (J : ℕ) (F : Finset ℤ) (x : ℤ) : ℝ :=
  ∑ n∈range J,‖positiveAverage A n (finiteIndicator F) x‖

theorem initialPositiveSum_nonneg (A : PositiveAverageFamily) (J : ℕ) (F : Finset ℤ) (x : ℤ) :
    0≤ initialPositiveSum A J F x := sum_nonneg (fun _ _ => norm_nonneg _)

theorem initialPositiveSum_dominates (A : PositiveAverageFamily) {J n : ℕ}
    (hn : n<J) (F : Finset ℤ) (x : ℤ) :
    ‖positiveAverage A n (finiteIndicator F) x‖≤ initialPositiveSum A J F x := by
  unfold initialPositiveSum
  exact single_le_sum (s := range J) (f := fun k : ℕ => ‖positiveAverage A k (finiteIndicator F) x‖)
    (fun k _ => norm_nonneg _) (mem_range.mpr hn)

theorem initialPositiveSum_l1 (A : PositiveAverageFamily) (J : ℕ) (F D : Finset ℤ) :
    (∑ x∈D,initialPositiveSum A J F x)≤(J : ℝ)*A.mass*F.card := by
  unfold initialPositiveSum
  rw [sum_comm]
  calc
    _ ≤ ∑ _n∈range J,A.mass*F.card := sum_le_sum (fun n _ => positiveAverage_indicator_l1 A n F D)
    _ = _ := by rw [sum_const,card_range,nsmul_eq_mul];ring

def FinitePowerBudget (g : ℤ → ℝ) (p B : ℝ) : Prop :=
  ∀ D : Finset ℤ,∑ x∈D,(g x)^p≤B

theorem finiteDistribution_real_power {g : ℤ → ℝ} (hg : ∀ x,0≤g x)
    {a p B : ℝ} (ha : 0<a) (hp : 0<p) (hbudget : FinitePowerBudget g p B) (D : Finset ℤ) :
    finiteDistribution D g a≤B/a^p := by
  have he (x : ℤ) : ‖(g x : ℂ)‖=g x := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hg x)]
  have h := finiteDistribution_chebyshev D (fun x => (g x : ℂ)) ha hp
  simp_rw [he] at h
  have h' := h.trans (hbudget D)
  exact (le_div_iff₀ (Real.rpow_pos_of_pos ha p)).mpr (by simpa only [mul_comm] using h')

theorem finitePowerBudget_lp {P : ENNReal} (hp : 0<P.toReal)
    (g : lp (fun _ : ℤ => ℝ) P) (hg : ∀ x,0≤g x) :
    FinitePowerBudget g P.toReal (‖g‖^P.toReal) := by
  intro D
  have h := lp.sum_rpow_le_norm_rpow hp g D
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hg _)] using h

theorem initialPositiveSum_distribution (A : PositiveAverageFamily) (J : ℕ) (F D : Finset ℤ)
    {t : ℝ} (ht : 0<t) :
    finiteDistribution D (initialPositiveSum A J F) (1/t)≤
      t*(J : ℝ)*A.mass*F.card := by
  have hb : FinitePowerBudget (initialPositiveSum A J F) 1 ((J : ℝ)*A.mass*F.card) := by
    intro S
    simpa only [Real.rpow_one] using initialPositiveSum_l1 A J F S
  have h := finiteDistribution_real_power (initialPositiveSum_nonneg A J F)
    (show 0<1/t by positivity) (by norm_num : (0 : ℝ)<1) hb D
  simpa only [Real.rpow_one,one_div,div_inv_eq_mul,mul_comm,mul_left_comm,mul_assoc] using h

end PrimeSquares
