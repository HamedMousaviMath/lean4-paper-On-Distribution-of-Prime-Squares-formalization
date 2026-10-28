import PrimeSquares.FiniteDistributionBounds
import Mathlib.Tactic.Ring

open Finset
namespace PrimeSquares

/-- Normalized positive finite averages. The integer shifts and finite
index sets are data, and the uniform mass bound is explicit. -/
structure PositiveAverageFamily where
  indices : ℕ → Finset ℕ
  shift : ℕ → ℤ
  weight : ℕ → ℕ → ℝ
  mass : ℝ
  mass_one_le : 1≤mass
  nonnegative : ∀ n j,j∈indices n → 0≤weight n j
  mass_bound : ∀ n,∑ j∈indices n,weight n j≤mass

noncomputable def positiveAverage (A : PositiveAverageFamily) (n : ℕ) (f : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑ j∈A.indices n,(A.weight n j : ℂ)*f (x-A.shift j)

noncomputable def positiveMaximal (A : PositiveAverageFamily) (f : ℤ → ℂ) (x : ℤ) : ℝ :=
  ⨆ n : ℕ,‖positiveAverage A n f x‖

theorem finiteFunction_norm_bound (F : Finset ℤ) (f : ℤ → ℂ)
    (hf : ∀ x,x∉F → f x=0) (x : ℤ) : ‖f x‖≤∑ y∈F,‖f y‖ := by
  by_cases hx : x∈F
  · exact single_le_sum (fun _ _ => norm_nonneg _) hx
  · rw [hf x hx,norm_zero]
    exact sum_nonneg (fun _ _ => norm_nonneg _)

theorem positiveAverage_norm_bound (A : PositiveAverageFamily) {f : ℤ → ℂ} {B : ℝ}
    (hB : 0≤B) (hf : ∀ x,‖f x‖≤B) (n : ℕ) (x : ℤ) :
    ‖positiveAverage A n f x‖≤A.mass*B := by
  calc
    _ ≤ ∑ j∈A.indices n,‖(A.weight n j : ℂ)*f (x-A.shift j)‖ := norm_sum_le _ _
    _ = ∑ j∈A.indices n,A.weight n j*‖f (x-A.shift j)‖ := by
      apply sum_congr rfl
      intro j hj
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (A.nonnegative n j hj)]
    _ ≤ ∑ j∈A.indices n,A.weight n j*B :=
      sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hf _) (A.nonnegative n j hj))
    _ = (∑ j∈A.indices n,A.weight n j)*B := (sum_mul _ _ _).symm
    _ ≤ A.mass*B := mul_le_mul_of_nonneg_right (A.mass_bound n) hB

theorem positiveMaximal_bdd (A : PositiveAverageFamily) {f : ℤ → ℂ} {B : ℝ}
    (hB : 0≤B) (hf : ∀ x,‖f x‖≤B) (x : ℤ) :
    BddAbove (Set.range (fun n : ℕ => ‖positiveAverage A n f x‖)) := by
  refine ⟨A.mass*B,?_⟩
  rintro _ ⟨n,rfl⟩
  exact positiveAverage_norm_bound A hB hf n x

theorem positiveMaximal_dominates (A : PositiveAverageFamily) {f : ℤ → ℂ} {B : ℝ}
    (hB : 0≤B) (hf : ∀ x,‖f x‖≤B) (n : ℕ) (x : ℤ) :
    ‖positiveAverage A n f x‖≤positiveMaximal A f x := le_ciSup (positiveMaximal_bdd A hB hf x) n

theorem positiveMaximal_nonneg (A : PositiveAverageFamily) {f : ℤ → ℂ} {B : ℝ}
    (hB : 0≤B) (hf : ∀ x,‖f x‖≤B) (x : ℤ) : 0≤positiveMaximal A f x :=
  (norm_nonneg _).trans (positiveMaximal_dominates A hB hf 0 x)

theorem positiveMaximal_norm_bound (A : PositiveAverageFamily) {f : ℤ → ℂ} {B : ℝ}
    (hB : 0≤B) (hf : ∀ x,‖f x‖≤B) (x : ℤ) :
    positiveMaximal A f x≤A.mass*B := ciSup_le (fun n => positiveAverage_norm_bound A hB hf n x)

theorem finiteIndicator_norm_le_one (F : Finset ℤ) (x : ℤ) : ‖finiteIndicator F x‖≤1 := by
  classical
  by_cases hx : x∈F <;> simp [finiteIndicator,hx]

theorem positiveMaximal_indicator_bound (A : PositiveAverageFamily) (F : Finset ℤ) (x : ℤ) :
    0≤positiveMaximal A (finiteIndicator F) x ∧ positiveMaximal A (finiteIndicator F) x≤A.mass := by
  constructor
  · exact positiveMaximal_nonneg A (by norm_num : (0 : ℝ)≤1) (finiteIndicator_norm_le_one F) x
  · simpa only [mul_one] using positiveMaximal_norm_bound A (by norm_num : (0 : ℝ)≤1)
      (finiteIndicator_norm_le_one F) x

theorem positiveAverage_indicator_real (A : PositiveAverageFamily) (n : ℕ) (F : Finset ℤ) (x : ℤ) :
    ‖positiveAverage A n (finiteIndicator F) x‖=
      ∑ j∈A.indices n,A.weight n j*(if x-A.shift j∈F then 1 else 0) := by
  classical
  have he : positiveAverage A n (finiteIndicator F) x=
      ((∑ j∈A.indices n,A.weight n j*(if x-A.shift j∈F then 1 else 0) : ℝ) : ℂ) := by
    simp only [positiveAverage,finiteIndicator,Complex.ofReal_sum]
    apply sum_congr rfl
    intro j hj
    split_ifs <;> simp
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
  exact sum_nonneg (fun j hj => mul_nonneg (A.nonnegative n j hj) (by split_ifs <;> norm_num))

theorem positiveMaximal_layer_majorization (A : PositiveAverageFamily) (I : Finset ℕ)
    (E : ℕ → Finset ℤ) (c : ℕ → ℝ) (hc : ∀ j∈I,0≤c j)
    {s : ℝ} (hs : 0≤s) (f : ℤ → ℂ)
    (hmajor : ∀ y,‖f y‖≤s+∑ j∈I,c j*(if y∈E j then 1 else 0)) (x : ℤ) :
    positiveMaximal A f x≤A.mass*s+∑ j∈I,c j*positiveMaximal A (finiteIndicator (E j)) x := by
  classical
  apply ciSup_le
  intro n
  calc
    _ ≤ ∑ k∈A.indices n,A.weight n k*‖f (x-A.shift k)‖ := by
      apply (norm_sum_le _ _).trans_eq
      apply sum_congr rfl
      intro k hk
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (A.nonnegative n k hk)]
    _ ≤ ∑ k∈A.indices n,A.weight n k*(s+∑ j∈I,c j*(if x-A.shift k∈E j then 1 else 0)) :=
      sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hmajor _) (A.nonnegative n k hk))
    _ = (∑ k∈A.indices n,A.weight n k)*s+
        ∑ j∈I,c j*‖positiveAverage A n (finiteIndicator (E j)) x‖ := by
      simp_rw [mul_add,sum_add_distrib,←sum_mul,mul_sum]
      rw [sum_comm]
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [positiveAverage_indicator_real,mul_sum]
      apply sum_congr rfl
      intro k hk
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (A.mass_bound n) hs)
      (sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left
        (positiveMaximal_dominates A (by norm_num : (0 : ℝ)≤1) (finiteIndicator_norm_le_one (E j)) n x) (hc j hj)))

end PrimeSquares
