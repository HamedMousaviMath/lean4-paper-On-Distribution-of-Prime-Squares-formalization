import PrimeSquares.QuadraticTripleMoment
import PrimeSquares.UnitSquareDensityProducts
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem finite_product_error_budget {I : Type*} [DecidableEq I] (S : Finset I)
    (ε : I → ℝ) (hε : ∀ i ∈ S, 0 ≤ ε i) (hsum : ∑ i ∈ S, ε i ≤ 1) :
    (∏ i ∈ S, (1+ε i)) ≤ 3 := by
  calc
    _ ≤ ∏ i ∈ S, Real.exp (ε i) := by
      apply Finset.prod_le_prod₀ (fun i hi => by linarith [hε i hi])
      intro i _
      simpa only [add_comm] using Real.add_one_le_exp (ε i)
    _ = Real.exp (∑ i ∈ S, ε i) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hsum
    _ ≤ 3 := Real.exp_one_lt_three.le

theorem finite_product_perturbed_bound {I : Type*} [DecidableEq I] (S : Finset I)
    (a b ε : I → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) (hb : ∀ i ∈ S, 0 ≤ b i)
    (hε : ∀ i ∈ S, 0 ≤ ε i) (hsum : ∑ i ∈ S, ε i ≤ 1)
    (hlocal : ∀ i ∈ S, a i ≤ (1+ε i)*b i) :
    (∏ i ∈ S, a i) ≤ 3*(∏ i ∈ S, b i) := by
  calc
    _ ≤ ∏ i ∈ S, ((1+ε i)*b i) := Finset.prod_le_prod₀ ha hlocal
    _ = (∏ i ∈ S, (1+ε i))*(∏ i ∈ S, b i) := Finset.prod_mul_distrib
    _ ≤ _ := mul_le_mul_of_nonneg_right (finite_product_error_budget S ε hε hsum)
      (Finset.prod_nonneg hb)

theorem unitSquare_model_product (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (k : ℕ) :
    (∏ p ∈ S, ((unitSquareCard p:ℝ)^k/(p:ℝ)))=
      (unitSquareCard (∏ p ∈ S, p):ℝ)^k/((∏ p ∈ S, p):ℝ) := by
  rw [Finset.prod_div_distrib, Finset.prod_pow, ←Nat.cast_prod,
    ←Nat.cast_prod, ←unitSquareCard_primeProduct S hS]

theorem global_quadratic_pair_moment (HW : RawSplitQuadraticWeilInput)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (hbudget : ∑ p ∈ S, (64/Real.sqrt p : ℝ) ≤ 1)
    (t : ℤ) (ht : ∀ p ∈ S, (t : ZMod p) ≠ 0) :
    (unitSquarePairCount (∏ p ∈ S, p) t : ℝ) ≤
      3*(unitSquareCard (∏ p ∈ S, p):ℝ)^2/((∏ p ∈ S, p):ℝ) := by
  rw [unitSquarePairCount_primeProduct S (fun p hp => (hS p hp).1), Nat.cast_prod]
  have hlocal (p : ℕ) (hp : p ∈ S) :
      (unitSquarePairCount p t : ℝ) ≤ (1+64/Real.sqrt p)*((unitSquareCard p:ℝ)^2/(p:ℝ)) := by
    have : Fact p.Prime := ⟨(hS p hp).1⟩
    rw [unitSquarePairCount_eq, unitSquareCard_eq]
    exact quadratic_pair_moment_common HW p (hS p hp).2 (t : ZMod p) (ht p hp)
  have h := finite_product_perturbed_bound S
    (fun p => (unitSquarePairCount p t : ℝ)) (fun p => (unitSquareCard p:ℝ)^2/(p:ℝ))
    (fun p => 64/Real.sqrt p)
    (fun _ _ => by positivity) (fun _ _ => by positivity)
    (fun _ _ => by positivity) hbudget hlocal
  rw [unitSquare_model_product S (fun p hp => (hS p hp).1) 2] at h
  convert h using 1; ring

theorem global_quadratic_triple_moment (HW : RawSplitQuadraticWeilInput)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (hbudget : ∑ p ∈ S, (64/Real.sqrt p : ℝ) ≤ 1) (t : ℤ) :
    (unitSquareTripleCount (∏ p ∈ S, p) t : ℝ) ≤
      3*(unitSquareCard (∏ p ∈ S, p):ℝ)^3/((∏ p ∈ S, p):ℝ) := by
  rw [unitSquareTripleCount_primeProduct S (fun p hp => (hS p hp).1), Nat.cast_prod]
  have hlocal (p : ℕ) (hp : p ∈ S) :
      (unitSquareTripleCount p t : ℝ) ≤ (1+64/Real.sqrt p)*((unitSquareCard p:ℝ)^3/(p:ℝ)) := by
    have : Fact p.Prime := ⟨(hS p hp).1⟩
    rw [unitSquareTripleCount_eq, unitSquareCard_eq]
    exact quadratic_triple_moment_common HW p (hS p hp).2 (t : ZMod p)
  have h := finite_product_perturbed_bound S
    (fun p => (unitSquareTripleCount p t : ℝ)) (fun p => (unitSquareCard p:ℝ)^3/(p:ℝ))
    (fun p => 64/Real.sqrt p)
    (fun _ _ => by positivity) (fun _ _ => by positivity)
    (fun _ _ => by positivity) hbudget hlocal
  rw [unitSquare_model_product S (fun p hp => (hS p hp).1) 3] at h
  convert h using 1; ring

end PrimeSquares
