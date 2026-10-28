import PrimeSquares.ExponentGeometricBound
import Mathlib.NumberTheory.ArithmeticFunction.Misc

open Finset
namespace PrimeSquares

theorem divisors_card_primePower_product (q : ℕ) (hq : 0 < q) :
    (q.divisors.card : ℝ) = ∏ p ∈ q.primeFactors, ((q.factorization p : ℝ)+1) := by
  rw [Nat.card_divisors hq.ne',Nat.cast_prod]
  simp only [Nat.cast_add,Nat.cast_one]

theorem divisors_card_weighted_power {ε A : ℝ} (_hA : 1 ≤ A)
    (hp : ∀ (p n : ℕ), 2 ≤ p → (n : ℝ)+1 ≤ A*((p : ℝ)^n)^ε)
    (q : ℕ) (hq : 0 < q) :
    (q.divisors.card : ℝ) ≤ A^q.primeFactors.card*(q : ℝ)^ε := by
  rw [divisors_card_primePower_product q hq]
  calc
    _ ≤ ∏ p ∈ q.primeFactors, A*((p : ℝ)^q.factorization p)^ε := by
      apply prod_le_prod₀
      · intro p _;positivity
      · intro p hpq
        exact hp p (q.factorization p) (Nat.prime_of_mem_primeFactors hpq).two_le
    _ = A^q.primeFactors.card*(∏ p ∈ q.primeFactors, (p : ℝ)^q.factorization p)^ε := by
      rw [prod_mul_distrib,prod_const,Real.finsetProd_rpow]
      intro p _;positivity
    _ = _ := by
      congr 1
      apply congrArg (fun t : ℝ => t^ε)
      exact_mod_cast (Nat.prod_primeFactors_pow_factorization hq.ne').symm

theorem divisors_card_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q → (q.divisors.card : ℝ) ≤ C*(q : ℝ)^ε := by
  obtain ⟨A,hA,ha⟩ := primePower_exponent_bound (half_pos hε)
  obtain ⟨C,hC,hc⟩ := primeFactor_pow_le_rpow A hA (ε/2) (half_pos hε)
  refine ⟨C,hC,?_⟩
  intro q hq
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    _ ≤ A^q.primeFactors.card*(q : ℝ)^(ε/2) := divisors_card_weighted_power hA ha q hq
    _ ≤ (C*(q : ℝ)^(ε/2))*(q : ℝ)^(ε/2) :=
      mul_le_mul_of_nonneg_right (hc q hq) (Real.rpow_nonneg hqp.le _)
    _ = _ := by rw [mul_assoc,←Real.rpow_add hqp];congr 2;ring

end PrimeSquares
