import PrimeSquares.BadnessModuliCoprime
import PrimeSquares.PrimeProductDifference

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem badnessPrimeBlock_large (j p : ℕ) (hp : p ∈ badnessPrimeBlock j) :
    3^(j+1) < p ∧ (64/Real.sqrt p : ℝ) ≤ 1/((j+1:ℕ):ℝ) := by
  let n := j+1
  let R := 3^n
  let A := 64*n*R
  have hn : 0 < n := by dsimp [n]; omega
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hR : 1 ≤ R := hRpos
  have h64n : 1 ≤ 64*n := by omega
  have hRA : R ≤ A := by
    simpa only [one_mul] using Nat.mul_le_mul_right R h64n
  have hA1 : 1 ≤ A := hR.trans hRA
  have hAA : A ≤ A^2 := by
    simpa only [mul_one, pow_two] using Nat.mul_le_mul_left A hA1
  have h64A : 64*n ≤ A := by
    simpa only [mul_one] using Nat.mul_le_mul_left (64*n) hR
  have hpA : A^2 < p := badnessPrimeBlock_threshold j p hp
  constructor
  · exact hRA.trans_lt (hAA.trans_lt hpA)
  · have hp0 : (0:ℝ)<p := by exact_mod_cast (badnessPrimeBlock_prime j p hp).1.pos
    have hA0 : (0:ℝ) ≤ A := by positivity
    have hroot : (A:ℝ) ≤ Real.sqrt p :=
      (Real.le_sqrt hA0 hp0.le).mpr (by exact_mod_cast hpA.le)
    have h64AR : (64:ℝ)*(n:ℝ) ≤ A := by exact_mod_cast h64A
    have h64S := h64AR.trans hroot
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hp0) (by exact_mod_cast hn)).mpr
    simpa only [one_mul] using h64S

theorem badnessPrimeBlock_error_budget (j : ℕ) :
    ∑ p ∈ badnessPrimeBlock j, (64/Real.sqrt p : ℝ) ≤ 1 := by
  calc
    _ ≤ ∑ _p ∈ badnessPrimeBlock j, (1/((j+1:ℕ):ℝ)) :=
      Finset.sum_le_sum (fun p hp => (badnessPrimeBlock_large j p hp).2)
    _ = ((badnessPrimeBlock j).card:ℝ)*(1/((j+1:ℕ):ℝ)) := by simp
    _ = 1 := by rw [badnessPrimeBlock_card]; field_simp

theorem badnessBlockSpacing_bounds (j : ℕ) :
    (2:ℝ)^(j+1) ≤ unitSquareSpacing (badnessBlockModulus j) ∧
      unitSquareSpacing (badnessBlockModulus j) ≤ (3:ℝ)^(j+1) := by
  simpa only [badnessPrimeBlock_card, badnessBlockModulus] using
    unitSquareSpacing_primeProduct_bounds (badnessPrimeBlock j) (badnessPrimeBlock_prime j)

theorem badnessBlockDensity_bounds (j : ℕ) :
    (1/3:ℝ)^(j+1) ≤ unitSquareDensity (badnessBlockModulus j) ∧
      unitSquareDensity (badnessBlockModulus j) ≤ (1/2:ℝ)^(j+1) := by
  simpa only [badnessPrimeBlock_card, badnessBlockModulus] using
    unitSquareDensity_primeProduct_bounds (badnessPrimeBlock j) (badnessPrimeBlock_prime j)

theorem badnessBlock_small_radius (j : ℕ) (γ : ℝ) (hγ : γ ≤ 1)
    (p : ℕ) (hp : p ∈ badnessPrimeBlock j) :
    γ*unitSquareSpacing (badnessBlockModulus j) ≤ (p:ℝ) := by
  calc
    _ ≤ 1*unitSquareSpacing (badnessBlockModulus j) :=
      mul_le_mul_of_nonneg_right hγ (unitSquareSpacing_pos _).le
    _ = unitSquareSpacing (badnessBlockModulus j) := one_mul _
    _ ≤ (3:ℝ)^(j+1) := (badnessBlockSpacing_bounds j).2
    _ ≤ (p:ℝ) := by exact_mod_cast (badnessPrimeBlock_large j p hp).1.le

theorem badnessBlock_finite_conditions (HW : RawSplitQuadraticWeilInput)
    (j : ℕ) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (γ-unitSquareDensity (badnessBlockModulus j)-(3/2:ℝ)*γ^2 ≤
      cyclicThickeningDensity (badnessBlockModulus j) (unitSquareResidues (badnessBlockModulus j)) γ ∧
      cyclicThickeningDensity (badnessBlockModulus j) (unitSquareResidues (badnessBlockModulus j)) γ ≤ γ) ∧
    1-6*γ-3*unitSquareDensity (badnessBlockModulus j) ≤
      cyclicFarPairFraction (badnessBlockModulus j) (unitSquareResidues (badnessBlockModulus j)) γ := by
  exact prime_product_finite_badness_conditions HW (badnessPrimeBlock j) (badnessPrimeBlock_prime j)
    (badnessPrimeBlock_error_budget j) γ hγ (badnessBlock_small_radius j γ hγ1)

end PrimeSquares
