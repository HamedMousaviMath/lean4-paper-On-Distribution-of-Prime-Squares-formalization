import PrimeSquares.QuadraticCorrelationWeilBound
import PrimeSquares.BoundedPowerDifference

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def primeResidueDensity (p : ℕ) [Fact p.Prime] : ℝ :=
  (unitSquareResidues p).card/p

theorem primeResidueDensity_formula (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    primeResidueDensity p=((p:ℝ)-1)/(2*p) := by
  rw [primeResidueDensity, unitSquareResidues_prime_card_real p hp]
  ring

theorem primeResidueDensity_bounds (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (1/3:ℝ) ≤ primeResidueDensity p ∧ primeResidueDensity p ≤ 1/2 :=
  unitSquareResidues_prime_density p hp

theorem quadratic_correlation_mainterm_shift (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k : ℕ) :
    |primeResidueDensity p^k*(p:ℝ)-(p:ℝ)/(2:ℝ)^k| ≤ (k:ℝ)/2 := by
  have hb := primeResidueDensity_bounds p hp
  have hp0 : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hd : |primeResidueDensity p-(1/2:ℝ)|=1/(2*p) := by
    rw [abs_of_nonpos (by linarith : primeResidueDensity p-1/2 ≤ 0), primeResidueDensity_formula p hp]
    field_simp
    ring
  have hpow := bounded_power_difference (by linarith : 0 ≤ primeResidueDensity p)
    (by linarith : primeResidueDensity p ≤ 1) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) k
  rw [hd] at hpow
  calc
    _ = |(primeResidueDensity p^k-(1/2:ℝ)^k)*(p:ℝ)| := by
      congr 1
      rw [div_pow, one_pow]
      ring
    _ = |primeResidueDensity p^k-(1/2:ℝ)^k| *(p:ℝ) := by rw [abs_mul, abs_of_pos hp0]
    _ ≤ ((k:ℝ)*(1/(2*p)))*p := mul_le_mul_of_nonneg_right hpow hp0.le
    _ = (k:ℝ)/2 := by field_simp

theorem quadraticCorrelation_density_error (HW : RawSplitQuadraticWeilInput)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (S : Finset (ZMod p)) :
    |quadraticCorrelation p S-primeResidueDensity p^S.card*(p:ℝ)| ≤
      3*(S.card:ℝ)*Real.sqrt p := by
  have hsqrt : 1 ≤ Real.sqrt p := Real.one_le_sqrt.mpr
    (by exact_mod_cast (Fact.out : p.Prime).one_le)
  calc
    _ ≤ |quadraticCorrelation p S-(p:ℝ)/(2:ℝ)^S.card|+
        |(p:ℝ)/(2:ℝ)^S.card-primeResidueDensity p^S.card*(p:ℝ)| := abs_sub_le _ _ _
    _ ≤ 2*(S.card:ℝ)*Real.sqrt p+(S.card:ℝ)/2 :=
      add_le_add (quadraticCorrelation_Weil_error HW p hp S)
        (by simpa only [abs_sub_comm] using quadratic_correlation_mainterm_shift p hp S.card)
    _ ≤ _ := by nlinarith [Nat.cast_nonneg (α:=ℝ) S.card]

theorem primeResidueDensity_power_lower (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k : ℕ) :
    1 ≤ (3:ℝ)^k*primeResidueDensity p^k := by
  have hpow : (1/3:ℝ)^k ≤ primeResidueDensity p^k := by
    gcongr
    exact (primeResidueDensity_bounds p hp).1
  calc
    (1:ℝ) = (3:ℝ)^k*(1/3:ℝ)^k := by rw [←mul_pow]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

theorem quadraticCorrelation_relative_error (HW : RawSplitQuadraticWeilInput)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (S : Finset (ZMod p)) :
    |quadraticCorrelation p S/(primeResidueDensity p^S.card*(p:ℝ))-1| ≤
      (3*(S.card:ℝ)*(3:ℝ)^S.card)/Real.sqrt p := by
  have hb := primeResidueDensity_bounds p hp
  have hp0 : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hr0 : 0 < primeResidueDensity p := by linarith
  have hbase : 0 < primeResidueDensity p^S.card*(p:ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hpow := primeResidueDensity_power_lower p hp S.card
  have herror := quadraticCorrelation_density_error HW p hp S
  have hlarge : 3*(S.card:ℝ)*Real.sqrt p ≤
      (3*(S.card:ℝ)*(3:ℝ)^S.card)*primeResidueDensity p^S.card*Real.sqrt p := by
    have hm := mul_le_mul_of_nonneg_left hpow (by positivity :
      0 ≤ 3*(S.card:ℝ)*Real.sqrt p)
    nlinarith
  have heq : ((3*(S.card:ℝ)*(3:ℝ)^S.card)/Real.sqrt p)*
      (primeResidueDensity p^S.card*(p:ℝ)) =
        (3*(S.card:ℝ)*(3:ℝ)^S.card)*primeResidueDensity p^S.card*Real.sqrt p := by
    have hdiv : (p:ℝ)/Real.sqrt p=Real.sqrt p :=
      (div_eq_iff hsqrt.ne').mpr (by nlinarith [Real.sq_sqrt hp0.le])
    calc
      _ = (3*(S.card:ℝ)*(3:ℝ)^S.card)*primeResidueDensity p^S.card*
          ((p:ℝ)/Real.sqrt p) := by ring
      _ = _ := by rw [hdiv]
  have he : |quadraticCorrelation p S/(primeResidueDensity p^S.card*(p:ℝ))-1| =
      |quadraticCorrelation p S-primeResidueDensity p^S.card*(p:ℝ)|/
        (primeResidueDensity p^S.card*(p:ℝ)) := by
    calc
      _ = |(quadraticCorrelation p S-primeResidueDensity p^S.card*(p:ℝ))/
          (primeResidueDensity p^S.card*(p:ℝ))| := by congr 1; field_simp
      _ = _ := by rw [abs_div, abs_of_pos hbase]
  rw [he]
  apply (div_le_iff₀ hbase).mpr
  rw [heq]
  exact herror.trans hlarge

end PrimeSquares
