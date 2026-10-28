import PrimeSquares.GoldbachMajorApproximationComplete
import PrimeSquares.GeneralLocalEuler

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachSmoothCoefficient (R : ℝ) (k : ℕ) (ℓ b n : ℤ) (q : ℕ) : ℂ :=
  if ∀ p∈q.primeFactors,(p:ℝ)≤R then generalCoefficient q k ℓ b n else 0

noncomputable def goldbachArithmeticFactor (R : ℝ) (k : ℕ) (ℓ b n : ℤ) : ℂ :=
  generalTwoEulerFactor k ℓ b n *
    ∏ p∈oddPrimesBelow (⌊R⌋₊+1),
      (p:ℂ)*((p.gcd k).totient:ℂ)/((p:ℂ)-1)^2*(primeSolutionCount p k ℓ b n:ℂ)

theorem goldbach_prime_inclusive_cutoff {R : ℝ} (hR : 0≤R) (p : ℕ) :
    (p:ℝ)≤R ↔ p<⌊R⌋₊+1 := by
  rw [Nat.lt_succ_iff,Nat.le_floor_iff hR]

theorem goldbach_smooth_coefficient_zero_off_bound {R : ℝ} (hR : 2≤R)
    (k : ℕ) [NeZero k] (ℓ b n : ℤ) (q : ℕ)
    (hq : q∉(smoothEulerBound (⌊R⌋₊+1)).divisors) :
    goldbachSmoothCoefficient R k ℓ b n q=0 := by
  classical
  have hQ : 3≤⌊R⌋₊+1 := by
    have hh : 2≤⌊R⌋₊ := (Nat.le_floor_iff (by linarith : 0≤R)).mpr hR
    omega
  unfold goldbachSmoothCoefficient
  split_ifs with hs
  · by_contra hn
    have hd := generalCoefficient_nonzero_dvd_bound (⌊R⌋₊+1) k ℓ b n hQ q
      (fun p hp => (goldbach_prime_inclusive_cutoff (by linarith : 0≤R) p).mp (hs p hp)) hn
    exact hq (Nat.mem_divisors.mpr ⟨hd,pow_ne_zero _ (Nat.factorial_ne_zero _)⟩)
  · rfl

theorem goldbach_smooth_coefficient_abs_summable {R : ℝ} (hR : 2≤R)
    (k : ℕ) [NeZero k] (ℓ b n : ℤ) :
    Summable (fun q : ℕ => ‖goldbachSmoothCoefficient R k ℓ b n q‖) := by
  apply summable_of_ne_finset_zero (s:=(smoothEulerBound (⌊R⌋₊+1)).divisors)
  intro q hq
  rw [goldbach_smooth_coefficient_zero_off_bound hR k ℓ b n q hq,norm_zero]

theorem goldbach_smooth_series_divisor_sum {R : ℝ} (hR : 2≤R)
    (k : ℕ) [NeZero k] (ℓ b n : ℤ) :
    (∑' q : ℕ,goldbachSmoothCoefficient R k ℓ b n q)=
      ∑ q∈(smoothEulerBound (⌊R⌋₊+1)).divisors,generalCoefficient q k ℓ b n := by
  have hQ : 3≤⌊R⌋₊+1 := by
    have hh : 2≤⌊R⌋₊ := (Nat.le_floor_iff (by linarith : 0≤R)).mpr hR
    omega
  simp only [goldbachSmoothCoefficient,goldbach_prime_inclusive_cutoff (by linarith : 0≤R)]
  exact smoothGeneralSeries_eq_divisor_sum (⌊R⌋₊+1) k ℓ b n hQ

theorem goldbach_arithmetic_factor_euler {R : ℝ} (hR : 2≤R)
    (k : ℕ) [NeZero k] (ℓ b n : ℤ) (hb : IsCoprime (k:ℤ) b) :
    (∑' q : ℕ,goldbachSmoothCoefficient R k ℓ b n q)=goldbachArithmeticFactor R k ℓ b n := by
  have hQ : 3≤⌊R⌋₊+1 := by
    have hh : 2≤⌊R⌋₊ := (Nat.le_floor_iff (by linarith : 0≤R)).mpr hR
    omega
  simp only [goldbachSmoothCoefficient,goldbach_prime_inclusive_cutoff (by linarith : 0≤R)]
  exact general_progression_euler_product (⌊R⌋₊+1) k hQ ℓ b n hb

theorem goldbach_arithmetic_factor_finite_split {R : ℝ} (hR : 2≤R)
    (k : ℕ) [NeZero k] (ℓ b n : ℤ) (hb : IsCoprime (k:ℤ) b) (Y : ℝ) :
    goldbachArithmeticFactor R k ℓ b n=
      (∑ q∈(smoothEulerBound (⌊R⌋₊+1)).divisors.filter (fun q : ℕ => (q:ℝ)≤Y),
        generalCoefficient q k ℓ b n)+
      ∑ q∈(smoothEulerBound (⌊R⌋₊+1)).divisors.filter (fun q : ℕ => Y<(q:ℝ)),
        generalCoefficient q k ℓ b n := by
  classical
  rw [←goldbach_arithmetic_factor_euler hR k ℓ b n hb,goldbach_smooth_series_divisor_sum hR]
  simpa only [not_le] using (sum_filter_add_sum_filter_not
    (smoothEulerBound (⌊R⌋₊+1)).divisors (fun q : ℕ => (q:ℝ)≤Y) (fun q => generalCoefficient q k ℓ b n)).symm

end PrimeSquares
