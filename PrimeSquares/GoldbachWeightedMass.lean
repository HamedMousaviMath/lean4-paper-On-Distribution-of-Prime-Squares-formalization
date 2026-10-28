import PrimeSquares.GoldbachWeightedPairs
import PrimeSquares.GoldbachWeightedArchimedean

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

noncomputable def goldbachWeightedMassConstant (K : ℝ) : ℝ :=
  (9/2:ℝ)*((1+K/Real.log 2)*(3/Real.log 2)^2)^3

theorem goldbach_weighted_mass_constant_positive (K : ℝ) (hK : 0≤K) :
    0<goldbachWeightedMassConstant K := by
  have hh : 0<Real.log 2 := Real.log_pos (by norm_num)
  dsimp only [goldbachWeightedMassConstant]
  positivity

theorem goldbach_weighted_mass_log_bound (R z K : ℝ) (N : ℕ) (n : ℤ)
    (hK : 0≤K) (hN : 2≤N) (hL : 1≤Real.log N) (hI : GoldbachClassicalIntervalMertens K) :
    (∑ i∈goldbachWeightedPairs N z,goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ))≤
      goldbachWeightedMassConstant K*(Real.log N)^7 := by
  have hh := goldbach_weighted_pairs_harmonic R z N n K hK hN hI
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hNsq : (1:ℝ)≤(N:ℝ)^2 := by
    have hNr : (2:ℝ)≤N := by exact_mod_cast hN
    nlinarith
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlog2N : Real.log 2≤Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hlog : Real.log ((N:ℝ)^2+1)≤3*Real.log N := by
    have hh := Real.log_le_log (by positivity : (0:ℝ)<(N:ℝ)^2+1)
      (show (N:ℝ)^2+1≤2*(N:ℝ)^2 by linarith)
    rw [Real.log_mul (by norm_num) (sq_pos_of_pos hN0).ne',Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hlog0 : 0≤Real.log ((N:ℝ)^2+1) := Real.log_nonneg (by linarith)
  have hs := pow_le_pow_left₀ (div_nonneg hlog0 hlog2.le)
    (div_le_div_of_nonneg_right hlog hlog2.le) 2
  have hp := pow_le_pow_left₀ (by positivity : 0≤(1+K/Real.log 2)*
      (Real.log ((N:ℝ)^2+1)/Real.log 2)^2)
    (mul_le_mul_of_nonneg_left hs (show 0≤1+K/Real.log 2 by positivity)) 3
  have hlast : 1+2*Real.log N≤3*Real.log N := by linarith
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤3/2)) hlast
    (by linarith : 0≤1+2*Real.log N) (by positivity)
  apply (hh.trans hm).trans_eq
  dsimp only [goldbachWeightedMassConstant]
  ring

theorem goldbach_weighted_arch_real_nonneg (N : ℕ) (n : ℝ) (ℓ : ℕ) :
    0≤(goldbachArchimedeanIntegral ℓ n (N:ℝ) ((N:ℝ)^2)).re := by
  rw [goldbach_weighted_arch_real]
  apply setIntegral_nonneg measurableSet_Icc
  intro u hu
  exact goldbach_weighted_arch_integrand_nonneg N n u ℓ hu.1

end PrimeSquares
