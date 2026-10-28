import PrimeSquares.GoldbachWeightedMeanCutoffs

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_weighted_harmonic_cutoff (hT : ClassicalHalfMeanValueInput)
    (K₀ K₁ K₂ : ℝ) (hK₀ : 0≤K₀) (hK₁ : 0≤K₁) (hK₂ : 0≤K₂)
    (hM : ClassicalPrimeLogMertens K₀) (hV : ClassicalPrimeMertensRatios K₁)
    (hI : GoldbachClassicalIntervalMertens K₂) :
    ∃ D A P : ℝ,1<D ∧ 0<A ∧ 0<P ∧ ∀ R : ℝ,Real.exp 2≤R→∀ n : ℤ,∀ b : ℝ,R^D≤b→
      (∑ u∈Icc 1 ⌊b⌋₊,goldbachWeightedMultiplicative R n u/(u:ℝ))≤
        (goldbachWeightedC R n/goldbachWeightedB R n)*
          (P*(Real.log R)^6+A*(1+Real.log b)/Real.log R) := by
  obtain ⟨D,A,hD,hA,hbound⟩ := goldbach_weighted_harmonic_refined hT K₀ K₁ K₂ hK₀ hK₁ hK₂ hM hV hI
  let P := 3*((1+K₂/Real.log 2)*((D+1)/Real.log 2)^2)^3
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hP : 0<P := by dsimp only [P];positivity
  refine ⟨D,A,P,hD,hA,hP,?_⟩
  intro R hR n b hb
  have hR3 : 3≤R := by have hh := Real.add_one_le_exp (2:ℝ);linarith
  have hR0 : 0<R := by linarith
  have hR1 : 1≤R := by linarith
  have hlogR : 2≤Real.log R := by
    have hh := Real.log_le_log (Real.exp_pos 2) hR
    rwa [Real.log_exp] at hh
  have hlog2R : Real.log 2≤Real.log R := Real.log_le_log (by norm_num) (by linarith)
  have hRD : 1≤R^D := Real.one_le_rpow hR1 (by linarith)
  have hlog : Real.log (R^D+1)≤(D+1)*Real.log R := by
    have hh := Real.log_le_log (by positivity : 0<R^D+1) (show R^D+1≤2*(R^D) by linarith)
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hR0 D).ne',Real.log_rpow hR0] at hh
    linarith
  have hprefix : 3*((1+K₂/Real.log 2)*(Real.log (R^D+1)/Real.log 2)^2)^3≤P*(Real.log R)^6 := by
    have hlog0 : 0≤Real.log (R^D+1) := Real.log_nonneg (by linarith)
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (div_nonneg hlog0 hlog2.le)
        (div_le_div_of_nonneg_right hlog hlog2.le) 2)
      (show 0≤1+K₂/Real.log 2 by positivity)
    have hh' := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hh 3) (by norm_num : (0:ℝ)≤3)
    apply hh'.trans_eq
    dsimp only [P]
    ring
  have hB := goldbach_weighted_B_positive R (by linarith) n
  have hratio : 1≤goldbachWeightedC R n/goldbachWeightedB R n :=
    (le_div_iff₀ hB).mpr (by simpa only [one_mul] using goldbach_weighted_B_le_C R (by linarith) n)
  have hprefix' := hprefix.trans (le_mul_of_one_le_left (by positivity : 0≤P*(Real.log R)^6) hratio)
  have hh := hbound R hR n b hb
  apply hh.trans
  apply (add_le_add hprefix' le_rfl).trans_eq
  ring

end PrimeSquares
