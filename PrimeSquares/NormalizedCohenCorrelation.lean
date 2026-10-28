import PrimeSquares.TruncatedCohenBound
import PrimeSquares.TwistedCorrelation

open Finset
namespace PrimeSquares

noncomputable def normalizedCohenCorrelation (q : ℕ) (x : ℤ) : ℂ :=
  (q.totient : ℂ)⁻¹*cohenCorrelation q x

theorem normalizedCohenCorrelation_weight (q : ℕ) (x : ℤ) :
    ‖normalizedCohenCorrelation q x‖/(q : ℝ)=cohenWeight q x := by
  rw [normalizedCohenCorrelation,norm_mul,norm_inv,Complex.norm_natCast]
  unfold cohenWeight
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem normalizedCohenCorrelation_log (Q : ℕ) (hQ : 2 ≤ Q) (x : ℤ) :
    (∑ q ∈ Icc 1 Q,‖normalizedCohenCorrelation q x‖/(q : ℝ)) ≤
      (cohenLogConstant/2)*Real.log ((Q : ℝ)+1) := by
  simp_rw [normalizedCohenCorrelation_weight]
  exact truncated_cohen_log_bound Q hQ x

theorem normalizedCohenCorrelation_principal (q : ℕ) [NeZero q] (x : ℤ) :
    normalizedCohenCorrelation q x=twistedSquareCorrelation q 1 (x : ZMod q) := by
  rw [twistedSquareCorrelation_principal,normalizedCohenCorrelation,cohenCorrelation_eq]

end PrimeSquares
