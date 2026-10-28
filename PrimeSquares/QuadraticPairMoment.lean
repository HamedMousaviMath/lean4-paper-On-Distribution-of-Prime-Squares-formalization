import PrimeSquares.FiniteAdditiveResidueCounts
import PrimeSquares.QuadraticCorrelationRelative

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem additivePairCount_quadraticCorrelation (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    (additivePairCount (unitSquareResidues p) t : ℝ)=quadraticCorrelation p {0,t} := by
  classical
  unfold additivePairCount quadraticCorrelation
  apply congrArg (fun R : Finset (ZMod p) => (R.card : ℝ))
  ext a
  simp

theorem quadratic_pair_relative_error (HW : RawSplitQuadraticWeilInput)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (t : ZMod p) (ht : t ≠ 0) :
    |(additivePairCount (unitSquareResidues p) t : ℝ)/
      (primeResidueDensity p^2*(p:ℝ))-1| ≤ 54/Real.sqrt p := by
  have hc : ({0,t} : Finset (ZMod p)).card=2 := by simp [Ne.symm ht]
  have h := quadraticCorrelation_relative_error HW p hp {0,t}
  rw [hc, ←additivePairCount_quadraticCorrelation] at h
  norm_num at h
  exact h

theorem quadratic_pair_moment (HW : RawSplitQuadraticWeilInput)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (t : ZMod p) (ht : t ≠ 0) :
    (additivePairCount (unitSquareResidues p) t : ℝ) ≤
      (1+54/Real.sqrt p)*(((unitSquareResidues p).card : ℝ)^2/p) := by
  have hb := primeResidueDensity_bounds p hp
  have hp0 : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hr0 : 0 < primeResidueDensity p := by linarith
  have hbase : 0 < primeResidueDensity p^2*(p:ℝ) := by positivity
  have hnorm := (abs_le.mp (quadratic_pair_relative_error HW p hp t ht)).2
  have hdiv : (additivePairCount (unitSquareResidues p) t : ℝ)/
      (primeResidueDensity p^2*(p:ℝ)) ≤ 1+54/Real.sqrt p := by linarith
  have hbound := (div_le_iff₀ hbase).mp hdiv
  have heq : primeResidueDensity p^2*(p:ℝ)=
      ((unitSquareResidues p).card : ℝ)^2/p := by
    unfold primeResidueDensity
    field_simp
  rw [heq] at hbound
  exact hbound

end PrimeSquares
