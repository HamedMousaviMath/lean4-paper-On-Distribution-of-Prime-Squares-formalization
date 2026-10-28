import PrimeSquares.OperatorSquareMaximal
import PrimeSquares.DyadicLogarithmicBudget
import Mathlib.Analysis.PSeries

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

noncomputable def dyadicLogSquareConstant (A : ℝ) : ℝ :=
  Real.sqrt (∑' j : ℕ, ((1+Real.log (((2:ℕ)^j:ℕ):ℝ))^(-A))^2)

theorem dyadic_log_square_summable {A : ℝ} (hA : 1/2 < A) :
    Summable (fun j : ℕ => ((1+Real.log (((2:ℕ)^j:ℕ):ℝ))^(-A))^2) := by
  have hA0 : 0 ≤ A := by linarith
  have hbase : Summable (fun j : ℕ => (j:ℝ)^(-(2*A))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift : Summable (fun j : ℕ => ((j:ℝ)+1)^(-(2*A))) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr hbase
  apply Summable.of_nonneg_of_le (fun j => sq_nonneg _)
    (fun j => ?_) (hshift.mul_left ((Real.log 2)^(-(2*A))))
  have hpos : 0 ≤ 1+Real.log (((2:ℕ)^j:ℕ):ℝ) := by
    rw [log_two_pow_nat]
    positivity
  rw [←Real.rpow_mul_natCast hpos]
  simp only [Nat.cast_ofNat]
  rw [show -A*(2:ℝ)=-(2*A) by ring]
  exact dyadic_log_inverse_power (show 0 ≤ 2*A by linarith) j

theorem dyadicLogSquareConstant_nonneg (A : ℝ) : 0 ≤ dyadicLogSquareConstant A :=
  Real.sqrt_nonneg _

theorem localError_square_majorant {A B : ℝ} (hA : 1/2 < A) (hB : 0 ≤ B)
    (T : ℕ → ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ))
    (hT : ∀ j : ℕ, ‖T j‖ ≤ B*(1+Real.log (((2:ℕ)^j:ℕ):ℝ))^(-A))
    (f : ℓ²(ℤ,ℂ)) :
    ∃ E : ℓ²(ℤ,ℝ), (∀ x,0 ≤ E x) ∧ (∀ j x,‖T j f x‖ ≤ E x) ∧
      ‖E‖ ≤ B*dyadicLogSquareConstant A*‖f‖ := by
  let w := fun j : ℕ => ((1+Real.log (((2:ℕ)^j:ℕ):ℝ))^(-A))^2
  have hw : Summable w := dyadic_log_square_summable hA
  have hsum : ∀ S : Finset ℕ, ∑ j ∈ S, ‖T j f‖^2 ≤
      (B*dyadicLogSquareConstant A*‖f‖)^2 := by
    intro S
    have hpoint (j : ℕ) : ‖T j f‖^2 ≤ B^2*w j*‖f‖^2 := by
      have h := ((T j).le_opNorm f).trans (mul_le_mul_of_nonneg_right (hT j) (norm_nonneg f))
      have hpow := pow_le_pow_left₀ (norm_nonneg _) h 2
      simpa only [mul_pow,mul_assoc] using hpow
    have hfin : ∑ j ∈ S, w j ≤ ∑' j, w j := hw.sum_le_tsum S (fun _ _ => sq_nonneg _)
    calc
      _ ≤ ∑ j ∈ S, B^2*w j*‖f‖^2 := sum_le_sum (fun j _ => hpoint j)
      _ = B^2*(∑ j ∈ S,w j)*‖f‖^2 := by rw [←sum_mul,←mul_sum]
      _ ≤ B^2*(∑' j,w j)*‖f‖^2 := by gcongr
      _ = _ := by
        rw [mul_pow,mul_pow,dyadicLogSquareConstant,Real.sq_sqrt (tsum_nonneg (fun j => sq_nonneg _))]
  have hF : FiniteSquareEnergyBound (fun j => T j f) (B*dyadicLogSquareConstant A*‖f‖) := hsum
  have hs := finiteSquareEnergy_summable _ hF
  refine ⟨squareMaximumL2 (fun j => T j f) hs,?_,?_,?_⟩
  · intro x
    exact squareMaximumValue_nonneg _ hs x
  · intro j x
    exact le_ciSup (squareMaximumValue_bddAbove _ hs x) j
  · exact finiteSquareEnergy_maximal _
      (mul_nonneg (mul_nonneg hB (dyadicLogSquareConstant_nonneg A)) (norm_nonneg f)) hF

end PrimeSquares
