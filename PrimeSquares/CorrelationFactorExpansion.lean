import PrimeSquares.ConductorFactors
import PrimeSquares.ElementaryPrimeProduct

open Finset
namespace PrimeSquares

noncomputable def correlationExcess (p : ℕ) : ℝ := 2/((p : ℝ)-1)

noncomputable def subsetCorrelationExcess (t : Finset ℕ) : ℝ := ∏ p ∈ t, correlationExcess p

theorem correlationExcess_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ correlationExcess p := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold correlationExcess
  exact div_nonneg (by norm_num) (by linarith)

theorem correlation_factor_excess {p : ℕ} (hp : p.Prime) :
    ((p : ℝ)+1)/((p : ℝ)-1)=1+correlationExcess p := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold correlationExcess
  have hne : (p : ℝ)-1 ≠ 0 := by linarith
  field_simp [hne]
  ring

theorem conductorCorrelationProduct_subset_expansion (n : ℕ) :
    conductorCorrelationProduct n=∑ t ∈ n.primeFactors.powerset,subsetCorrelationExcess t := by
  rw [conductorCorrelationProduct]
  calc
    _ = ∏ p ∈ n.primeFactors,(1+correlationExcess p) := by
      exact prod_congr rfl (fun p hp => correlation_factor_excess (Nat.prime_of_mem_primeFactors hp))
    _ = _ := by rw [prod_one_add];rfl

end PrimeSquares
