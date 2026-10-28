import PrimeSquares.BinaryTreeEnergyContainment
import Mathlib.Tactic.FinCases
open Finset
namespace PrimeSquares
theorem norm_add_square_weighted (u v : ℂ) {k E : ℝ} (hk : 0 < k) (hv : ‖v‖^2 ≤ k*E) :
    ‖u+v‖^2 ≤ (k+1)*(‖u‖^2+E) := by
  have hc := norm_finset_sum_square_weighted (univ : Finset (Fin 2))
    (fun i => if i=0 then u else v) (fun i => if i=0 then (1 : ℝ) else k)
    (fun i _ => by fin_cases i <;> simp [hk])
  have he : ‖v‖^2/k ≤ E := (div_le_iff₀ hk).mpr (by simpa only [mul_comm] using hv)
  have hh : ‖u+v‖^2 ≤ (1+k)*(‖u‖^2+‖v‖^2/k) := by
    simpa only [Fin.sum_univ_two,Fin.isValue,ite_true,Fin.one_eq_zero_iff,OfNat.ofNat_ne_one,ite_false,div_one] using hc
  calc
    _ ≤ (1+k)*(‖u‖^2+‖v‖^2/k) := hh
    _ ≤ (1+k)*(‖u‖^2+E) := mul_le_mul_of_nonneg_left (add_le_add_right he _) (by linarith)
    _ = _ := by ring
end PrimeSquares
