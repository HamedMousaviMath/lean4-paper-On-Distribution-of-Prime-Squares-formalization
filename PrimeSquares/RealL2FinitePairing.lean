import PrimeSquares.CircleEnergyMaximalWitness

open Finset
open scoped lp
namespace PrimeSquares

theorem real_l2_finite_sum_bound {α : Type*} (G : Finset α) (g : lp (fun _ : α => ℝ) 2)
    (hg : ∀ x ∈ G,0 ≤ g x) :
    (∑ x ∈ G,g x) ≤ ‖g‖*Real.sqrt (G.card : ℝ) := by
  have he : (∑ x ∈ G,‖g x‖^2) ≤ ‖g‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.sum_rpow_le_norm_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) g G
  have hs : (∑ x ∈ G,g x)^2 ≤ (∑ x ∈ G,‖g x‖^2)*(G.card : ℝ) := by
    have hh := sum_mul_sq_le_sq_mul_sq G (fun x => g x) (fun _ => (1 : ℝ))
    simpa only [mul_one,one_pow,sum_const,nsmul_eq_mul,mul_one,Real.norm_eq_abs,sq_abs] using hh
  have ht := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg G.card)
  have hp := Real.sq_sqrt (Nat.cast_nonneg G.card)
  have hsum : 0 ≤ ∑ x ∈ G,g x := sum_nonneg hg
  have hn := norm_nonneg g
  have hr := Real.sqrt_nonneg (G.card : ℝ)
  have hpos : 0 ≤ ‖g‖*Real.sqrt (G.card : ℝ) := mul_nonneg hn hr
  have heq : (‖g‖*Real.sqrt (G.card : ℝ))^2=‖g‖^2*(G.card : ℝ) := by rw [mul_pow,hp]
  nlinarith

theorem real_l2_majorant_finite_sum {α : Type*} (G : Finset α) (g : lp (fun _ : α => ℝ) 2)
    (F : α → ℂ) (hg : ∀ x ∈ G,0 ≤ g x) (hF : ∀ x ∈ G,‖F x‖ ≤ g x) :
    (∑ x ∈ G,‖F x‖) ≤ ‖g‖*Real.sqrt (G.card : ℝ) :=
  (sum_le_sum hF).trans (real_l2_finite_sum_bound G g hg)

end PrimeSquares
