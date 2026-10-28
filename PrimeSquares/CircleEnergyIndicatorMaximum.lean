import PrimeSquares.RealL2FinitePairing

open Finset
open scoped lp
namespace PrimeSquares

theorem circle_energy_indicator_maximal_pairing (m : ℕ → C(PrimeCircle,ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ J : Finset ℕ,∀ θ : PrimeCircle,(∑ j ∈ J,‖m j θ‖^2) ≤ B^2) (F : Finset ℤ) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (m j) (finiteIndicatorLp F 2) x‖) ∧
      (∀ j x,‖integerMultiplier (m j) (finiteIndicatorLp F 2) x‖ ≤ g x) ∧
      ∀ G : Finset ℤ,(∑ x ∈ G,g x) ≤ B*Real.sqrt (F.card : ℝ)*Real.sqrt (G.card : ℝ) := by
  obtain ⟨g,hg,hg0,hd,hn⟩ := circle_energy_maximal_witness m hB hm (finiteIndicatorLp F 2)
  rw [finiteIndicatorLp_two_norm] at hn
  refine ⟨g,hg,hd,?_⟩
  intro G
  exact (real_l2_finite_sum_bound G g (fun x _ => hg0 x)).trans
    (mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg _))

end PrimeSquares
