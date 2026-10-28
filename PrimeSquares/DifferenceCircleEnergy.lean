import PrimeSquares.TwoTermSquareEnergyBound
open Finset
namespace PrimeSquares
theorem difference_circle_energy (m n : ℕ → C(PrimeCircle,ℂ)) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hm : ∀ J : Finset ℕ,∀ θ : PrimeCircle,(∑ j ∈ J,‖m j θ‖^2) ≤ A^2)
    (hn : ∀ J : Finset ℕ,∀ θ : PrimeCircle,(∑ j ∈ J,‖n j θ‖^2) ≤ B^2)
    (J : Finset ℕ) (θ : PrimeCircle) :
    (∑ j ∈ J,‖(m j-n j) θ‖^2) ≤ (2*(A+B))^2 := by
  have ht : (∑ j ∈ J,‖(m j-n j) θ‖^2) ≤ 2*(∑ j ∈ J,‖m j θ‖^2)+2*(∑ j ∈ J,‖n j θ‖^2) := by
    simpa only [sum_add_distrib,mul_sum,ContinuousMap.sub_apply] using
      sum_le_sum (fun j (_hj : j ∈ J) => norm_sub_square_two_bound (m j θ) (n j θ))
  have ha := hm J θ
  have hb := hn J θ
  nlinarith [mul_nonneg hA hB]
end PrimeSquares
