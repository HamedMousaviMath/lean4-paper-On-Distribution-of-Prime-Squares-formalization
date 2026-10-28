import PrimeSquares.LinearLocalMass

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

theorem linearSourceBallMass_enlarge_radius {C C₀ K M : ℝ}
    (hK : 1 ≤ K) (hM : 0 < M) (hC : C ≤ C₀*K)
    (f : ℓ¹(ℤ,ℂ)) (x : ℤ) :
    linearSourceBallMass C f x M ≤ K*linearSourceBallMass C₀ f x (K*M) := by
  have hKp : 0 < K := by linarith
  have hsum : (∑' y : ℤ,if |((x-y:ℤ):ℝ)| ≤ C*M then ‖f y‖ else 0) ≤
      ∑' y : ℤ,if |((x-y:ℤ):ℝ)| ≤ C₀*(K*M) then ‖f y‖ else 0 := by
    apply Summable.tsum_le_tsum _ (linearSourceBall_summable C f x M)
      (linearSourceBall_summable C₀ f x (K*M))
    intro y
    split_ifs with hy hy' hy'
    · exact le_rfl
    · have hr : C*M ≤ C₀*(K*M) := by nlinarith
      exact (hy' (hy.trans hr)).elim
    · exact norm_nonneg _
    · exact le_rfl
  unfold linearSourceBallMass
  calc
    _ ≤ M⁻¹*(∑' y : ℤ,if |((x-y:ℤ):ℝ)| ≤ C₀*(K*M) then ‖f y‖ else 0) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

theorem linearSourceLocalMass_enlarge_radius {C C₀ K : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hC : C ≤ C₀*K)
    (f : ℓ¹(ℤ,ℂ)) (x : ℤ) :
    linearSourceLocalMass C N f x ≤ K*linearSourceLocalMass C₀ N f x := by
  have hK0 : 0 ≤ K := by linarith
  have hNr : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  apply ciSup_le
  intro M
  have hMp : 0 < (M:ℝ) := hNr.trans_le M.property
  have hKM : (N:ℝ) ≤ K*M := M.property.trans (by nlinarith)
  exact (linearSourceBallMass_enlarge_radius hK hMp hC f x).trans
    (mul_le_mul_of_nonneg_left (linearSourceBallMass_le_local hN C₀ f x (K*M) hKM) hK0)

theorem linearSourceLocalMass_change_radius {C C₀ : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hC₀ : 0 < C₀) (f : ℓ¹(ℤ,ℂ)) (x : ℤ) :
    linearSourceLocalMass C N f x ≤ max 1 (C/C₀)*linearSourceLocalMass C₀ N f x := by
  apply linearSourceLocalMass_enlarge_radius hN (le_max_left _ _) _ f x
  have h := (div_le_iff₀ hC₀).mp (le_max_right (1:ℝ) (C/C₀))
  simpa only [mul_comm] using h

end PrimeSquares
