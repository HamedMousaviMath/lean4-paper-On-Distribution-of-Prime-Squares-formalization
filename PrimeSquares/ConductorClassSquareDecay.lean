import PrimeSquares.ConductorClassPowerDecay
namespace PrimeSquares
theorem conductor_class_square_decay {ε : ℝ} (hε : 0 ≤ ε) (q₀ : ℕ → ℕ)
    (hclass : ∀ i,2^i ≤ q₀ i) (i : ℕ) : ((q₀ i : ℝ)^(-ε))^2 ≤ ((2 : ℝ)^(-(2*ε)))^i := by
  have hq : (0 : ℝ) < q₀ i := by exact_mod_cast conductor_class_positive q₀ hclass i
  calc
    _ = (q₀ i : ℝ)^(-(2*ε)) := by rw [←Real.rpow_mul_natCast hq.le];congr 1;ring
    _ ≤ _ := conductor_class_power_decay (show 0 ≤ 2*ε by positivity) q₀ hclass i
end PrimeSquares
