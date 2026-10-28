import PrimeSquares.CircleAnnularErrorSupport
open Finset
namespace PrimeSquares
noncomputable def rationalProjectionErrorBlock (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (s : ℕ) (β : ℚ → ℝ) (c : ℚ → ℂ) : C(PrimeCircle,ℂ) :=
  ∑ r ∈ Γ,c r • circleAnnularProjectionError N hN (β r) s r
theorem rationalProjectionErrorBlock_zero (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    {s : ℕ} (hs : 1 ≤ s) (β : ℚ → ℝ) (c : ℚ → ℂ) (θ : PrimeCircle)
    (hz : ∀ r ∈ Γ,circleSourceCutoff s r θ=0) :
    rationalProjectionErrorBlock Γ N hN s β c θ=0 := by
  simp only [rationalProjectionErrorBlock,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  exact sum_eq_zero (fun r hr => by rw [circleAnnularProjectionError_cutoff_zero N hN (β r) hs r θ (hz r hr),mul_zero])
end PrimeSquares
