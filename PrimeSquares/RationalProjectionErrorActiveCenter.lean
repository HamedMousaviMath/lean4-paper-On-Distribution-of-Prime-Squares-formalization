import PrimeSquares.RationalProjectionErrorBlock
import PrimeSquares.CircleSourceCutoffDisjoint
open Finset
namespace PrimeSquares
theorem rationalProjectionErrorBlock_active (Γ : Finset ℚ) {s : ℕ} (hs : 2 ≤ s)
    (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    {r : ℚ} (hr : r ∈ Γ) (θ : PrimeCircle) (hz : circleSourceCutoff s r θ ≠ 0)
    (N : ℕ) (hN : 1 ≤ N) (β : ℚ → ℝ) (c : ℚ → ℂ) :
    rationalProjectionErrorBlock Γ N hN s β c θ=c r*circleAnnularProjectionError N hN (β r) s r θ := by
  classical
  simp only [rationalProjectionErrorBlock,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  apply sum_eq_single r
  · intro t ht htr
    have ht0 := (circleSourceCutoff_disjoint hs (hc t ht) (hc r hr) htr (hd t ht) (hd r hr) θ).resolve_right hz
    rw [circleAnnularProjectionError_cutoff_zero N hN (β t) (by omega) t θ ht0,mul_zero]
  · exact fun h => (h hr).elim
end PrimeSquares
