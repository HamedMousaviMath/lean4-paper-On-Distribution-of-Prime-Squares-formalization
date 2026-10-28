import PrimeSquares.CollarTailSummability
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace PrimeSquares

theorem collarFactor_square_summable {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) {q Q : ℝ} (hq : 0 < q) (hQ : 0 < Q) (θ : ℝ) :
    Summable (fun j : ℕ => ‖annularCollarFactor ((2 : ℕ)^j*M) (β j) q Q θ‖^2) := by
  classical
  by_cases h : ∃ j : ℕ,annularCollarMask ((((2 : ℕ)^j*M : ℕ) : ℝ)) q Q θ ≠ 0
  · obtain ⟨i,hi,_⟩ := annularCollar_first_scale M q Q θ h
    have hs := collarFactor_tail_square_summable hM β hβ0 hβ1 hq hQ i hi
    apply (summable_nat_add_iff i).mp
    simpa only [Nat.add_comm] using hs
  · have hz := annularCollar_no_onset M q Q θ h
    have he : (fun j : ℕ => ‖annularCollarFactor ((2 : ℕ)^j*M) (β j) q Q θ‖^2)=fun _ => 0 := by
      funext j
      rw [annularCollarFactor_zero_of_mask _ _ _ _ _ (hz j),norm_zero,zero_pow (by norm_num : 2 ≠ 0)]
    rw [he]
    exact summable_zero

end PrimeSquares
