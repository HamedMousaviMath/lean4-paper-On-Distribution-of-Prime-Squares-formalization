import PrimeSquares.ConductorQuotientCoordinates
import PrimeSquares.PhysicalLowKernel

open Finset
namespace PrimeSquares

noncomputable def realExceptionalDenominators (q₀ M : ℕ) (Q : ℝ) : Finset ℕ :=
  (Icc 1 ⌊Q⌋₊).filter (fun d => conductorMajorant q₀*(d : ℝ) ≤ Q ∧ q₀*d ≤ M)

theorem mem_realExceptionalDenominators {q₀ M d : ℕ} (hq₀ : 0 < q₀) (Q : ℝ) :
    d ∈ realExceptionalDenominators q₀ M Q ↔
      1 ≤ d ∧ conductorMajorant q₀*(d : ℝ) ≤ Q ∧ q₀*d ≤ M := by
  classical
  simp only [realExceptionalDenominators,mem_filter,mem_Icc]
  constructor
  · rintro ⟨⟨hd,_⟩,hw,hM⟩
    exact ⟨hd,hw,hM⟩
  · rintro ⟨hd,hw,hM⟩
    have hle : (d : ℝ) ≤ conductorMajorant q₀*(d : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (conductorMajorant_one_le q₀ hq₀) (Nat.cast_nonneg d)
    exact ⟨⟨hd,Nat.le_floor (hle.trans hw)⟩,hw,hM⟩

theorem realExceptionalDenominators_subset (q₀ M : ℕ) (Q : ℝ) :
    realExceptionalDenominators q₀ M Q ⊆ Icc 1 ⌊Q⌋₊ := filter_subset _ _

end PrimeSquares
