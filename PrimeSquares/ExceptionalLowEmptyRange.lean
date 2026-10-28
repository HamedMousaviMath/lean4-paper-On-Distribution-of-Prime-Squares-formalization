import PrimeSquares.ExceptionalPhysicalLow

open Finset
namespace PrimeSquares

theorem exceptionalLow_set_empty (S : Finset ℕ) {B Q : ℝ} (hB : 0 < B) (hBQ : Q < B)
    (hpos : ∀ d ∈ S,1 ≤ d) (hwidth : ∀ d ∈ S,B*(d : ℝ) ≤ Q) : S=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hdp : (1 : ℝ) ≤ d := by exact_mod_cast hpos d hd
  have h := hwidth d hd
  nlinarith

theorem exceptionalPhysicalLowKernel_empty (N Q q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (β : ℝ) (x : ℤ) :
    exceptionalPhysicalLowKernel N Q q₀ χ₀ β ∅ x=0 := by simp [exceptionalPhysicalLowKernel]

end PrimeSquares
