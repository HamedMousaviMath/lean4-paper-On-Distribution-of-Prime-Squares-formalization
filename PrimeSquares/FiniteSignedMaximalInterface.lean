import PrimeSquares.RealLineFourierMultipliers
import Mathlib.Order.PartialSups

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

noncomputable def signedSequenceSum (u : ℕ→ℤ→ℂ) (J : ℕ) (σ : ℕ→ℂ) (x : ℤ) : ℂ :=
  ∑ j∈range J,σ j*u j x

noncomputable def finitePartialSumMaximum (u : ℕ→ℤ→ℂ) (J : ℕ) (x : ℤ) : ℝ :=
  partialSups (fun m => ‖∑ j∈range m,u j x‖) J

/-- Independent general finite-sequence Rademacher-Menshov/Khintchine
maximal consequence, uniform for 1<=p<=2. It is about arbitrary scalar
sequences on counting measure. No Fourier, annular, arithmetic, IW, cutoff,
starting-scale or current-paper conclusion occurs in its fields. -/
def RawFiniteSignedMaximalInput (C : ℝ) : Prop :=
  ∀ p : ℝ,1≤p → p≤2 → ∀ (J : ℕ) (u : ℕ→ℤ→ℂ) (B : ENNReal),
    (∀ σ : ℕ→ℂ,(∀ j∈range J,‖σ j‖≤1) →
      MemLp (signedSequenceSum u J σ) (ENNReal.ofReal p) Measure.count ∧
        eLpNorm (signedSequenceSum u J σ) (ENNReal.ofReal p) Measure.count≤B) →
    MemLp (finitePartialSumMaximum u J) (ENNReal.ofReal p) Measure.count ∧
      eLpNorm (finitePartialSumMaximum u J) (ENNReal.ofReal p) Measure.count≤
        ENNReal.ofReal (C*Real.log (2+(J : ℝ)))*B

theorem finitePartialSumMaximum_nonneg (u : ℕ→ℤ→ℂ) (J : ℕ) (x : ℤ) :
    0≤finitePartialSumMaximum u J x := by
  have h := le_partialSups (fun m => ‖∑ j∈range m,u j x‖) J
  exact (norm_nonneg _).trans h

theorem finitePartialSumMaximum_dominates (u : ℕ→ℤ→ℂ) {m J : ℕ}
    (hm : m≤J) (x : ℤ) :
    ‖∑ j∈range m,u j x‖≤finitePartialSumMaximum u J x :=
  le_partialSups_of_le (fun m => ‖∑ j∈range m,u j x‖) hm

theorem finite_signed_maximal {C : ℝ} (HRM : RawFiniteSignedMaximalInput C)
    {p : ℝ} (hp0 : 1≤p) (hp1 : p≤2) (J : ℕ) (u : ℕ→ℤ→ℂ) (B : ENNReal)
    (hu : ∀ σ : ℕ→ℂ,(∀ j∈range J,‖σ j‖≤1) →
      MemLp (signedSequenceSum u J σ) (ENNReal.ofReal p) Measure.count ∧
        eLpNorm (signedSequenceSum u J σ) (ENNReal.ofReal p) Measure.count≤B) :
    MemLp (finitePartialSumMaximum u J) (ENNReal.ofReal p) Measure.count ∧
      eLpNorm (finitePartialSumMaximum u J) (ENNReal.ofReal p) Measure.count≤
        ENNReal.ofReal (C*Real.log (2+(J : ℝ)))*B :=
  HRM p hp0 hp1 J u B hu

end PrimeSquares
