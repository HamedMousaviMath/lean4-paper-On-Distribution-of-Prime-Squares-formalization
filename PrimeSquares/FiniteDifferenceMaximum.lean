import PrimeSquares.FiniteSignedMaximalInterface
import PrimeSquares.InitialTemporalMaximum
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares

noncomputable def finiteDifferenceSequence (F : ℕ→ℓ²(ℤ,ℂ)) (j : ℕ) (x : ℤ) : ℂ := F (j+1) x-F j x

theorem finiteDifferenceSequence_telescope (F : ℕ→ℓ²(ℤ,ℂ)) (m : ℕ) (x : ℤ) :
    (∑ j∈range m,finiteDifferenceSequence F j x)=F m x-F 0 x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ,ih]
    unfold finiteDifferenceSequence
    ring

theorem finiteDifferenceSequence_maximum_bound (F : ℕ→ℓ²(ℤ,ℂ)) (J : ℕ) (x : ℤ) :
    initialTemporalMaximum F J x≤‖F 0 x‖+finitePartialSumMaximum (finiteDifferenceSequence F) J x := by
  apply partialSups_le
  intro m hm
  have ht := norm_add_le (F 0 x) (F m x-F 0 x)
  rw [show F 0 x+(F m x-F 0 x)=F m x by ring] at ht
  have hb := finitePartialSumMaximum_dominates (finiteDifferenceSequence F) hm x
  rw [finiteDifferenceSequence_telescope] at hb
  linarith

theorem finiteDifferenceSequence_maximum_Lp (F : ℕ→ℓ²(ℤ,ℂ)) (J : ℕ) {p : ENNReal}
    (hp : 1≤p) (h0 : MemLp (F 0 : ℤ→ℂ) p Measure.count)
    (hmax : MemLp (finitePartialSumMaximum (finiteDifferenceSequence F) J) p Measure.count) :
    MemLp (initialTemporalMaximum F J) p Measure.count ∧
      eLpNorm (initialTemporalMaximum F J) p Measure.count≤
        eLpNorm (F 0 : ℤ→ℂ) p Measure.count+
          eLpNorm (finitePartialSumMaximum (finiteDifferenceSequence F) J) p Measure.count := by
  let g : ℤ→ℝ := fun x => ‖F 0 x‖+finitePartialSumMaximum (finiteDifferenceSequence F) J x
  have hg : MemLp g p Measure.count :=
    (h0.norm.add hmax).ae_eq (Filter.Eventually.of_forall (fun _ => rfl))
  have hm : AEStronglyMeasurable (initialTemporalMaximum F J) Measure.count :=
    (measurable_of_countable _).aestronglyMeasurable
  have hd : ∀ᵐ x ∂Measure.count,‖initialTemporalMaximum F J x‖≤g x := by
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (initialTemporalMaximum_nonneg F J x)]
      exact finiteDifferenceSequence_maximum_bound F J x)
  refine ⟨hg.mono' hm hd,?_⟩
  calc
    _ ≤ eLpNorm g p Measure.count :=
      eLpNorm_mono_ae hm (hd.mono (fun x hx => hx.trans (le_abs_self (g x))))
    _ ≤ eLpNorm (fun x => ‖F 0 x‖) p Measure.count+
        eLpNorm (finitePartialSumMaximum (finiteDifferenceSequence F) J) p Measure.count := by
      change eLpNorm ((fun x => ‖F 0 x‖)+finitePartialSumMaximum (finiteDifferenceSequence F) J) p Measure.count≤_
      exact eLpNorm_add_le hp
    _ = _ := by rw [eLpNorm_norm _ h0.aestronglyMeasurable]

end PrimeSquares
