import PrimeSquares.IWSamplingSpaces
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace PrimeSquares

noncomputable def countableCoordinateMaximum (g : ℕ → ℤ → ℂ) (x : ℤ) : ℝ :=
  ((⨆ n : ℕ, ‖g n x‖₊) : NNReal)

theorem uniform_finite_integer_Lp_majorant {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (g : ℕ → ℤ → ℂ) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hbound : ∀ I : Finset ℕ, MemLp (finiteCoordinateMaximum I g) p Measure.count ∧
      eLpNorm (finiteCoordinateMaximum I g) p Measure.count ≤ B) :
    ∃ H : ℤ → ℝ, (∀ x, 0 ≤ H x) ∧ MemLp H p Measure.count ∧
      (∀ n x, ‖g n x‖ ≤ H x) ∧ eLpNorm H p Measure.count ≤ B := by
  have hpoint (n : ℕ) (x : ℤ) : ‖g n x‖ ≤ B.toReal := by
    have hE := (enorm_le_eLpNorm_count (finiteCoordinateMaximum {n} g) x hp0).trans (hbound {n}).2
    have he : finiteCoordinateMaximum {n} g x = ‖g n x‖ := by
      simp only [finiteCoordinateMaximum, Finset.sup_singleton]
      rfl
    rw [he, enorm_norm] at hE
    have ht := ENNReal.toReal_mono hB hE
    simpa only [toReal_enorm] using ht
  have hbdd (x : ℤ) : BddAbove (Set.range (fun n : ℕ => ‖g n x‖₊)) := by
    refine ⟨⟨B.toReal, ENNReal.toReal_nonneg⟩, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hpoint n x
  have hmeas : AEStronglyMeasurable (countableCoordinateMaximum g) Measure.count :=
    AEStronglyMeasurable.of_discrete
  have ht : ∀ᵐ x ∂Measure.count, Tendsto
      (fun I : Finset ℕ => finiteCoordinateMaximum I g x) atTop
      (𝓝 (countableCoordinateMaximum g x)) := by
    apply Filter.Eventually.of_forall
    intro x
    exact NNReal.continuous_coe.continuousAt.tendsto.comp (tendsto_finsetSup_ciSup (hbdd x))
  have hn : eLpNorm (countableCoordinateMaximum g) p Measure.count ≤ B :=
    Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall (fun I => (hbound I).2))
      (fun I => (hbound I).1.aestronglyMeasurable) hmeas ht
  refine ⟨countableCoordinateMaximum g, fun _ => NNReal.coe_nonneg _,
    lt_of_le_of_lt hn hB.lt_top, ?_, hn⟩
  intro n x
  exact_mod_cast (le_ciSup (hbdd x) n)

end PrimeSquares
