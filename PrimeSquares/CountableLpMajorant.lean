import PrimeSquares.RealMultiplierSubtraction
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Measure.Count

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace PrimeSquares

theorem countable_integer_Lp_majorant {p : ℝ≥0∞} (hp : 1 ≤ p)
    (g : ℕ → ℤ → ℂ) (hg : ∀ n, MemLp (g n) p Measure.count)
    (hs : ∑' n, eLpNorm (g n) p Measure.count ≠ ∞) :
    ∃ H : ℤ → ℝ, (∀ x, 0 ≤ H x) ∧ MemLp H p Measure.count ∧
      (∀ n x, ‖g n x‖ ≤ H x) ∧
      eLpNorm H p Measure.count ≤ ∑' n, eLpNorm (g n) p Measure.count := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let G : ℕ → Lp ℝ p (Measure.count : Measure ℤ) :=
    fun n => (hg n).norm.toLp (fun x => ‖g n x‖)
  have hG (n : ℕ) : ‖G n‖ₑ = eLpNorm (g n) p Measure.count := by
    simp only [G, Lp.enorm_toLp, eLpNorm_norm _ (hg n).aestronglyMeasurable]
  have hsG : ∑' n, ‖G n‖ₑ ≠ ∞ := by simpa only [hG] using hs
  have hsx : ∀ x, Summable (fun n => ‖g n x‖) :=
    Measure.ae_count_iff.mp (summable_norm_of_tsum_eLpNorm_ne_top hp hs)
  have hGe (n : ℕ) : (G n : ℤ → ℝ) =ᵐ[Measure.count] fun x => ‖g n x‖ :=
    (hg n).norm.coeFn_toLp
  have hsum : (⇑(∑' n, G n) : ℤ → ℝ) =ᵐ[Measure.count] fun x => ∑' n, ‖g n x‖ := by
    filter_upwards [Lp.coeFn_tsum hsG, ae_all_iff.mpr hGe] with x hx hxG
    rw [hx]
    exact tsum_congr (fun n => hxG n)
  refine ⟨fun x => ∑' n, ‖g n x‖, fun x => tsum_nonneg (fun n => norm_nonneg _),
    (Lp.memLp (∑' n, G n)).ae_eq hsum, ?_, ?_⟩
  · intro n x
    exact (hsx x).le_tsum n (fun i _ => norm_nonneg _)
  · rw [←eLpNorm_congr_ae hsum, ←Lp.enorm_def]
    calc
      ‖∑' n, G n‖ₑ ≤ ∑' n, ‖G n‖ₑ := enorm_tsum_le_tsum_enorm
      _ = _ := tsum_congr hG

end PrimeSquares
