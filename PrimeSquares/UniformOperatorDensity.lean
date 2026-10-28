import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open Filter
open scoped Topology
namespace PrimeSquares

theorem uniform_operator_dense_cauchy {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (T : ℕ → E →L[ℂ] F) {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ n : ℕ, ‖T n‖ ≤ M) {f : E} (g : ℕ → E) (hg : Tendsto g atTop (𝓝 f))
    (hc : ∀ j : ℕ, CauchySeq (fun n : ℕ => T n (g j))) :
    CauchySeq (fun n : ℕ => T n f) := by
  apply Metric.cauchySeq_iff.mpr
  intro e he
  have hd : 0 < e/(4*(M+1)) := by positivity
  obtain ⟨j, hj⟩ := (Metric.tendsto_nhds.mp hg (e/(4*(M+1))) hd).exists
  have hclose : ‖f-g j‖ < e/(4*(M+1)) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hj
  have hmul := (lt_div_iff₀ (by positivity : 0 < 4*(M+1))).mp hclose
  have herror : M*‖f-g j‖ < e/4 := by nlinarith [norm_nonneg (f-g j)]
  obtain ⟨J, hJ⟩ := Metric.cauchySeq_iff.mp (hc j) (e/2) (by positivity)
  refine ⟨J, ?_⟩
  intro n hn m hm
  have hN : ‖T n (f-g j)‖ ≤ M*‖f-g j‖ :=
    ((T n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _))
  have hM' : ‖T m (f-g j)‖ ≤ M*‖f-g j‖ :=
    ((T m).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hT m) (norm_nonneg _))
  have hG : ‖T n (g j)-T m (g j)‖ < e/2 := by
    simpa only [dist_eq_norm] using hJ n hn m hm
  have heq : T n f-T m f = (T n (f-g j)+(T n (g j)-T m (g j)))-T m (f-g j) := by
    rw [map_sub, map_sub]
    abel
  have htriangle := (norm_sub_le (T n (f-g j)+(T n (g j)-T m (g j))) (T m (f-g j))).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  rw [←heq] at htriangle
  rw [dist_eq_norm]
  nlinarith

end PrimeSquares
