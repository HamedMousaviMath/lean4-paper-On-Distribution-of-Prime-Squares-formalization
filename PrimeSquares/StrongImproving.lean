import PrimeSquares.FiniteOutputDuality
import PrimeSquares.FiniteBilinearImproving
import PrimeSquares.LpRealizations

/-!
# Strong operator improving from the checked finite bilinear estimate

The coarse actual l2 realization supplies membership. Finite-output
duality proves the sharper norm on finite inputs, and density extends it
with the same constant to every lp input.
-/

open Finset
open scoped lp

namespace PrimeSquares

theorem kernelLp_realization_single {P Q : ENNReal} [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    {K : ℤ → ℂ} (T : lp (fun _ : ℤ => ℂ) P →L[ℂ] lp (fun _ : ℤ => ℂ) Q)
    (hT : ∀ F : Finset ℤ, ∀ x, indicatorConvolution K F x = T (finiteIndicatorLp F P) x)
    (i : ℤ) (z : ℂ) (x : ℤ) : T (lp.single P i z) x = K (x-i) * z := by
  have he : lp.single P i z = z • finiteIndicatorLp {i} P := by
    rw [finiteIndicatorLp_singleton]
    simpa only [smul_eq_mul, mul_one] using
      lp.single_smul (E := fun _ : ℤ => ℂ) P i z (1 : ℂ)
  rw [he, map_smul]
  change z * T (finiteIndicatorLp {i} P) x = _
  rw [← hT]
  simp only [indicatorConvolution, sum_singleton, mul_comm]

theorem kernelLp_realization_finiteInput {P Q : ENNReal} [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    {K : ℤ → ℂ} (T : lp (fun _ : ℤ => ℂ) P →L[ℂ] lp (fun _ : ℤ => ℂ) Q)
    (hT : ∀ F : Finset ℤ, ∀ x, indicatorConvolution K F x = T (finiteIndicatorLp F P) x)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    T (finiteInputLp F f P) x = finiteConvolution K F f x := by
  simp only [finiteInputLp, map_sum, lp.coeFn_sum, Finset.sum_apply, finiteConvolution]
  exact sum_congr rfl (fun y _ => kernelLp_realization_single T hT y (f y) x)

theorem restricted_l2_strong_improving {P Q : ENNReal} [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    (hP2 : P ≤ 2) (h2Q : 2 ≤ Q) (hQ : Q ≠ ⊤)
    (hconj : Q.toReal = holderConjugate P.toReal) (hp1 : 1 < P.toReal)
    {K : ℤ → ℂ} {N q A B : ℝ} (hN : 0 < N) (hq : 0 < q)
    (hqp : q < P.toReal) (hp2 : P.toReal < 2) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hK : NonnegativeKernel K) (h2 : KernelL2Bound K B)
    (hrestricted : ∀ F G : Finset ℤ, ‖restrictedKernelPairing K F G‖ ≤
      A * N^(1-2/q) * (F.card : ℝ)^(1/q) * (G.card : ℝ)^(1/q)) :
    KernelLpBound K P Q
      ((interpolationWeightConstant A B (1/q-1/P.toReal) (1/P.toReal-1/2) *
        (3 : ℝ)^(2/P.toReal)) * N^(1-2/P.toReal)) := by
  have hP : P ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hP2
  obtain ⟨ha, hb⟩ := interpolation_gaps_pos hq hqp hp2
  let D := (interpolationWeightConstant A B (1/q-1/P.toReal) (1/P.toReal-1/2) *
    (3 : ℝ)^(2/P.toReal)) * N^(1-2/P.toReal)
  have hD : 0 ≤ D := mul_nonneg
    (mul_nonneg (interpolationWeightConstant_nonneg hA hB ha hb) (by positivity))
    (Real.rpow_nonneg hN.le _)
  have h2bound := h2
  obtain ⟨T, hT, _⟩ := h2
  let U := lpL2Lift T hP2 h2Q hQ
  have hfinite (F : Finset ℤ) (f : ℤ → ℂ) :
      ‖U (finiteInputLp F f P)‖ ≤ D * ‖finiteInputLp F f P‖ := by
    apply lp_norm_le_of_finite_pairing hp1 hp2.le hconj
      (mul_nonneg hD (norm_nonneg _)) (U (finiteInputLp F f P))
    intro G g
    have he : (∑ x ∈ G, U (finiteInputLp F f P) x * star (g x)) =
        finiteKernelPairing K F G f g := by
      apply sum_congr rfl
      intro x _
      rw [show U (finiteInputLp F f P) x = finiteConvolution K F f x from
        lpL2Lift_finiteInput T hT hP2 h2Q hQ F f x]
    rw [he]
    exact restricted_l2_finite_bilinear_improving hP2 hN hq hqp hp2 hA hB hK h2bound
      hrestricted F G f g
  refine ⟨U, ?_, lp_opNorm_bound_of_finiteInputs hD hP U hfinite⟩
  intro F x
  change indicatorConvolution K F x = lpL2Lift T hP2 h2Q hQ (finiteIndicatorLp F P) x
  rw [lpL2Lift_apply, lpInclusion_finiteIndicator]
  exact hT F x

theorem kernelLp_pair_bound {P Q : ENNReal} [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    {KA KB : ℤ → ℂ} {CA CB : ℝ}
    (hA : KernelLpBound KA P Q CA) (hB : KernelLpBound KB P Q CB) :
    ∃ TA TB : lp (fun _ : ℤ => ℂ) P →L[ℂ] lp (fun _ : ℤ => ℂ) Q,
      (∀ F : Finset ℤ, ∀ x, indicatorConvolution KA F x = TA (finiteIndicatorLp F P) x) ∧
      (∀ F : Finset ℤ, ∀ x, indicatorConvolution KB F x = TB (finiteIndicatorLp F P) x) ∧
      ∀ f, ‖TA f‖ + ‖TB f‖ ≤ (CA + CB) * ‖f‖ := by
  obtain ⟨TA, heA, hnA⟩ := hA
  obtain ⟨TB, heB, hnB⟩ := hB
  refine ⟨TA, TB, heA, heB, ?_⟩
  intro f
  have ha := (TA.le_opNorm f).trans (mul_le_mul_of_nonneg_right hnA (norm_nonneg f))
  have hb := (TB.le_opNorm f).trans (mul_le_mul_of_nonneg_right hnB (norm_nonneg f))
  exact (add_le_add ha hb).trans_eq (by ring)

end PrimeSquares
