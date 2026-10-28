import PrimeSquares.FiniteMagnitudeBlocks
import PrimeSquares.InterpolationBlockBounds

/-!
# Strong bilinear estimate for arbitrary finite complex inputs

The rank blocks and coefficient mass are constructed and proved, then
inserted into the actual complex block-family estimate. No partition or
mass bound is a hypothesis. Finite-output norm duality and the final
strong operator corollary are proved in the subsequent modules.
-/

open Finset
open scoped lp

namespace PrimeSquares

theorem finiteKernelPairing_magnitudeBlocks (K : ℤ → ℂ) (F G : Finset ℤ) (f g : ℤ → ℂ) :
    finiteKernelPairing K F G f g =
      ∑ i ∈ range (F.card+1), ∑ j ∈ range (G.card+1),
        finiteKernelPairing K (magnitudeBlock F f i) (magnitudeBlock G g j) f g := by
  symm
  unfold finiteKernelPairing finiteConvolution
  simp_rw [sum_mul]
  rw [sum_comm]
  calc
    _ = ∑ j ∈ range (G.card+1), ∑ x ∈ magnitudeBlock G g j,
        ∑ i ∈ range (F.card+1), ∑ y ∈ magnitudeBlock F f i, K (x-y) * f y * star (g x) := by
      apply sum_congr rfl
      intro j _
      rw [sum_comm]
    _ = ∑ j ∈ range (G.card+1), ∑ x ∈ magnitudeBlock G g j,
        ∑ y ∈ F, K (x-y) * f y * star (g x) := by
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro x _
      exact magnitudeBlock_sum F f (fun y => K (x-y) * f y * star (g x))
    _ = _ := magnitudeBlock_sum G g (fun x => ∑ y ∈ F, K (x-y) * f y * star (g x))

theorem magnitudeBlock_coefficient_lp_norm {P : ENNReal} [Fact (1 ≤ P)]
    (hp : 0 < P.toReal) (F : Finset ℤ) (f : ℤ → ℂ) :
    (∑ j ∈ range (F.card+1),
      |interpolationBlockCoefficient P.toReal j (magnitudeAmplitude F f j)|^P.toReal)^(1/P.toReal) ≤
      (3 : ℝ)^(1/P.toReal) * ‖finiteInputLp F f P‖ := by
  have hcoeff (j : ℕ) : 0 ≤ interpolationBlockCoefficient P.toReal j (magnitudeAmplitude F f j) := by
    unfold interpolationBlockCoefficient
    exact mul_nonneg (by positivity) (magnitudeAmplitude_nonneg F f j)
  have hmass : (∑ j ∈ range (F.card+1),
      |interpolationBlockCoefficient P.toReal j (magnitudeAmplitude F f j)|^P.toReal) ≤
      3 * ‖finiteInputLp F f P‖^P.toReal := by
    simp_rw [abs_of_nonneg (hcoeff _)]
    rw [finiteInputLp_norm_rpow F f P hp]
    exact magnitudeBlock_coefficient_mass F f hp
  have hnorm : (‖finiteInputLp F f P‖^P.toReal)^(1/P.toReal) = ‖finiteInputLp F f P‖ := by
    simpa only [one_div] using Real.rpow_rpow_inv (norm_nonneg (finiteInputLp F f P)) hp.ne'
  calc
    _ ≤ (3 * ‖finiteInputLp F f P‖^P.toReal)^(1/P.toReal) :=
      Real.rpow_le_rpow (sum_nonneg fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
        hmass (one_div_nonneg.mpr hp.le)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by positivity), hnorm]

/-- Full finite-complex bilinear improving bound from the actual restricted
q estimate, kernel positivity and genuine l2 operator input. The constant
contains no N, support size, partition, or desired coefficient estimate. -/
theorem restricted_l2_finite_bilinear_improving {P : ENNReal} [Fact (1 ≤ P)] (hP2 : P ≤ 2)
    {K : ℤ → ℂ} {N q A B : ℝ} (hN : 0 < N) (hq : 0 < q)
    (hqp : q < P.toReal) (hp2 : P.toReal < 2) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hK : NonnegativeKernel K) (h2 : KernelL2Bound K B)
    (hrestricted : ∀ F G : Finset ℤ, ‖restrictedKernelPairing K F G‖ ≤
      A * N^(1-2/q) * (F.card : ℝ)^(1/q) * (G.card : ℝ)^(1/q))
    (F G : Finset ℤ) (f g : ℤ → ℂ) :
    ‖finiteKernelPairing K F G f g‖ ≤
      (interpolationWeightConstant A B (1/q-1/P.toReal) (1/P.toReal-1/2) * (3 : ℝ)^(2/P.toReal)) *
        N^(1-2/P.toReal) * ‖finiteInputLp F f P‖ * ‖finiteInputLp G g P‖ := by
  have hp : 0 < P.toReal := hq.trans hqp
  obtain ⟨ha,hb⟩ := interpolation_gaps_pos hq hqp hp2
  have hC := interpolationWeightConstant_nonneg hA hB ha hb
  have hpref : 0 ≤ N^(1-2/P.toReal) *
      interpolationWeightConstant A B (1/q-1/P.toReal) (1/P.toReal-1/2) :=
    mul_nonneg (Real.rpow_nonneg hN.le _) hC
  have hblock := finite_complex_block_family_bound hP2 hN hq hqp hp2 hA hB hK h2 hrestricted
    (range (F.card+1)) (range (G.card+1)) (magnitudeBlock F f) (magnitudeBlock G g)
    (fun _ => f) (fun _ => g) (magnitudeAmplitude F f) (magnitudeAmplitude G g)
    (fun i _ => magnitudeAmplitude_nonneg F f i) (fun j _ => magnitudeAmplitude_nonneg G g j)
    (fun i _ => by exact_mod_cast magnitudeBlock_card_le F f i)
    (fun j _ => by exact_mod_cast magnitudeBlock_card_le G g j)
    (fun i _ => magnitudeBlock_norm_le F f i) (fun j _ => magnitudeBlock_norm_le G g j)
  rw [← finiteKernelPairing_magnitudeBlocks] at hblock
  have hF := magnitudeBlock_coefficient_lp_norm hp F f
  have hG := magnitudeBlock_coefficient_lp_norm hp G g
  have hthree : (3 : ℝ)^(1/P.toReal) * (3 : ℝ)^(1/P.toReal) = (3 : ℝ)^(2/P.toReal) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  calc
    _ ≤ _ := hblock
    _ ≤ (N^(1-2/P.toReal) * interpolationWeightConstant A B (1/q-1/P.toReal) (1/P.toReal-1/2)) *
        ((3 : ℝ)^(1/P.toReal) * ‖finiteInputLp F f P‖) *
        (∑ j ∈ range (G.card+1),
          |interpolationBlockCoefficient P.toReal j (magnitudeAmplitude G g j)|^P.toReal)^(1/P.toReal) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF hpref)
        (Real.rpow_nonneg (sum_nonneg fun j _ => Real.rpow_nonneg (abs_nonneg _) _) _)
    _ ≤ (N^(1-2/P.toReal) * interpolationWeightConstant A B (1/q-1/P.toReal) (1/P.toReal-1/2)) *
        ((3 : ℝ)^(1/P.toReal) * ‖finiteInputLp F f P‖) *
        ((3 : ℝ)^(1/P.toReal) * ‖finiteInputLp G g P‖) :=
      mul_le_mul_of_nonneg_left hG (mul_nonneg hpref (mul_nonneg (by positivity) (norm_nonneg _)))
    _ = (interpolationWeightConstant A B (1/q-1/P.toReal) (1/P.toReal-1/2) *
        ((3 : ℝ)^(1/P.toReal) * (3 : ℝ)^(1/P.toReal))) *
        N^(1-2/P.toReal) * ‖finiteInputLp F f P‖ * ‖finiteInputLp G g P‖ := by ring
    _ = _ := by rw [hthree]

end PrimeSquares
