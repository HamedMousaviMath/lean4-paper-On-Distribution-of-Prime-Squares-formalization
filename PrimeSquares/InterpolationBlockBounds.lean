import PrimeSquares.InterpolationGeometry
import PrimeSquares.FiniteComplexInputs

/-!
# Exact scale algebra and complex bounds on individual dyadic blocks

The estimates apply to actual finite convolutions on any supports with the
stated dyadic cardinality bounds. Constructing the rank partition of a
general finite input, and summing its coefficient mass, remain separate
obligations. No such partition is assumed in a completed paper theorem.
-/

open Finset

namespace PrimeSquares

noncomputable def interpolationBlockCoefficient (p : ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  ((2 : ℝ)^i)^(1/p) * u

theorem interpolation_scale_balance {N f g : ℝ} (hN : 0 < N) (hf : 0 < f) (hg : 0 < g)
    (x y : ℝ) :
    N^(1-2*x) * f^x * g^x =
      N^(1-2*y) * f^y * g^y * (f*g/N^2)^(x-y) := by
  rw [Real.div_rpow (mul_nonneg hf.le hg.le) (sq_nonneg N),
    Real.mul_rpow hf.le hg.le, ← Real.rpow_natCast_mul hN.le]
  norm_num only [Nat.cast_ofNat]
  symm
  calc
    _ = (N^(1-2*y) / N^(2*(x-y))) * (f^y * f^(x-y)) * (g^y * g^(x-y)) := by ring
    _ = N^((1-2*y)-2*(x-y)) * f^(y+(x-y)) * g^(y+(x-y)) := by
      rw [← Real.rpow_sub hN, ← Real.rpow_add hf, ← Real.rpow_add hg]
    _ = _ := by
      rw [show (1-2*y)-2*(x-y) = 1-2*x by ring, show y+(x-y) = x by ring]

theorem dyadic_interpolation_scale_balance {N : ℝ} (hN : 0 < N) (i j : ℕ) (x y : ℝ) :
    N^(1-2*x) * ((2 : ℝ)^i)^x * ((2 : ℝ)^j)^x =
      N^(1-2*y) * ((2 : ℝ)^i)^y * ((2 : ℝ)^j)^y *
        ((2 : ℝ)^(i+j)/N^2)^(x-y) := by
  simpa only [pow_add] using interpolation_scale_balance hN
    (by positivity : (0 : ℝ) < 2^i) (by positivity : (0 : ℝ) < 2^j) x y

theorem interpolation_low_block_identity {N p q A u v : ℝ} (hN : 0 < N) (i j : ℕ) :
    u*v * (A * N^(1-2/q) * ((2 : ℝ)^i)^(1/q) * ((2 : ℝ)^j)^(1/q)) =
      N^(1-2/p) * interpolationBlockCoefficient p i u * interpolationBlockCoefficient p j v *
        (A * ((2 : ℝ)^(i+j)/N^2)^(1/q-1/p)) := by
  have h := dyadic_interpolation_scale_balance hN i j (1/q) (1/p)
  rw [show 2*(1/q) = 2/q by ring, show 2*(1/p) = 2/p by ring] at h
  calc
    _ = (u*v*A) * (N^(1-2/q) * ((2 : ℝ)^i)^(1/q) * ((2 : ℝ)^j)^(1/q)) := by ring
    _ = _ := by rw [h]; unfold interpolationBlockCoefficient; ring

theorem interpolation_two_block_identity {N p B u v : ℝ} (hN : 0 < N) (i j : ℕ) :
    u*v * (B * ((2 : ℝ)^i)^(1/2 : ℝ) * ((2 : ℝ)^j)^(1/2 : ℝ)) =
      N^(1-2/p) * interpolationBlockCoefficient p i u * interpolationBlockCoefficient p j v *
        (B * ((2 : ℝ)^(i+j)/N^2)^(-(1/p-1/2))) := by
  have h := dyadic_interpolation_scale_balance hN i j (1/2) (1/p)
  rw [show (1 : ℝ)-2*(1/2) = 0 by norm_num, Real.rpow_zero, one_mul,
    show 2*(1/p) = 2/p by ring, show (1/2 : ℝ)-1/p = -(1/p-1/2) by ring] at h
  calc
    _ = (u*v*B) * (((2 : ℝ)^i)^(1/2 : ℝ) * ((2 : ℝ)^j)^(1/2 : ℝ)) := by ring
    _ = _ := by rw [h]; unfold interpolationBlockCoefficient; ring

theorem interpolation_block_min_identity {N p q A B u v : ℝ}
    (hN : 0 < N) (hu : 0 ≤ u) (hv : 0 ≤ v) (i j : ℕ) :
    min (u*v * (A * N^(1-2/q) * ((2 : ℝ)^i)^(1/q) * ((2 : ℝ)^j)^(1/q)))
        (u*v * (B * ((2 : ℝ)^i)^(1/2 : ℝ) * ((2 : ℝ)^j)^(1/2 : ℝ))) =
      N^(1-2/p) * interpolationBlockCoefficient p i u * interpolationBlockCoefficient p j v *
        interpolationWeight A B (1/q-1/p) (1/p-1/2) (N^2) (i+j) := by
  rw [interpolation_low_block_identity hN, interpolation_two_block_identity hN]
  unfold interpolationWeight
  exact (mul_min_of_nonneg _ _ (by
    unfold interpolationBlockCoefficient
    positivity)).symm

/-- An actual complex convolution block is bounded by the exact geometric
weight. The l2 input is a genuine continuous operator, not a scalar proxy. -/
theorem finiteKernelPairing_dyadic_block_bound {K : ℤ → ℂ} {N p q A B u v : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hK : NonnegativeKernel K) (h2 : KernelL2Bound K B)
    (F G : Finset ℤ) (i j : ℕ) (f g : ℤ → ℂ)
    (hF : (F.card : ℝ) ≤ (2 : ℝ)^i) (hG : (G.card : ℝ) ≤ (2 : ℝ)^j)
    (hf : ∀ y ∈ F, ‖f y‖ ≤ u) (hg : ∀ x ∈ G, ‖g x‖ ≤ v)
    (hrestricted : ‖restrictedKernelPairing K F G‖ ≤
      A * N^(1-2/q) * (F.card : ℝ)^(1/q) * (G.card : ℝ)^(1/q)) :
    ‖finiteKernelPairing K F G f g‖ ≤
      N^(1-2/p) * interpolationBlockCoefficient p i u * interpolationBlockCoefficient p j v *
        interpolationWeight A B (1/q-1/p) (1/p-1/2) (N^2) (i+j) := by
  have hFq := Real.rpow_le_rpow (Nat.cast_nonneg F.card) hF (one_div_nonneg.mpr hq.le)
  have hGq := Real.rpow_le_rpow (Nat.cast_nonneg G.card) hG (one_div_nonneg.mpr hq.le)
  have hlo : ‖restrictedKernelPairing K F G‖ ≤
      A * N^(1-2/q) * ((2 : ℝ)^i)^(1/q) * ((2 : ℝ)^j)^(1/q) := by
    calc
      _ ≤ _ := hrestricted
      _ ≤ A * N^(1-2/q) * ((2 : ℝ)^i)^(1/q) * (G.card : ℝ)^(1/q) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFq (by positivity)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hGq (by positivity)
  have hFtwo : Real.sqrt (F.card : ℝ) ≤ ((2 : ℝ)^i)^(1/2 : ℝ) :=
    (Real.sqrt_le_sqrt hF).trans_eq (Real.sqrt_eq_rpow _)
  have hGtwo : Real.sqrt (G.card : ℝ) ≤ ((2 : ℝ)^j)^(1/2 : ℝ) :=
    (Real.sqrt_le_sqrt hG).trans_eq (Real.sqrt_eq_rpow _)
  have hhi : ‖restrictedKernelPairing K F G‖ ≤
      B * ((2 : ℝ)^i)^(1/2 : ℝ) * ((2 : ℝ)^j)^(1/2 : ℝ) := by
    calc
      _ ≤ _ := restrictedKernelPairing_l2_bound h2 F G
      _ ≤ B * ((2 : ℝ)^i)^(1/2 : ℝ) * Real.sqrt (G.card : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFtwo hB) (Real.sqrt_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hGtwo (by positivity)
  have hamp := finiteKernelPairing_bound_by_indicators hK F G f g hu hf hg
  rw [← interpolation_block_min_identity hN hu hv i j]
  exact le_min (hamp.trans (mul_le_mul_of_nonneg_left hlo (mul_nonneg hu hv)))
    (hamp.trans (mul_le_mul_of_nonneg_left hhi (mul_nonneg hu hv)))

/-- Sum any specified finite block family with genuine support/amplitude
bounds. Constructing such blocks for an arbitrary input and controlling
their coefficient mass is deliberately not a hypothesis-free conclusion. -/
theorem finite_complex_block_family_bound {P : ENNReal} [Fact (1 ≤ P)] (hP2 : P ≤ 2)
    {K : ℤ → ℂ} {N q A B : ℝ} (hN : 0 < N) (hq : 0 < q)
    (hqp : q < P.toReal) (hp2 : P.toReal < 2) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hK : NonnegativeKernel K) (h2 : KernelL2Bound K B)
    (hrestricted : ∀ F G : Finset ℤ, ‖restrictedKernelPairing K F G‖ ≤
      A * N^(1-2/q) * (F.card : ℝ)^(1/q) * (G.card : ℝ)^(1/q))
    (S T : Finset ℕ) (F G : ℕ → Finset ℤ) (f g : ℕ → ℤ → ℂ) (u v : ℕ → ℝ)
    (hu : ∀ i ∈ S, 0 ≤ u i) (hv : ∀ j ∈ T, 0 ≤ v j)
    (hF : ∀ i ∈ S, ((F i).card : ℝ) ≤ (2 : ℝ)^i)
    (hG : ∀ j ∈ T, ((G j).card : ℝ) ≤ (2 : ℝ)^j)
    (hf : ∀ i ∈ S, ∀ y ∈ F i, ‖f i y‖ ≤ u i)
    (hg : ∀ j ∈ T, ∀ x ∈ G j, ‖g j x‖ ≤ v j) :
    ‖∑ i ∈ S, ∑ j ∈ T, finiteKernelPairing K (F i) (G j) (f i) (g j)‖ ≤
      (N^(1-2/P.toReal) * interpolationWeightConstant A B (1/q-1/P.toReal) (1/P.toReal-1/2)) *
        (∑ i ∈ S, |interpolationBlockCoefficient P.toReal i (u i)|^P.toReal)^(1/P.toReal) *
        (∑ j ∈ T, |interpolationBlockCoefficient P.toReal j (v j)|^P.toReal)^(1/P.toReal) := by
  obtain ⟨ha, hb⟩ := interpolation_gaps_pos hq hqp hp2
  let c : ℕ → ℝ := fun i => interpolationBlockCoefficient P.toReal i (u i)
  let d : ℕ → ℝ := fun j => interpolationBlockCoefficient P.toReal j (v j)
  have hmatrix := interpolationWeight_finite_schur_lp hP2 hA hB ha hb hN S T c d
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ T, ‖finiteKernelPairing K (F i) (G j) (f i) (g j)‖ :=
      (norm_sum_le _ _).trans (sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i ∈ S, ∑ j ∈ T, N^(1-2/P.toReal) * c i * d j *
        interpolationWeight A B (1/q-1/P.toReal) (1/P.toReal-1/2) (N^2) (i+j) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      exact finiteKernelPairing_dyadic_block_bound hN hq hA hB (hu i hi) (hv j hj)
        hK h2 (F i) (G j) i j (f i) (g j) (hF i hi) (hG j hj) (hf i hi) (hg j hj)
        (hrestricted (F i) (G j))
    _ = N^(1-2/P.toReal) * (∑ i ∈ S, ∑ j ∈ T,
        interpolationWeight A B (1/q-1/P.toReal) (1/P.toReal-1/2) (N^2) (i+j) * c i * d j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ N^(1-2/P.toReal) * (interpolationWeightConstant A B (1/q-1/P.toReal) (1/P.toReal-1/2) *
        (∑ i ∈ S, |c i|^P.toReal)^(1/P.toReal) * (∑ j ∈ T, |d j|^P.toReal)^(1/P.toReal)) :=
      mul_le_mul_of_nonneg_left hmatrix (Real.rpow_nonneg hN.le _)
    _ = _ := by ring

end PrimeSquares
