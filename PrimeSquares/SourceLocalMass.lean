import PrimeSquares.DyadicLocalMassBounds
import PrimeSquares.AllInputFourierConvolution

/-!
# The source local average for all l1 inputs

The supremum is over every real radius M >= N, and each spatial ball has
radius M^2. This is the literal source local maximal average with C=1.
Finite dyadic local masses are dominated by this actual all-input quantity.
-/

open Finset
open scoped lp

namespace PrimeSquares

theorem sourceBall_summable (f : ℓ¹(ℤ, ℂ)) (x : ℤ) (M : ℝ) :
    Summable (fun y : ℤ => if |((x-y : ℤ) : ℝ)| ≤ M^2 then ‖f y‖ else 0) := by
  have hf : Summable (fun y : ℤ => ‖f y‖) := by simpa using f.2.summable
  exact hf.of_norm_bounded (fun y => by split_ifs <;> simp)

noncomputable def sourceBallMass (f : ℓ¹(ℤ, ℂ)) (x : ℤ) (M : ℝ) : ℝ :=
  (M^2)⁻¹ * ∑' y : ℤ, if |((x-y : ℤ) : ℝ)| ≤ M^2 then ‖f y‖ else 0

theorem sourceBallMass_nonneg (f : ℓ¹(ℤ, ℂ)) (x : ℤ) (M : ℝ) :
    0 ≤ sourceBallMass f x M := by
  unfold sourceBallMass
  exact mul_nonneg (by positivity) (tsum_nonneg (fun y => by split_ifs <;> positivity))

theorem sourceBallMass_uniform {N : ℕ} (hN : 1 ≤ N) (M : ℝ) (hM : (N : ℝ) ≤ M)
    (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    sourceBallMass f x M ≤ ((N : ℝ)^2)⁻¹ * ‖f‖ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMs : (N : ℝ)^2 ≤ M^2 := (sq_le_sq₀ hNr.le (hNr.le.trans hM)).2 hM
  have hf : Summable (fun y : ℤ => ‖f y‖) := by simpa using f.2.summable
  have ht : (∑' y : ℤ, if |((x-y : ℤ) : ℝ)| ≤ M^2 then ‖f y‖ else 0) ≤ ‖f‖ := by
    calc
      _ ≤ ∑' y : ℤ, ‖f y‖ := Summable.tsum_le_tsum
        (fun y => by split_ifs <;> simp) (sourceBall_summable f x M) hf
      _ = ‖f‖ := by
        rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
        simp
  exact mul_le_mul (inv_anti₀ (sq_pos_of_pos hNr) hMs) ht
    (tsum_nonneg (fun y => by split_ifs <;> positivity)) (by positivity)

noncomputable def sourceLocalMass (N : ℕ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) : ℝ :=
  ⨆ M : Set.Ici (N : ℝ), sourceBallMass f x M

theorem sourceLocalMass_bddAbove {N : ℕ} (hN : 1 ≤ N) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    BddAbove (Set.range (fun M : Set.Ici (N : ℝ) => sourceBallMass f x M)) := by
  refine ⟨((N : ℝ)^2)⁻¹ * ‖f‖, ?_⟩
  rintro _ ⟨M, rfl⟩
  exact sourceBallMass_uniform hN M M.property f x

theorem sourceBallMass_le_local {N : ℕ} (hN : 1 ≤ N) (f : ℓ¹(ℤ, ℂ)) (x : ℤ)
    (M : ℝ) (hM : (N : ℝ) ≤ M) : sourceBallMass f x M ≤ sourceLocalMass N f x :=
  le_ciSup (sourceLocalMass_bddAbove hN f x) ⟨M, hM⟩

theorem sourceLocalMass_nonneg {N : ℕ} (hN : 1 ≤ N) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    0 ≤ sourceLocalMass N f x :=
  (sourceBallMass_nonneg f x N).trans (sourceBallMass_le_local hN f x N le_rfl)

theorem sourceLocalMass_uniform {N : ℕ} (hN : 1 ≤ N) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    sourceLocalMass N f x ≤ ((N : ℝ)^2)⁻¹ * ‖f‖ :=
  ciSup_le (fun M => sourceBallMass_uniform hN M M.property f x)

theorem finiteDyadicLocalMass_le_source {N : ℕ} (hN : 1 ≤ N)
    (F : Finset ℤ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    dyadicLocalMass ((N : ℝ)^2) F (fun y => ‖f y‖) x ≤ sourceLocalMass N f x := by
  apply ciSup_le
  intro j
  let M : ℝ := Real.sqrt ((2 : ℝ)^j * (N : ℝ)^2)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hM : (N : ℝ) ≤ M := by
    calc
      (N : ℝ) = Real.sqrt ((N : ℝ)^2) := (Real.sqrt_sq hN0).symm
      _ ≤ M := Real.sqrt_le_sqrt (le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (by norm_num)))
  have hMs : M^2 = (2 : ℝ)^j * (N : ℝ)^2 := Real.sq_sqrt (by positivity)
  have hb : dyadicBallMass ((N : ℝ)^2) F (fun y => ‖f y‖) x j ≤ sourceBallMass f x M := by
    have hs := sourceBall_summable f x M
    rw [hMs] at hs
    unfold dyadicBallMass sourceBallMass
    rw [hMs, sum_filter]
    exact mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum F (fun y _ => by split_ifs <;> positivity) hs) (by positivity)
  exact hb.trans (sourceBallMass_le_local hN f x M hM)

theorem fourierL1Operator_local_of_finite (m : C(PrimeCircle, ℂ)) {N : ℕ} (hN : 1 ≤ N)
    {A : ℝ} (hA : 0 ≤ A)
    (hfinite : ∀ (F : Finset ℤ) (u : ℤ → ℂ) (x : ℤ),
      ‖integerMultiplier m (finiteInputLp F u 2) x‖ ≤
        A * dyadicLocalMass ((N : ℝ)^2) F (fun y => ‖u y‖) x)
    (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    ‖fourierL1Operator m f x‖ ≤ A * sourceLocalMass N f x := by
  have hK : ∀ z, ‖fourierKernel m z‖ ≤ ‖m‖ :=
    fourierKernel_uniform_bound m (fun θ => m.norm_coe_le_norm θ)
  have hs : HasSum (fun y : ℤ => fourierKernel m (x-y) * f y) (fourierL1Operator m f x) :=
    (kernelL1_summable (fourierKernel m) hK f x).hasSum
  have hb : ∀ F : Finset ℤ,
      ‖∑ y ∈ F, fourierKernel m (x-y) * f y‖ ≤ A * sourceLocalMass N f x := by
    intro F
    have he : (∑ y ∈ F, fourierKernel m (x-y) * f y) =
        fourierL1Operator m (finiteInputLp F f 1) x :=
      (kernelL1Operator_finite (fourierKernel m) hK F f x).symm
    rw [he, fourierL1Operator_l2_agreement]
    exact (hfinite F f x).trans (mul_le_mul_of_nonneg_left
      (finiteDyadicLocalMass_le_source hN F f x) hA)
  exact le_of_tendsto ((continuous_norm.tendsto _).comp hs) (Filter.Eventually.of_forall hb)

end PrimeSquares
