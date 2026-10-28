import PrimeSquares.RestrictedL2

/-!
# Contractive inclusions between counting-space lp spaces

For finite exponents 1 <= P <= Q, the canonical inclusion is continuous
complex-linear and has norm at most one. These are genuine lp spaces;
the underlying sequence is unchanged. No interpolation result is assumed.
-/

open Finset
open scoped lp

namespace PrimeSquares

variable {α : Type*} {P Q : ENNReal}

theorem lp_inclusion_norm [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    (hPQ : P ≤ Q) (hQ : Q ≠ ⊤) (f : lp (fun _ : α => ℂ) P) :
    ‖lp.linearMapOfLE ℂ (fun _ : α => ℂ) hPQ f‖ ≤ ‖f‖ := by
  have hP : P ≠ ⊤ := ne_top_of_le_ne_top hQ hPQ
  have hP0 : P ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ P)).ne'
  have hQ0 : Q ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ Q)).ne'
  have hp : 0 < P.toReal := ENNReal.toReal_pos hP0 hP
  have hq : 0 < Q.toReal := ENNReal.toReal_pos hQ0 hQ
  have hpq : P.toReal ≤ Q.toReal := ENNReal.toReal_mono hQ hPQ
  apply lp.norm_le_of_forall_sum_le hq (norm_nonneg f)
  intro S
  change ∑ i ∈ S, ‖f i‖ ^ Q.toReal ≤ ‖f‖ ^ Q.toReal
  have hexp : Q.toReal - P.toReal + P.toReal ≠ 0 := by linarith
  calc
    _ = ∑ i ∈ S, ‖f i‖ ^ (Q.toReal - P.toReal) * ‖f i‖ ^ P.toReal := by
      apply sum_congr rfl
      intro i _
      rw [← Real.rpow_add' (norm_nonneg _) hexp, sub_add_cancel]
    _ ≤ ∑ i ∈ S, ‖f‖ ^ (Q.toReal - P.toReal) * ‖f i‖ ^ P.toReal := by
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (norm_nonneg _) (lp.norm_apply_le_norm hP0 f i)
          (sub_nonneg.mpr hpq)) (Real.rpow_nonneg (norm_nonneg _) _)
    _ = ‖f‖ ^ (Q.toReal - P.toReal) * ∑ i ∈ S, ‖f i‖ ^ P.toReal :=
      (mul_sum S _ _).symm
    _ ≤ ‖f‖ ^ (Q.toReal - P.toReal) * ‖f‖ ^ P.toReal :=
      mul_le_mul_of_nonneg_left (lp.sum_rpow_le_norm_rpow hp f S)
        (Real.rpow_nonneg (norm_nonneg _) _)
    _ = _ := by rw [← Real.rpow_add' (norm_nonneg _) hexp, sub_add_cancel]

noncomputable def lpInclusion [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    (hPQ : P ≤ Q) (hQ : Q ≠ ⊤) :
    lp (fun _ : α => ℂ) P →L[ℂ] lp (fun _ : α => ℂ) Q :=
  (lp.linearMapOfLE ℂ (fun _ : α => ℂ) hPQ).mkContinuous 1
    (fun f => by simpa only [one_mul] using lp_inclusion_norm hPQ hQ f)

theorem lpInclusion_apply [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    (hPQ : P ≤ Q) (hQ : Q ≠ ⊤) (f : lp (fun _ : α => ℂ) P) (i : α) :
    lpInclusion hPQ hQ f i = f i := rfl

theorem lpInclusion_norm_le [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    (hPQ : P ≤ Q) (hQ : Q ≠ ⊤) :
    ‖lpInclusion (α := α) hPQ hQ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem lpInclusion_contracts [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    (hPQ : P ≤ Q) (hQ : Q ≠ ⊤) (f : lp (fun _ : α => ℂ) P) :
    ‖lpInclusion hPQ hQ f‖ ≤ ‖f‖ := lp_inclusion_norm hPQ hQ f

theorem lpInclusion_finiteIndicator [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    (hPQ : P ≤ Q) (hQ : Q ≠ ⊤) (F : Finset ℤ) :
    lpInclusion hPQ hQ (finiteIndicatorLp F P) = finiteIndicatorLp F Q := by
  apply lp.ext
  rfl

end PrimeSquares
