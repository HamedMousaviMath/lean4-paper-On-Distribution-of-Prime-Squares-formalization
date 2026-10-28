import PrimeSquares.IntegerReflection
import PrimeSquares.OrliczPairing

/-!
# Reflection transfers convolution estimates with the same constants

Both finite input sets and output sets are reflected. The two- and three-piece
operator predicates are equivalent for `K` and `K(-·)`. This requires no
linearity of the decomposition maps. Continuous linear realizations are
conjugated by the actual `lp` isometries, preserving their operator norms.
-/

open Finset
open scoped lp

namespace PrimeSquares

noncomputable def reflectLpMap {p q : ENNReal}
    (T : ℓ^p(ℤ, ℂ) → ℓ^q(ℤ, ℂ)) : ℓ^p(ℤ, ℂ) → ℓ^q(ℤ, ℂ) :=
  fun f => reflectLp (T (reflectLp f))

@[simp]
theorem reflectLpMap_apply {p q : ENNReal}
    (T : ℓ^p(ℤ, ℂ) → ℓ^q(ℤ, ℂ)) (f : ℓ^p(ℤ, ℂ)) (x : ℤ) :
    reflectLpMap T f x = T (reflectLp f) (-x) := rfl

@[simp]
theorem reflectLpMap_involutive {p q : ENNReal}
    (T : ℓ^p(ℤ, ℂ) → ℓ^q(ℤ, ℂ)) : reflectLpMap (reflectLpMap T) = T := by
  funext f
  simp [reflectLpMap]

@[simp]
theorem reflectLpMap_norm {p q : ENNReal} [Fact (1 ≤ q)]
    (T : ℓ^p(ℤ, ℂ) → ℓ^q(ℤ, ℂ)) (f : ℓ^p(ℤ, ℂ)) :
    ‖reflectLpMap T f‖ = ‖T (reflectLp f)‖ := reflectLp_norm _

theorem reflectLpMap_bound_iff {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (T : ℓ^p(ℤ, ℂ) → ℓ^q(ℤ, ℂ)) (A : ℝ) :
    (∀ f, ‖reflectLpMap T f‖ ≤ A * ‖f‖) ↔ (∀ f, ‖T f‖ ≤ A * ‖f‖) := by
  constructor
  · intro h f
    simpa only [reflectLpMap_norm, reflectLp_involutive, reflectLp_norm] using h (reflectLp f)
  · intro h f
    simpa only [reflectLpMap_norm, reflectLp_norm] using h (reflectLp f)

noncomputable def reflectContinuousLinearMap {p q : ENNReal}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (T : ℓ^p(ℤ, ℂ) →L[ℂ] ℓ^q(ℤ, ℂ)) :
    ℓ^p(ℤ, ℂ) →L[ℂ] ℓ^q(ℤ, ℂ) :=
  (integerReflection (𝕜 := ℂ) q).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp (integerReflection (𝕜 := ℂ) p).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem reflectContinuousLinearMap_apply {p q : ENNReal}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (T : ℓ^p(ℤ, ℂ) →L[ℂ] ℓ^q(ℤ, ℂ))
    (f : ℓ^p(ℤ, ℂ)) (x : ℤ) :
    reflectContinuousLinearMap T f x = T (reflectLp f) (-x) := rfl

theorem reflectContinuousLinearMap_eq {p q : ENNReal}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (T : ℓ^p(ℤ, ℂ) →L[ℂ] ℓ^q(ℤ, ℂ)) :
    (reflectContinuousLinearMap T : ℓ^p(ℤ, ℂ) → ℓ^q(ℤ, ℂ)) = reflectLpMap T := rfl

@[simp]
theorem reflectContinuousLinearMap_involutive {p q : ENNReal}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (T : ℓ^p(ℤ, ℂ) →L[ℂ] ℓ^q(ℤ, ℂ)) :
    reflectContinuousLinearMap (reflectContinuousLinearMap T) = T := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  simp

theorem reflectContinuousLinearMap_norm_le {p q : ENNReal}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (T : ℓ^p(ℤ, ℂ) →L[ℂ] ℓ^q(ℤ, ℂ)) :
    ‖reflectContinuousLinearMap T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro f
  change ‖reflectLp (T (reflectLp f))‖ ≤ _
  simpa only [reflectLp_norm] using T.le_opNorm (reflectLp f)

@[simp]
theorem reflectContinuousLinearMap_norm {p q : ENNReal}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (T : ℓ^p(ℤ, ℂ) →L[ℂ] ℓ^q(ℤ, ℂ)) :
    ‖reflectContinuousLinearMap T‖ = ‖T‖ := by
  apply le_antisymm (reflectContinuousLinearMap_norm_le T)
  simpa only [reflectContinuousLinearMap_involutive] using
    reflectContinuousLinearMap_norm_le (reflectContinuousLinearMap T)

theorem finiteConvolution_reflect (K : ℤ → ℂ) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    finiteConvolution (reflectSequence K) F f x =
      finiteConvolution K (reflectedFinset F) (reflectSequence f) (-x) := by
  simp only [finiteConvolution, reflectedFinset, sum_image neg_injective.injOn,
    reflectSequence_apply, neg_neg]
  apply sum_congr rfl
  intro y _
  congr 2; ring

theorem indicatorConvolution_reflect (K : ℤ → ℂ) (F : Finset ℤ) (x : ℤ) :
    indicatorConvolution (reflectSequence K) F x =
      indicatorConvolution K (reflectedFinset F) (-x) := by
  have h := finiteConvolution_reflect K F (fun _ => 1) x
  change finiteConvolution (reflectSequence K) F (fun _ => 1) x =
    finiteConvolution K (reflectedFinset F) (fun _ => 1) (-x) at h
  simpa only [finiteConvolution_indicator] using h

theorem finiteKernelPairing_reflect (K : ℤ → ℂ) (F G : Finset ℤ) (f g : ℤ → ℂ) :
    finiteKernelPairing (reflectSequence K) F G f g =
      finiteKernelPairing K (reflectedFinset F) (reflectedFinset G)
        (reflectSequence f) (reflectSequence g) := by
  simp only [finiteKernelPairing, reflectedFinset, sum_image neg_injective.injOn,
    reflectSequence_apply, neg_neg]
  apply sum_congr rfl
  intro x _
  rw [finiteConvolution_reflect]
  rfl

theorem restrictedKernelPairing_reflect (K : ℤ → ℂ) (F G : Finset ℤ) :
    restrictedKernelPairing (reflectSequence K) F G =
      restrictedKernelPairing K (reflectedFinset F) (reflectedFinset G) := by
  have h := finiteKernelPairing_reflect K F G (fun _ => 1) (fun _ => 1)
  change finiteKernelPairing (reflectSequence K) F G (fun _ => 1) (fun _ => 1) =
    finiteKernelPairing K (reflectedFinset F) (reflectedFinset G)
      (fun _ => 1) (fun _ => 1) at h
  simpa only [finiteKernelPairing_indicators] using h

theorem operatorHighLowBound_reflect {K : ℤ → ℂ} {N J s r γ β C : ℝ}
    (h : OperatorHighLowBound K N J s r γ β C) :
    OperatorHighLowBound (reflectSequence K) N J s r γ β C := by
  obtain ⟨Lo, Hi, heq, hlo, hhi⟩ := h
  refine ⟨reflectLpMap Lo, reflectLpMap Hi, ?_, ?_, ?_⟩
  · intro F x
    simpa only [indicatorConvolution_reflect, reflectLpMap_apply,
      reflectLp_finiteIndicator] using heq (reflectedFinset F) (-x)
  · exact (reflectLpMap_bound_iff Lo _).2 hlo
  · exact (reflectLpMap_bound_iff Hi _).2 hhi

theorem operatorHighLowBound_reflect_iff (K : ℤ → ℂ) (N J s r γ β C : ℝ) :
    OperatorHighLowBound (reflectSequence K) N J s r γ β C ↔
      OperatorHighLowBound K N J s r γ β C := by
  constructor
  · intro h
    simpa only [reflectSequence_involutive] using operatorHighLowBound_reflect h
  · exact operatorHighLowBound_reflect

theorem operatorOrliczBound_reflect {K : ℤ → ℂ}
    {N Q s r α c₁ κ M A CLo CHi CErr : ℝ}
    (h : OperatorOrliczBound K N Q s r α c₁ κ M A CLo CHi CErr) :
    OperatorOrliczBound (reflectSequence K) N Q s r α c₁ κ M A CLo CHi CErr := by
  obtain ⟨Lo, Hi, Err, heq, hlo, hhi, herr⟩ := h
  refine ⟨reflectLpMap Lo, reflectLpMap Hi, reflectLpMap Err, ?_, ?_, ?_, ?_⟩
  · intro F x
    simpa only [indicatorConvolution_reflect, reflectLpMap_apply,
      reflectLp_finiteIndicator] using heq (reflectedFinset F) (-x)
  · exact (reflectLpMap_bound_iff Lo _).2 hlo
  · exact (reflectLpMap_bound_iff Hi _).2 hhi
  · exact (reflectLpMap_bound_iff Err _).2 herr

theorem operatorOrliczBound_reflect_iff (K : ℤ → ℂ)
    (N Q s r α c₁ κ M A CLo CHi CErr : ℝ) :
    OperatorOrliczBound (reflectSequence K) N Q s r α c₁ κ M A CLo CHi CErr ↔
      OperatorOrliczBound K N Q s r α c₁ κ M A CLo CHi CErr := by
  constructor
  · intro h
    simpa only [reflectSequence_involutive] using operatorOrliczBound_reflect h
  · exact operatorOrliczBound_reflect

theorem kernelL2Bound_reflect {K : ℤ → ℂ} {C : ℝ} (h : KernelL2Bound K C) :
    KernelL2Bound (reflectSequence K) C := by
  obtain ⟨T, heq, hT⟩ := h
  refine ⟨reflectContinuousLinearMap T, ?_, ?_⟩
  · intro F x
    simpa only [indicatorConvolution_reflect, reflectContinuousLinearMap_apply,
      reflectLp_finiteIndicator] using heq (reflectedFinset F) (-x)
  · simpa only [reflectContinuousLinearMap_norm] using hT

theorem kernelL2Bound_reflect_iff (K : ℤ → ℂ) (C : ℝ) :
    KernelL2Bound (reflectSequence K) C ↔ KernelL2Bound K C := by
  constructor
  · intro h
    simpa only [reflectSequence_involutive] using kernelL2Bound_reflect h
  · exact kernelL2Bound_reflect

end PrimeSquares
