import PrimeSquares.IWSamplingSpaces
import PrimeSquares.CompactCircleInverseKernel
import PrimeSquares.FourierKernelAlgebra
import PrimeSquares.SquareResidueGrouping
import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false
open MeasureTheory Finset
open scoped FourierTransform lp
namespace PrimeSquares

noncomputable def circleSymbolTranslate (m : C(PrimeCircle, ℂ)) (α : PrimeCircle) :
    C(PrimeCircle, ℂ) :=
  m.comp ⟨fun ξ => ξ-α, continuous_id.sub continuous_const⟩

theorem fourierKernel_translate (m : C(PrimeCircle, ℂ)) (α : PrimeCircle) (n : ℤ) :
    fourierKernel (circleSymbolTranslate m α) n =
      negativeFourierCharacter (-n) α * fourierKernel m n := by
  rw [fourierKernel_coefficient, fourierKernel_coefficient]
  change (∫ ξ : PrimeCircle, negativeFourierCharacter (-n) ξ * m (ξ-α) ∂AddCircle.haarAddCircle) = _
  rw [←integral_add_right_eq_self
    (fun ξ : PrimeCircle => negativeFourierCharacter (-n) ξ * m (ξ-α)) α]
  simp only [add_sub_cancel_right, negativeFourierCharacter_add_argument]
  change (∫ ξ : PrimeCircle, negativeFourierCharacter (-n) ξ * negativeFourierCharacter (-n) α * m ξ ∂AddCircle.haarAddCircle) =
    negativeFourierCharacter (-n) α * (∫ ξ : PrimeCircle, negativeFourierCharacter (-n) ξ * m ξ ∂AddCircle.haarAddCircle)
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ => by ring)

theorem fourierKernel_finsetSum {ι : Type*} (I : Finset ι)
    (m : ι → C(PrimeCircle, ℂ)) (n : ℤ) :
    fourierKernel (∑ i ∈ I, m i) n = ∑ i ∈ I, fourierKernel (m i) n := by
  unfold fourierKernel fourierKernelSequence
  rw [map_sum, map_sum, lp.coeFn_sum, Finset.sum_apply]

theorem iwCyclicSymbol_kernel (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (ν : ZMod P → ℂ) (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ x : ℝ, 1 ≤ |x| → m x = 0)
    (hn : ∀ x : ℝ, 1/2 ≤ |x| → m x = 0) (n : ℤ) :
    fourierKernel (iwCyclicSymbol S k P ν m hs) n =
      ∑ α ∈ iwFrequencySet S k, cyclicRationalCoefficient P ν α *
        negativeFourierCharacter (-n) ((α : ℝ) : PrimeCircle) * 𝓕⁻ (m : ℝ → ℂ) (n : ℝ) := by
  rw [iwCyclicSymbol, fourierKernel_finsetSum]
  apply Finset.sum_congr rfl
  intro α _
  rw [fourierKernel_smul]
  change _ * fourierKernel (circleSymbolTranslate (compactCircleLift m.toContinuousMap hs)
    ((α : ℝ) : PrimeCircle)) n = _
  rw [fourierKernel_translate, compactCircleLift_inverse_kernel m.toContinuousMap hs hn]
  change _ * (_ * 𝓕⁻ (m : ℝ → ℂ) (n : ℝ)) = _
  ring

theorem integerMultiplier_finite_symbol_product (m : C(PrimeCircle, ℂ))
    (F : Finset ℤ) (f : ℤ → ℂ) (n : ℤ) :
    integerMultiplier m (finiteInputLp F f 2) n =
      fourierKernel (m * finiteFourierPolynomial F f) n := by
  rw [integerMultiplier_apply, integerFourier_finiteInput, circleMultiply_toLp]
  rfl

theorem compactCircleLift_mul_circle (m h : C(ℝ, ℂ))
    (hm : ∀ x : ℝ, 1 ≤ |x| → m x = 0) (hh : ∀ x : ℝ, 1 ≤ |x| → h x = 0)
    (g : C(PrimeCircle, ℂ)) (α : PrimeCircle)
    (he : ∀ x : ℝ, h x = m x * g (α + (x : PrimeCircle))) :
    compactCircleLift h hh = compactCircleLift m hm *
      g.comp ⟨fun ξ => α+ξ, continuous_const.add continuous_id⟩ := by
  ext ξ
  refine QuotientAddGroup.induction_on ξ (fun x => ?_)
  change compactCircleLift h hh (x : PrimeCircle) =
    compactCircleLift m hm (x : PrimeCircle) * g (α+(x : PrimeCircle))
  rw [compactCircleLift_all_real, compactCircleLift_all_real, ←tsum_mul_right]
  apply tsum_congr
  intro j
  rw [he]
  congr 2
  rw [AddCircle.coe_add]
  have hz : (((j : ℝ)) : PrimeCircle) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨j, by simp⟩
  rw [hz, add_zero]

end PrimeSquares
