import PrimeSquares.FiniteSmoothFourierLift
import PrimeSquares.CyclicRealLpBounds

set_option autoImplicit false
open MeasureTheory Finset
open scoped FourierTransform ContDiff lp
namespace PrimeSquares

theorem rationalCharacter_eq_of_cyclic_cast (P : ℕ) [NeZero P]
    (α : ℚ) (hα : α.den ∣ P) (n m : ℤ) (hnm : (n : ZMod P) = (m : ZMod P)) :
    negativeFourierCharacter n ((α : ℝ) : PrimeCircle) =
      negativeFourierCharacter m ((α : ℝ) : PrimeCircle) := by
  let : NeZero α.den := ⟨α.den_pos.ne'⟩
  have hcast : (n : ZMod α.den) = (m : ZMod α.den) := by
    have h := congrArg (ZMod.castHom hα (ZMod α.den)) hnm
    simpa only [map_intCast] using h
  rw [Rat.cast_def, negativeFourierCharacter_rational, negativeFourierCharacter_rational]
  congr 1
  push_cast
  rw [hcast]

theorem cyclicLiftCharacter_integer (P : ℕ) [NeZero P]
    (α : ℚ) (hα : α.den ∣ P) (n : ℤ) :
    negativeFourierCharacter (-((n : ZMod P).val : ℤ)) ((α : ℝ) : PrimeCircle) =
      negativeFourierCharacter (-n) ((α : ℝ) : PrimeCircle) := by
  apply rationalCharacter_eq_of_cyclic_cast P α hα
  simp only [Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem cyclicLiftCharacter_sub (P : ℕ) [NeZero P]
    (α : ℚ) (hα : α.den ∣ P) (y z : ZMod P) :
    negativeFourierCharacter (-((y-z).val : ℤ)) ((α : ℝ) : PrimeCircle) =
      negativeFourierCharacter (-(y.val : ℤ)) ((α : ℝ) : PrimeCircle) *
        negativeFourierCharacter (z.val : ℤ) ((α : ℝ) : PrimeCircle) := by
  have he : negativeFourierCharacter (-((y-z).val : ℤ)) ((α : ℝ) : PrimeCircle) =
      negativeFourierCharacter (-(y.val : ℤ)+(z.val : ℤ)) ((α : ℝ) : PrimeCircle) := by
    apply rationalCharacter_eq_of_cyclic_cast P α hα
    push_cast
    simp only [ZMod.natCast_zmod_val]
    ring
  rw [he, negativeFourierCharacter_add]

theorem cyclicSynthesis_convolution (Γ : Finset ℚ) (P : ℕ) [NeZero P]
    (hΓ : ∀ α ∈ Γ, α.den ∣ P) (ν : ZMod P → ℂ)
    (u : ℚ → SchwartzMap ℝ ℂ) (y : ZMod P) (x : ℝ) :
    cyclicConvolutionSchwartz P ν (cyclicSynthesisSchwartz Γ P u) y x =
      ∑ α ∈ Γ, cyclicRationalCoefficient P ν α * u α x *
        negativeFourierCharacter (-(y.val : ℤ)) ((α : ℝ) : PrimeCircle) := by
  simp_rw [cyclicConvolutionSchwartz_apply, cyclicSynthesisSchwartz_apply, cyclicSynthesis,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α hα
  simp_rw [cyclicLiftCharacter_sub P α (hΓ α hα)]
  unfold cyclicRationalCoefficient
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem cyclicSynthesis_diagonal (Γ : Finset ℚ) (P : ℕ) [NeZero P]
    (hΓ : ∀ α ∈ Γ, α.den ∣ P) (u : ℚ → SchwartzMap ℝ ℂ) (n : ℤ) :
    cyclicDiagonal P (cyclicSynthesis Γ P u) n =
      ∑ α ∈ Γ, u α (n : ℝ) * negativeFourierCharacter (-n) ((α : ℝ) : PrimeCircle) := by
  unfold cyclicDiagonal cyclicSynthesis
  apply Finset.sum_congr rfl
  intro α hα
  rw [cyclicLiftCharacter_integer P α (hΓ α hα) n]

noncomputable def cyclicPointMass (P : ℕ) : ZMod P → ℂ :=
  fun z => if z = 0 then 1 else 0

theorem cyclicPointMass_variation (P : ℕ) [NeZero P] :
    cyclicVariation P (cyclicPointMass P) = 1 := by
  classical
  simp only [cyclicVariation, cyclicPointMass]
  simp_rw [apply_ite norm, norm_one, norm_zero]
  simp

theorem cyclicPointMass_coefficient (P : ℕ) [NeZero P] (α : ℚ) :
    cyclicRationalCoefficient P (cyclicPointMass P) α = 1 := by
  classical
  simp [cyclicRationalCoefficient, cyclicPointMass, negativeFourierCharacter]

theorem iw_finite_lift_diagonal (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (hΓ : ∀ α ∈ iwFrequencySet S k, α.den ∣ P)
    (m : BoundedContinuousFunction ℝ ℂ) (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0)
    (hn : ∀ θ : ℝ, 1/2 ≤ |θ| → m θ = 0) (hm : ContDiff ℝ ∞ (m : ℝ → ℂ))
    (F : Finset ℤ) (f : ℤ → ℂ) :
    cyclicDiagonal P (cyclicSynthesis (iwFrequencySet S k) P (finiteLiftComponent m hs hm F f)) =
      (integerMultiplier (iwCyclicSymbol S k P (cyclicPointMass P) m hs) (finiteInputLp F f 2) : ℤ → ℂ) := by
  funext n
  rw [cyclicSynthesis_diagonal _ P hΓ,
    iwCyclicSymbol_finite_lift S k P (cyclicPointMass P) m hs hn hm F f n]
  apply Finset.sum_congr rfl
  intro α _
  rw [cyclicPointMass_coefficient, one_mul, mul_comm]

theorem iw_cyclic_convolution_lift_diagonal (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (hΓ : ∀ α ∈ iwFrequencySet S k, α.den ∣ P) (ν : ZMod P → ℂ)
    (m : BoundedContinuousFunction ℝ ℂ) (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0)
    (hn : ∀ θ : ℝ, 1/2 ≤ |θ| → m θ = 0) (hm : ContDiff ℝ ∞ (m : ℝ → ℂ))
    (F : Finset ℤ) (f : ℤ → ℂ) (n : ℤ) :
    cyclicDiagonal P
      (fun y x => cyclicConvolutionSchwartz P ν
        (cyclicSynthesisSchwartz (iwFrequencySet S k) P (finiteLiftComponent m hs hm F f)) y x) n =
      integerMultiplier (iwCyclicSymbol S k P ν m hs) (finiteInputLp F f 2) n := by
  change cyclicConvolutionSchwartz P ν
    (cyclicSynthesisSchwartz (iwFrequencySet S k) P (finiteLiftComponent m hs hm F f))
    (n : ZMod P) (n : ℝ) = _
  rw [cyclicSynthesis_convolution _ P hΓ,
    iwCyclicSymbol_finite_lift S k P ν m hs hn hm F f n]
  apply Finset.sum_congr rfl
  intro α hα
  rw [cyclicLiftCharacter_integer P α (hΓ α hα) n]
  ring

theorem iw_finite_lift_size {C : ℝ} (hC : 2 ≤ C)
    (HIW : RawIWMultiplierInput C) (HS : RawMajorArcSamplingInput C)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (m : BoundedContinuousFunction ℝ ℂ) (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0)
    (hn : ∀ θ : ℝ, 1/2 ≤ |θ| → m θ = 0)
    (hε : ∀ θ : ℝ, iwWidth C r k Q ≤ |θ| → m θ = 0)
    (hm : ContDiff ℝ ∞ (m : ℝ → ℂ)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : RealLpMultiplierBound (ENNReal.ofReal (iwNearOneExponent r)) m K)
    (F : Finset ℤ) (f : ℤ → ℂ)
    (hf : MemLp (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count) :
    cyclicRealLpSize d.period (ENNReal.ofReal (iwNearOneExponent r))
      (cyclicSynthesis (iwFrequencySet d.S k) d.period (finiteLiftComponent m hs hm F f)) ≤
      ENNReal.ofReal ((iwMultiplierConstant C r k)^2*K)*
        eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  have hp2r : iwNearOneExponent r ≤ 2*(r : ℝ) := by
    have hp := iwNearOneExponent_bounds hr
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hI := quantitative_iw_multiplier hC HIW hr hk d m hs hε hm (cyclicPointMass d.period)
    (cyclicPointMass_variation d.period).le le_rfl hp2r hK hbound (finiteInputLp F f 2) hf
  have he := iw_finite_lift_diagonal d.S k d.period d.periodic m hs hn hm F f
  have hd : MemLp (cyclicDiagonal d.period (cyclicSynthesis (iwFrequencySet d.S k) d.period
      (finiteLiftComponent m hs hm F f))) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
    rw [he]
    exact hI.1
  have hband : ∀ α ∈ iwFrequencySet d.S k, ∀ θ : ℝ, iwWidth C r k Q ≤ |θ| →
      𝓕 (finiteLiftComponent m hs hm F f α : ℝ → ℂ) θ = 0 := by
    intro α _ θ hθ
    rw [finiteLiftComponent_fourier, hε θ hθ, zero_mul]
  have hS := quantitative_iw_sampling hC HS hr hk d (finiteLiftComponent m hs hm F f) hband hd
  rw [he] at hS
  refine hS.trans ?_
  calc
    _ ≤ ENNReal.ofReal (iwMultiplierConstant C r k)*
        (ENNReal.ofReal (iwMultiplierConstant C r k*K)*
          eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count) :=
      mul_le_mul_right hI.2 _
    _ = _ := by
      rw [←mul_assoc, ←ENNReal.ofReal_mul (iwMultiplierConstant_nonneg (by linarith : 0 ≤ C) r k)]
      congr 2
      ring

end PrimeSquares
