import PrimeSquares.RealLineFourierMultipliers
import PrimeSquares.CyclicConductorCoefficients
import PrimeSquares.IWGoodness
import PrimeSquares.CompactCirclePeriodization
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false
open Finset
open scoped ContDiff
namespace PrimeSquares

noncomputable def cyclicRationalCoefficient (P : ℕ) [NeZero P]
    (ν : ZMod P → ℂ) (r : ℚ) : ℂ :=
  ∑ z : ZMod P,ν z*negativeFourierCharacter (z.val : ℤ) ((r : ℝ) : PrimeCircle)

theorem cyclicRationalCoefficient_norm (P : ℕ) [NeZero P]
    (ν : ZMod P → ℂ) (r : ℚ) :
    ‖cyclicRationalCoefficient P ν r‖≤cyclicVariation P ν := by
  calc
    _ ≤ ∑ z : ZMod P,‖ν z*negativeFourierCharacter (z.val : ℤ) ((r : ℝ) : PrimeCircle)‖ :=
      norm_sum_le _ _
    _ = _ := by simp only [norm_mul,negativeFourierCharacter_norm,mul_one,cyclicVariation]

/-- The literal sum of periodized translates; its operator is the already
constructed negative-phase integer Fourier multiplier. -/
noncomputable def iwCyclicSymbol (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (ν : ZMod P → ℂ) (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ x : ℝ,1≤|x| → m x=0) : C(PrimeCircle,ℂ) :=
  ∑ r∈iwFrequencySet S k,cyclicRationalCoefficient P ν r •
    (compactCircleLift m.toContinuousMap hs).comp
      ⟨fun ξ => ξ-((r : ℝ) : PrimeCircle),continuous_id.sub continuous_const⟩

theorem iwCyclicSymbol_real (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (ν : ZMod P → ℂ) (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ x : ℝ,1≤|x| → m x=0) (ξ : ℝ) :
    iwCyclicSymbol S k P ν m hs (ξ : PrimeCircle)=
      ∑ r∈iwFrequencySet S k,cyclicRationalCoefficient P ν r *
        ∑' n : ℤ,m (ξ-(r : ℝ)+n) := by
  simp only [iwCyclicSymbol,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    ContinuousMap.comp_apply,ContinuousMap.coe_mk,smul_eq_mul]
  apply sum_congr rfl
  intro r _
  rw [←AddCircle.coe_sub,compactCircleLift_all_real]
  rfl

/-- Independent smooth IW multiplier theorem, in dimension one, with c=1/2.
This is an explicit hypothesis on arbitrary good coprime sets and arbitrary
smooth compact symbols. It contains no annular, beta, maximal, arithmetic
low/high, restricted-type or current-paper conclusion. No existence or proof
of this deep theorem is asserted by declaring the predicate. -/
def RawIWMultiplierInput (C : ℝ) : Prop :=
  ∀ (r k : ℕ),2≤r → 1≤k → ∀ S : Finset ℕ,
    (∀ s∈S,0<s) → (S : Set ℕ).Pairwise Nat.Coprime →
    ∀ (P : ℕ) [NeZero P],(∀ a∈iwFrequencySet S k,a.den∣P) →
    ∀ ε : ℝ,IWGood r k S ε →
    ∀ (m : BoundedContinuousFunction ℝ ℂ) (hs : ∀ x : ℝ,1≤|x| → m x=0),
    (∀ x : ℝ,ε≤|x| → m x=0) → ContDiff ℝ ∞ (m : ℝ → ℂ) →
    ∀ ν : ZMod P → ℂ,cyclicVariation P ν≤1 →
    ∀ p : ℝ,iwNearOneExponent r≤p → p≤2*(r : ℝ) →
    ∀ K : ℝ,0≤K → RealLpMultiplierBound (ENNReal.ofReal p) m K →
      IntegerLpMultiplierBound (ENNReal.ofReal p) (iwCyclicSymbol S k P ν m hs)
        (iwMultiplierConstant C r k*K)

theorem quantitative_iw_multiplier {C : ℝ} (hC : 2≤C)
    (HIW : RawIWMultiplierInput C) {r k Q : ℕ} (hr : 2≤r) (hk : 4≤k)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (m : BoundedContinuousFunction ℝ ℂ) (hs : ∀ x : ℝ,1≤|x| → m x=0)
    (hε : ∀ x : ℝ,iwWidth C r k Q≤|x| → m x=0)
    (hm : ContDiff ℝ ∞ (m : ℝ → ℂ))
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν≤1)
    {p K : ℝ} (hp0 : iwNearOneExponent r≤p) (hp1 : p≤2*(r : ℝ))
    (hK : 0≤K) (hbound : RealLpMultiplierBound (ENNReal.ofReal p) m K) :
    IntegerLpMultiplierBound (ENNReal.ofReal p)
      (iwCyclicSymbol d.S k d.period ν m hs) (iwMultiplierConstant C r k*K) := by
  exact HIW r k hr (by omega) d.S d.positive d.coprime d.period d.periodic
    (iwWidth C r k Q) (quantitative_iw_goodness hC hr hk d) m hs hε hm ν hν p hp0 hp1 K hK hbound

end PrimeSquares
