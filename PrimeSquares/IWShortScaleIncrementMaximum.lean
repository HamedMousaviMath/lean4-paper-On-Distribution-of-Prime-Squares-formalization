import PrimeSquares.IWAnnularLp
import PrimeSquares.FiniteSignedMaximalInterface

set_option autoImplicit false
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares

noncomputable def iwAnnularIncrementSequence (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (ν : ZMod P→ℂ) (β a : ℝ) (ha : 2≤ a) (f : ℓ²(ℤ,ℂ)) (j : ℕ) (x : ℤ) : ℂ :=
  iwAnnularLowOperator S k P ν ((2 : ℕ)^(j+1)) (one_le_pow₀ (by norm_num)) β a ha f x-
    iwAnnularLowOperator S k P ν ((2 : ℕ)^j) (one_le_pow₀ (by norm_num)) β a ha f x

theorem iwAnnularIncrementSequence_signed (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (ν : ZMod P→ℂ) (β a : ℝ) (ha : 2≤ a) (f : ℓ²(ℤ,ℂ)) (J : ℕ) (σ : ℕ→ℂ) :
    signedSequenceSum (iwAnnularIncrementSequence S k P ν β a ha f) J σ=
      (iwAnnularSignedOperator S k P ν β a ha J σ f : ℤ→ℂ) := by
  funext x
  simp only [signedSequenceSum,iwAnnularIncrementSequence,iwAnnularSignedOperator,
    _root_.sum_apply,_root_.smul_apply,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,
    Pi.smul_apply,smul_eq_mul,_root_.sub_apply,lp.coeFn_sub,Pi.sub_apply]

theorem iw_short_scale_increment_maximum {C Z R : ℝ} (hC : 2≤ C) (hZ : 0≤ Z)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) {r k Q : ℕ} (hr : 2≤ r) (hk : 4≤ k)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period→ℂ) (hν : cyclicVariation d.period ν≤1)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (J : ℕ) (f : ℓ²(ℤ,ℂ))
    (hf : MemLp (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count)
    (ha : 2≤ iwCutoffScale C r k Q) :
    MemLp (finitePartialSumMaximum
      (iwAnnularIncrementSequence d.S k d.period ν β (iwCutoffScale C r k Q) ha f) J)
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
    eLpNorm (finitePartialSumMaximum
      (iwAnnularIncrementSequence d.S k d.period ν β (iwCutoffScale C r k Q) ha f) J)
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count≤
      ENNReal.ofReal (R*Real.log (2+(J : ℝ)))*
        (ENNReal.ofReal (iwAnnularIncrementCost Z*(r : ℝ)*iwMultiplierConstant C r k)*
          eLpNorm (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count) := by
  have hp := iwNearOneExponent_bounds hr
  apply finite_signed_maximal HRM hp.1.le (by linarith [hp.2])
  intro σ hσ
  rw [iwAnnularIncrementSequence_signed]
  exact iw_annular_signed_increments hC hZ HIW HCZ HY hr hk d ν hν hβ0 hβ1 J σ hσ f hf

end PrimeSquares
