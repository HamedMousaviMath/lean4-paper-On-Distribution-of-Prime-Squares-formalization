import PrimeSquares.ContinuousAnnularCutoffLp
import PrimeSquares.AnnularFourierSmoothness
import PrimeSquares.IWActualAnnularSymbols

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem scaled_cutoff_boundary_zero {a w x : ℝ} (ha : 0≤ a)
    (haw : 1≤ a*w) (hx : w≤|x|) : sourceArcCutoff (a*x)=0 := by
  apply sourceArcCutoff_zero
  rw [abs_mul,abs_of_nonneg ha]
  exact haw.trans (mul_le_mul_of_nonneg_left hx ha)

theorem allAnnularBoundedSymbol_boundary (N : ℕ) (hN : 1≤ N) (β : ℝ)
    (hβ0 : 0≤β) (hβ1 : β≤1) {a w : ℝ} (ha : 0≤ a) (haw : 1≤ a*w)
    (x : ℝ) (hx : w≤|x|) : allAnnularBoundedSymbol N hN β hβ0 hβ1 a x=0 := by
  rw [allAnnularBoundedSymbol_apply,scaled_cutoff_boundary_zero ha haw hx,
    Complex.ofReal_zero,mul_zero]

theorem continuousAnnularSignedSymbol_boundary (β : ℝ) (hβ0 : 0≤β) (hβ1 : β≤1)
    (J : ℕ) (σ : ℕ→ℂ) {a w : ℝ} (ha : 0≤ a) (haw : 1≤ a*w)
    (x : ℝ) (hx : w≤|x|) : continuousAnnularSignedSymbol β hβ0 hβ1 a J σ x=0 := by
  rw [continuousAnnularSignedSymbol_apply,scaled_cutoff_boundary_zero ha haw hx,
    Complex.ofReal_zero,mul_zero]

theorem iwNearOneExponent_cost {r : ℕ} (hr : 2≤ r) {A : ℝ} (hA : 0≤ A) :
    A/(iwNearOneExponent r-1)≤2*A*(r : ℝ) := by
  rw [iwNearOneExponent_sub_one hr,div_div_eq_mul_div,div_one]
  nlinarith

theorem iwMultiplierConstant_nonneg {C : ℝ} (hC : 0≤ C) (r k : ℕ) :
    0≤ iwMultiplierConstant C r k := by
  have hl : 0≤ Real.log (2+k : ℝ) := Real.log_nonneg (by have hk : (0 : ℝ)≤k := Nat.cast_nonneg k;linarith)
  unfold iwMultiplierConstant
  exact Real.rpow_nonneg (by positivity) _

noncomputable def iwAnnularIncrementCost (Z : ℝ) : ℝ :=
  2*(Z*(continuousAnnularIncrementConstant+2+50))*cutoffL1Constant

theorem iwAnnularIncrementCost_nonneg {Z : ℝ} (hZ : 0≤ Z) : 0≤ iwAnnularIncrementCost Z := by
  unfold iwAnnularIncrementCost
  have h := continuousAnnularIncrementConstant_pos
  have hcut := cutoffL1Constant_nonneg
  positivity

theorem iw_signed_annular_multiplier {C Z : ℝ} (hC : 2≤ C) (hZ : 0≤ Z)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    {r k Q : ℕ} (hr : 2≤ r) (hk : 4≤ k)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period→ℂ) (hν : cyclicVariation d.period ν≤1)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1)
    (J : ℕ) (σ : ℕ→ℂ) (hσ : ∀ j∈range J,‖σ j‖≤1)
    (hs : ∀ x : ℝ,1≤|x| →
      continuousAnnularSignedSymbol β hβ0.le hβ1 (iwCutoffScale C r k Q) J σ x=0) :
    IntegerLpMultiplierBound (ENNReal.ofReal (iwNearOneExponent r))
      (iwCyclicSymbol d.S k d.period ν
        (continuousAnnularSignedSymbol β hβ0.le hβ1 (iwCutoffScale C r k Q) J σ) hs)
      (iwAnnularIncrementCost Z*(r : ℝ)*iwMultiplierConstant C r k) := by
  have ha4 := iwCutoffScale_four_le hC hr k Q
  have ha : 0< iwCutoffScale C r k Q := by linarith
  have hw := iwWidth_pos hC hr k Q
  have haw : 1≤ iwCutoffScale C r k Q*iwWidth C r k Q := by
    rw [iwCutoffScale,inv_mul_cancel₀ hw.ne']
  have hpr := iwNearOneExponent_bounds hr
  have hp2 : iwNearOneExponent r≤2 := by linarith
  have hp2r : iwNearOneExponent r≤2*(r : ℝ) := by
    have hrR : (2 : ℝ)≤ r := by exact_mod_cast hr
    linarith
  have hcont := continuousAnnularCutoffSignedMultiplier_Lp hZ HCZ HY hβ0 hβ1 ha J σ hσ hpr.1 hp2
  have hK : 0≤(Z*(continuousAnnularIncrementConstant+2+50)/(iwNearOneExponent r-1))*cutoffL1Constant := by
    have hp : 0< iwNearOneExponent r-1 := by linarith [hpr.1]
    have h := continuousAnnularIncrementConstant_pos
    have hcut := cutoffL1Constant_nonneg
    positivity
  have hiw := quantitative_iw_multiplier hC HIW hr hk d _ hs
    (continuousAnnularSignedSymbol_boundary β hβ0.le hβ1 J σ ha.le haw)
    (continuousAnnularSignedSymbol_contDiff β hβ0.le hβ1 (iwCutoffScale C r k Q) J σ)
    ν hν le_rfl hp2r hK hcont
  apply integerLpMultiplierBound_mono hiw
  have hA : 0≤ Z*(continuousAnnularIncrementConstant+2+50) := by
    have h := continuousAnnularIncrementConstant_pos
    positivity
  have hb := mul_le_mul_of_nonneg_right (iwNearOneExponent_cost hr hA) cutoffL1Constant_nonneg
  have hm := mul_le_mul_of_nonneg_left hb (iwMultiplierConstant_nonneg (by linarith : 0≤ C) r k)
  exact hm.trans_eq (by unfold iwAnnularIncrementCost;ring)

end PrimeSquares
