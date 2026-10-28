import PrimeSquares.CommonCutoffPowerMaximum
import PrimeSquares.CyclicRationalGaussDecay

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

noncomputable def iwCutoffScale (C : ℝ) (r k Q : ℕ) : ℝ := (iwWidth C r k Q)⁻¹

theorem iwCutoffScale_formula (C : ℝ) (r k Q : ℕ) :
    iwCutoffScale C r k Q=2^20*(r : ℝ)*(iwDenominatorBound C k Q)^(2*r+8) := by
  simp only [iwCutoffScale,iwWidth,inv_inv]

theorem iwCutoffScale_four_le {C : ℝ} (hC : 2≤C) {r : ℕ} (hr : 2≤r) (k Q : ℕ) :
    4≤ iwCutoffScale C r k Q := by
  have hB := iwDenominatorBound_one_le hC k Q
  have hp := one_le_pow₀ hB (n := 2*r+8)
  have hrR : (2 : ℝ)≤r := by exact_mod_cast hr
  rw [iwCutoffScale_formula]
  have hm := mul_le_mul_of_nonneg_left hp (show 0≤2^20*(r : ℝ) by positivity)
  norm_num only [mul_one] at hm
  nlinarith

theorem iwCutoffScale_band_core {C : ℝ} (hC : 2≤C) {r k Q : ℕ} (hr : 2≤r)
    (hk : 4≤k) (d : TaoArcConstructionData C (iwRho k) k Q)
    {t : ℚ} (ht : t∈iwFrequencySet d.S k) :
    2*(16 : ℝ)^(Nat.log2 t.den)≤ iwCutoffScale C r k Q := by
  let B := iwDenominatorBound C k Q
  have hB : 1≤B := iwDenominatorBound_one_le hC k Q
  have hden : (t.den : ℝ)≤B := taoArc_denominator_bound hC d hk ht
  have hlog : (2 : ℝ)^(Nat.log2 t.den)≤t.den := by
    exact_mod_cast Nat.log2_self_le t.den_pos.ne'
  have hscale : (16 : ℝ)^(Nat.log2 t.den)≤B^4 := by
    rw [dyadic_sixteen_scale]
    exact pow_le_pow_left₀ (by positivity) (hlog.trans hden) 4
  have hp : B^4≤B^(2*r+8) := pow_le_pow_right₀ hB (by omega)
  have hrR : (2 : ℝ)≤r := by exact_mod_cast hr
  have hc : (2 : ℝ)≤2^20*(r : ℝ) := by nlinarith
  rw [iwCutoffScale_formula]
  exact (mul_le_mul_of_nonneg_left hscale (by norm_num)).trans
    (mul_le_mul hc hp (by positivity) (by positivity))

/-- The common-IW-cutoff tail for the actual cyclic square measure, with its
proved character coefficients. No low-model maximal estimate is a premise. -/
theorem iw_cyclic_square_common_tail {Cb : ℝ} (hCb : 0≤Cb)
    (HB : SmoothCircleBourgainInput Cb) :
    ∃ K : ℝ,0<K ∧ ∀ (C : ℝ) (hC : 2≤C) (r k Q : ℕ) (hr : 2≤r) (_hk : 4≤k) (_hQ : 2^k≤Q),
      ∀ (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
        (χ : DirichletCharacter ℂ d.period) (M : ℕ) (hM : 2≤M)
        (β : ℕ → ℝ),(∀ j,0≤β j) → (∀ j,β j≤1) → ∀ f : ℓ²(ℤ,ℂ),
      ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
        (∀ j x,‖integerMultiplier (weightedWidthAnnularBlock
          ((iwFrequencySet d.S k).filter (fun t => (Q : ℝ)<(t.den : ℝ))) ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) (β j) (iwCutoffScale C r k Q)
          (by have h := iwCutoffScale_four_le hC hr k Q;linarith)
          (cyclicRationalCoefficient d.period (cyclicSquareMeasure d.period χ))) f x‖≤g x) ∧
        ‖g‖≤K*(Q : ℝ)^(-(1/4 : ℝ))*‖f‖ := by
  obtain ⟨A,hA,hGauss⟩ := cyclicRationalSquare_uniform_decay (by norm_num : (3/8 : ℝ)<1/2)
  refine ⟨annularPowerConstant Cb (1/8)*A,mul_pos (annularPowerConstant_pos hCb _) hA,?_⟩
  intro C hC r k Q hr hk hQ d inst χ M hM β hβ0 hβ1 f
  have h16 : 16≤2^k := by
    calc
      16 = 2^4 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hQ4 : (4 : ℝ)≤Q := by exact_mod_cast (show 4≤Q by omega)
  let Γ := iwFrequencySet d.S k
  exact common_cutoff_denominator_tail hCb HB hA.le (iwCutoffScale_four_le hC hr k Q) hQ4 hM Γ
    (fun t ht => ((iwFrequencySet_mem d.positive t).mp ht).1)
    (fun t ht => Finset.le_sup (f := Rat.den) ht)
    (fun t ht => iwCutoffScale_band_core hC hr hk d ht) β hβ0 hβ1
    (cyclicRationalCoefficient d.period (cyclicSquareMeasure d.period χ))
    (fun t ht => hGauss d.period χ t (d.periodic t ht)) f

end PrimeSquares
