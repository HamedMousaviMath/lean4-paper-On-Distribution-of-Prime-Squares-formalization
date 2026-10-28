import PrimeSquares.IWPrimeHighMaximum

set_option autoImplicit false
open scoped lp
namespace PrimeSquares

theorem iw_source_cutoff_of_exp {δ A S Q X : ℝ} (hδ : 0<δ)
    (hA : (δ^2)⁻¹≤A) (hQ : 1≤Q) (hX : 1≤X)
    (hS : (Real.log Q)^2≤S) (hstart : Real.exp (A*S)≤X) :
    Real.log Q≤δ*Real.sqrt (Real.log X) := by
  have hδ2 : 0<δ^2 := sq_pos_of_pos hδ
  have hA0 : 0≤A := (inv_pos.mpr hδ2).le.trans hA
  have hlog : A*S≤Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hstart
  have hAL : A*(Real.log Q)^2≤Real.log X :=
    (mul_le_mul_of_nonneg_left hS hA0).trans hlog
  have hδA : 1≤δ^2*A := by
    have h := mul_le_mul_of_nonneg_left hA hδ2.le
    rwa [mul_inv_cancel₀ hδ2.ne'] at h
  have hmul := mul_le_mul_of_nonneg_left hAL hδ2.le
  have hlower := mul_le_mul_of_nonneg_right hδA (sq_nonneg (Real.log Q))
  have hsquare : (Real.log Q)^2≤δ^2*Real.log X := by nlinarith
  apply (sq_le_sq₀ (Real.log_nonneg hQ) (mul_nonneg hδ.le (Real.sqrt_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (Real.log_nonneg hX)]
  exact hsquare

/-- Exact conclusion of the prime high-side comparison. This predicate
contains the actual operator family and all norm and geometry assertions. -/
def IWPrimeHighBound {c : ℝ} (D : PagePrimeSquareDistributionInputs c) (C : ℝ)
    (r k Q M : ℕ) (hC : 2≤C) (hr : 2≤r) (hM : 2≤M) (K : ℝ) : Prop :=
  ∃ d : TaoArcConstructionData C (iwRho k) k Q,
    IWGood r k d.S (iwWidth C r k Q) ∧
    (∀ t∈iwFrequencySet d.S k,(t.den : ℝ)≤ iwDenominatorBound C k Q) ∧
    ∃ E₀ : Option PageZeroDatum,
      (∀ F,E₀=some F → F.conductor≤Q ∧ F.conductor∣d.period) ∧
      ∀ f : ℓ²(ℤ,ℂ),∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
        (∀ j x,‖iwPrimeHighOperator D (iwFrequencySet d.S k) ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) (iwCutoffScale C r k Q)
          (by have h := iwCutoffScale_four_le hC hr k Q;linarith) E₀ Q f x‖≤g x) ∧
        ‖g‖≤K*(Q : ℝ)^(-(1/4 : ℝ))*‖f‖

/-- The full prime high-side rate under precisely the source's sufficiently
large exponential starting scale; no extra Q-range premise remains. -/
theorem iw_prime_high_source_scale {Cb c : ℝ} (hCb : 0≤Cb) (HB : SmoothCircleBourgainInput Cb)
    (hc : 0<c) (HP : RawPageUniquenessInput c) (D : PagePrimeSquareDistributionInputs c) :
    ∃ Cstart K : ℝ,0<Cstart ∧ 0<K ∧ ∀ (C : ℝ) (hC : 2≤C),Real.exp 1≤C →
      RawTaoArcConstructionInput C → ∀ (r k Q M : ℕ) (hr : 2≤r),4≤k → 2^k≤Q →
      ∀ hM : 2≤M,Real.exp (Cstart*((Real.log (Q : ℝ))^2+
        (r : ℝ)*Real.log (iwDenominatorBound C k Q)))≤M →
      IWPrimeHighBound D C r k Q M hC hr hM K := by
  obtain ⟨δ,K,hδ,hK,hHigh⟩ := iw_prime_high_maximum hCb HB hc HP D
  let Cstart := max 25 ((δ^2)⁻¹)
  have h25 : 25≤Cstart := le_max_left _ _
  have hCstart : 0<Cstart := (by norm_num : (0 : ℝ)<25).trans_le h25
  refine ⟨Cstart,K,hCstart,hK,?_⟩
  intro C hC hCe HT r k Q M hr hk hQ hM hstart
  let S := (Real.log (Q : ℝ))^2+(r : ℝ)*Real.log (iwDenominatorBound C k Q)
  have hlogB : 0≤Real.log (iwDenominatorBound C k Q) :=
    Real.log_nonneg (iwDenominatorBound_one_le hC k Q)
  have hS : (Real.log (Q : ℝ))^2≤S := by
    dsimp [S]
    have hm := mul_nonneg (Nat.cast_nonneg (α := ℝ) r) hlogB
    linarith
  have hS0 : 0≤S := (sq_nonneg _).trans hS
  have hQnat : 1≤Q := (one_le_pow₀ (by norm_num : 1≤(2 : ℕ))).trans hQ
  have hcut : Real.log (Q : ℝ)≤δ*Real.sqrt (Real.log (M : ℝ)) :=
    iw_source_cutoff_of_exp hδ (le_max_right _ _) (by exact_mod_cast hQnat)
      (by exact_mod_cast (show 1≤M by omega)) hS hstart
  have hstart25 : Real.exp (25*S)≤M :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h25 hS0)).trans hstart
  exact hHigh C hC hCe HT r k Q M hr hk hQ hM hstart25 hcut

end PrimeSquares
