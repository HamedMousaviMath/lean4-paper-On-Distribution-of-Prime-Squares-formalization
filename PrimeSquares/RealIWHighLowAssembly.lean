import PrimeSquares.RealIWHighData
import PrimeSquares.IWFullSquareHighSourceScale


set_option autoImplicit false
open scoped lp Classical
namespace PrimeSquares

/-- The high estimates hold for every construction satisfying the geometric
conditions, so the prime and ordinary-square families may use the same data. -/
theorem iw_prime_high_maximum_for_data {Cb c : ℝ} (hCb : 0≤Cb) (HB : SmoothCircleBourgainInput Cb)
    (hc : 0<c) (HP : RawPageUniquenessInput c) (D : PagePrimeSquareDistributionInputs c) :
    ∃ δ K : ℝ,0<δ ∧ 0<K ∧ ∀ (C : ℝ) (hC : 2≤C) (_hCe : Real.exp 1≤C)
      (r k Q M : ℕ) (hr : 2≤r) (_hk : 4≤k)
      (_hQ : 2^k≤Q) (hM : 2≤M) (d : TaoArcConstructionData C (iwRho k) k Q),
      Real.exp (25*((Real.log (Q : ℝ))^2+(r : ℝ)*Real.log (iwDenominatorBound C k Q)))≤M →
      Real.log (Q : ℝ)≤δ*Real.sqrt (Real.log (M : ℝ)) →
        ∃ E₀ : Option PageZeroDatum,
          (∀ F,E₀=some F → F.conductor≤Q ∧ F.conductor∣d.period) ∧
          ∀ f : ℓ²(ℤ,ℂ),∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
            (∀ j x,‖iwPrimeHighOperator D (iwFrequencySet d.S k) ((2 : ℕ)^j*M)
              (by have h := dyadic_annular_scale_lower hM j;omega) (iwCutoffScale C r k Q)
              (by have h := iwCutoffScale_four_le hC hr k Q;linarith) E₀ Q f x‖≤g x) ∧
            ‖g‖≤K*(Q : ℝ)^(-(1/4 : ℝ))*‖f‖ := by
  obtain ⟨δ,KE,hδ,hKE,hRaw,hError⟩ := iw_prime_approximation_maximum D
  obtain ⟨KM,hKM,hModel⟩ := iw_page_model_maximum hCb HB hc HP
  refine ⟨δ,KM+KE,hδ,add_pos hKM hKE,?_⟩
  intro C hC hCe r k Q M hr hk hQ hM d hstart hcut
  have h16 : 16≤2^k := by
    calc
      16 = 2^4 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hQ2 : (2 : ℝ)≤Q := by exact_mod_cast (show 2≤Q by omega)
  have hQ1 : (1 : ℝ)≤Q := by linarith
  have hM2 : (2 : ℝ)≤M := by exact_mod_cast hM
  have hbudget := iw_starting_budget_of_source_scale hC hCe hr hk (show 1≤Q by omega) hM hstart
  let E := fun j => sourcePageDatum D ((2 : ℕ)^j*M) Q
  let R := fun j => sourceMajorArcScale (((2 : ℕ)^j*M : ℕ) : ℝ) Q
  have hR : ∀ j,(Q : ℝ)≤R j := fun j => sourceMajorArcScale_cutoff_le hQ1 _
  have hE : ∀ j F,E j=some F → (F.conductor : ℝ)≤R j ∧ 1-(c/2)/Real.log (R j)<F.beta := by
    intro j F hF
    have hp : (1 : ℕ)≤2^j := one_le_pow₀ (by norm_num)
    have hMN : (M : ℝ)≤(((2 : ℕ)^j*M : ℕ) : ℝ) := by
      exact_mod_cast (show M≤(2 : ℕ)^j*M by simpa only [one_mul] using Nat.mul_le_mul_right M hp)
    exact (sourcePageDatum_spec D _ Q (hRaw Q M hQ2 hM2 hcut _ hMN)).1 F hF
  obtain ⟨E₀,h₀,hselected,hmodel⟩ := hModel C hC r k Q M hr hk hQ hM d hbudget E R hR hE
  refine ⟨E₀,?_,?_⟩
  · intro F hF
    have hs : F.conductor≤Q := by exact_mod_cast (h₀ F hF).1
    exact ⟨hs,iw_period_divisible_small d F.conductor_two hs⟩
  · intro f
    obtain ⟨gm,hgm,htm,hnm⟩ := hmodel f
    obtain ⟨ge,hge,hte,hne⟩ := hError Q hQ2 M hM hcut f
    have hQpow : (Q : ℝ)^(-(1/2 : ℝ))≤(Q : ℝ)^(-(1/4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
    have hne' : ‖ge‖≤KE*(Q : ℝ)^(-(1/4 : ℝ))*‖f‖ :=
      hne.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQpow hKE.le) (norm_nonneg _))
    refine ⟨gm+ge,fun x => add_nonneg (hgm x) (hge x),?_,?_⟩
    · intro j x
      rw [iwPrimeHigh_error_model,_root_.add_apply,lp.coeFn_add,Pi.add_apply]
      change _≤gm x+ge x
      exact (norm_add_le _ _).trans ((add_le_add (hte j x) (htm j x)).trans_eq (add_comm _ _))
    · exact ((norm_add_le gm ge).trans (add_le_add hnm hne')).trans_eq (by ring)


theorem iw_full_square_high_source_scale_for_data {Cb E : ℝ} (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E) :
    ∃ Cstart K : ℝ, 0 < Cstart ∧ 0 < K ∧ ∀ (C : ℝ) (hC : 2 ≤ C), Real.exp 1 ≤ C →
      ∀ (r k Q M : ℕ) (hr : 2 ≤ r), 4 ≤ k → 2^k ≤ Q →
      ∀ (hM : 2 ≤ M) (d : TaoArcConstructionData C (iwRho k) k Q), Even M →
      Real.exp (Cstart*((Real.log (Q : ℝ))^2+(r : ℝ)*Real.log (iwDenominatorBound C k Q))) ≤ M →
      (let : NeZero d.period := ⟨d.period_pos.ne'⟩
       ∀ f : ℓ²(ℤ,ℂ), ∃ g : lp (fun _ : ℤ => ℝ) 2, (∀ x, 0 ≤ g x) ∧
         (∀ j x, ‖iwFullSquareHighOperator d.S k d.period ((2 : ℕ)^j*M)
           (by have h := dyadic_annular_scale_lower hM j; omega) (iwCutoffScale C r k Q)
           (by have h := iwCutoffScale_four_le hC hr k Q; linarith) f x‖ ≤ g x) ∧
         ‖g‖ ≤ K*(Q : ℝ)^(-(1/4 : ℝ))*‖f‖) := by
  obtain ⟨N₀, hN₀, hError⟩ := full_square_approximation_maximum hE HE
  let Cstart := max 64 (max 25 (Real.log ((N₀ : ℝ)+1)))
  let K := iwFullSquareModelConstant Cb+fullSquareErrorMaximalConstant
  have h64 : (64 : ℝ) ≤ Cstart := le_max_left _ _
  have h25 : (25 : ℝ) ≤ Cstart := (le_max_left _ _).trans (le_max_right _ _)
  have hlogStart : Real.log ((N₀ : ℝ)+1) ≤ Cstart := (le_max_right _ _).trans (le_max_right _ _)
  have hCstart : 0 < Cstart := by linarith
  have hK : 0 < K := add_pos (iwFullSquareModelConstant_pos hCb) fullSquareErrorMaximalConstant_pos
  refine ⟨Cstart, K, hCstart, hK, ?_⟩
  intro C hC hCe r k Q M hr hk hQ hM d hEven hstart
  have hQ1nat : 1 ≤ Q := (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))).trans hQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1nat
  have hlogC : 1 ≤ Real.log C := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hCe
  have hlogB := iwDenominatorBound_log_one_le hC hlogC hk hQ1nat
  let S := (Real.log (Q : ℝ))^2+(r : ℝ)*Real.log (iwDenominatorBound C k Q)
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hS : 1 ≤ S := by
    have hmul := mul_le_mul_of_nonneg_left hlogB (Nat.cast_nonneg (α := ℝ) r)
    dsimp [S]
    nlinarith [sq_nonneg (Real.log (Q : ℝ))]
  have hSlog : (Real.log (Q : ℝ))^2 ≤ S := by
    dsimp [S]
    have hmul := mul_nonneg (Nat.cast_nonneg (α := ℝ) r) (show 0 ≤ Real.log (iwDenominatorBound C k Q) by linarith)
    linarith
  have hlogM : Real.log ((N₀ : ℝ)+1) ≤ Cstart*S :=
    hlogStart.trans (le_mul_of_one_le_right hCstart.le hS)
  have hNMr : (N₀ : ℝ)+1 ≤ M := by
    calc
      _ = Real.exp (Real.log ((N₀ : ℝ)+1)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (Cstart*S) := Real.exp_le_exp.mpr hlogM
      _ ≤ _ := hstart
  have hNM : N₀ ≤ M := by exact_mod_cast (show (N₀ : ℝ) ≤ M by linarith)
  have hcut : Real.log (Q : ℝ) ≤ (1/8 : ℝ)*Real.sqrt (Real.log (M : ℝ)) :=
    iw_source_cutoff_of_exp (by norm_num : (0 : ℝ) < 1/8)
      (by norm_num; exact h64) hQ1 (by exact_mod_cast (show 1 ≤ M by omega)) hSlog hstart
  have hstart25 : Real.exp (25*S) ≤ M :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h25 (by linarith : 0 ≤ S))).trans hstart
  let : NeZero d.period := ⟨d.period_pos.ne'⟩
  have hbudget := iw_starting_budget_of_source_scale hC hCe hr hk hQ1nat hM hstart25
  let R := fun j => sourceMajorArcScale (((2 : ℕ)^j*M : ℕ) : ℝ) (Q : ℝ)
  have hR : ∀ j, (Q : ℝ) ≤ R j := fun j => sourceMajorArcScale_cutoff_le hQ1 _
  dsimp only
  intro f
  obtain ⟨gm, hgm, htm, hnm⟩ := iw_full_square_model_comparison hC hCb HB hr hk hQ hM d hbudget R hR f
  obtain ⟨ge, hge, hte, hne⟩ := hError M hNM hM hEven Q hQ1 hcut f
  have hpow : (Q : ℝ)^(-(1/2 : ℝ)) ≤ (Q : ℝ)^(-(1/4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  have hne' : ‖ge‖ ≤ fullSquareErrorMaximalConstant*(Q : ℝ)^(-(1/4 : ℝ))*‖f‖ :=
    hne.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow fullSquareErrorMaximalConstant_pos.le) (norm_nonneg _))
  refine ⟨gm+ge, fun x => add_nonneg (hgm x) (hge x), ?_, ?_⟩
  · intro j x
    rw [iwFullSquareHigh_error_model (P := d.period) (Q := (Q : ℝ)), _root_.add_apply, lp.coeFn_add, Pi.add_apply]
    change _ ≤ gm x+ge x
    exact (norm_add_le _ _).trans ((add_le_add (hte j x) (htm j x)).trans_eq (add_comm _ _))
  · exact ((norm_add_le gm ge).trans (add_le_add hnm hne')).trans_eq (by dsimp [K]; ring)


end PrimeSquares


set_option autoImplicit false
open scoped lp Classical
namespace PrimeSquares

/-- Both actual high families, with one arithmetic set and exact real width. -/
def RealIWHighComparison {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (C : ℝ) (k : ℕ) (Q : ℝ) (M : ℕ) (hM : 2 ≤ M)
    (d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊) [NeZero d.period]
    (a : ℝ) (ha : 2 ≤ a) (K : ℝ) : Prop :=
  ∃ E₀ : Option PageZeroDatum,
    (∀ E,E₀=some E → E.conductor ≤ ⌊Q⌋₊ ∧ E.conductor ∣ d.period) ∧
    ∀ f : ℓ²(ℤ,ℂ), ∃ gp gs : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,0≤gp x) ∧ (∀ x,0≤gs x) ∧
      (∀ j x,‖iwPrimeHighOperator D (iwFrequencySet d.S k) ((2:ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j; omega) a ha E₀ ⌊Q⌋₊ f x‖ ≤ gp x) ∧
      (∀ j x,‖iwFullSquareHighOperator d.S k d.period ((2:ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j; omega) a ha f x‖ ≤ gs x) ∧
      ‖gp‖+‖gs‖ ≤ K*Q^(-(1/4:ℝ))*‖f‖

theorem real_iw_high_comparison {Cb c E : ℝ} (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hc : 0<c) (HP : RawPageUniquenessInput c)
    (D : PagePrimeSquareDistributionInputs c) (hE : 0≤E) (HE : RawQuadraticWeylApproximationInput E) :
    ∃ Cstart K : ℝ,0<Cstart ∧ 0<K ∧
      ∀ (C : ℝ) (hC : 2≤C), Real.exp 1≤C →
      ∀ (r k : ℕ) (Q : ℝ) (M : ℕ) (hr : 2≤r) (hk : 4≤k) (hQ : (2:ℝ)^k≤Q),
      ∀ (hM : 2≤M), Even M →
      ∀ (d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊) [NeZero d.period],
      Real.exp (Cstart*((Real.log Q)^2+(r:ℝ)*Real.log (realIWDenominatorBound C k Q)))≤M →
      RealIWHighComparison D C k Q M hM d (realIWCutoffScale C r k Q)
        (by have hQ0 := (show (0:ℝ)≤(2:ℝ)^k by positivity).trans hQ
            have h := realIWCutoffScale_four_le hC hQ0 hr k
            linarith) K := by
  obtain ⟨δ,Kp,hδ,hKp,hprime⟩ := iw_prime_high_maximum_for_data hCb HB hc HP D
  obtain ⟨Cs,Ks,hCs,hKs,hsquare⟩ := iw_full_square_high_source_scale_for_data hCb HB hE HE
  let Cstart := max (max 25 ((δ^2)⁻¹)) Cs
  let K := 2*Kp+2*Ks
  have h25 : 25≤Cstart := (le_max_left _ _).trans (le_max_left _ _)
  have hδC : (δ^2)⁻¹≤Cstart := (le_max_right _ _).trans (le_max_left _ _)
  have hCsC : Cs≤Cstart := le_max_right _ _
  refine ⟨Cstart,K,by linarith,by dsimp [K]; positivity,?_⟩
  intro C hC hCe r k Q M hr hk hQ hM hEven d inst hstart
  let : NeZero d.period := inst
  have h16 : (16:ℝ)≤Q := by
    calc
      16 = (2:ℝ)^4 := by norm_num
      _ ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hk
      _ ≤ Q := hQ
  have hQ2 : 2≤Q := by linarith
  have hf := realIWFloor_bounds hQ2
  have hf1 : 1≤⌊Q⌋₊ := by exact_mod_cast hf.1
  have hfQ : (2:ℕ)^k≤⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ)
  let U := realIWUpperBase C k Q
  let du := realIWHighData hC hQ2 hk d
  let : NeZero du.period := ⟨du.period_pos.ne'⟩
  have hCU : C≤U := realIWUpperBase_lower hC hQ2 hk
  have hU : 2≤U := hC.trans hCU
  have hUe : Real.exp 1≤U := hCe.trans hCU
  have hB : iwDenominatorBound U k ⌊Q⌋₊=realIWDenominatorBound C k Q :=
    realIWUpperBase_denominator (by linarith : 0≤C) hQ2 k
  have ha : iwCutoffScale U r k ⌊Q⌋₊=realIWCutoffScale C r k Q :=
    realIWUpperBase_cutoff (by linarith : 0≤C) hQ2 r k
  let Sn := (Real.log (⌊Q⌋₊:ℝ))^2+(r:ℝ)*Real.log (iwDenominatorBound U k ⌊Q⌋₊)
  let Sr := (Real.log Q)^2+(r:ℝ)*Real.log (realIWDenominatorBound C k Q)
  have hSn0 : 0≤Sn := by
    dsimp [Sn]
    exact add_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg r)
      (Real.log_nonneg (iwDenominatorBound_one_le hU k ⌊Q⌋₊)))
  have hSn : Sn≤Sr := by
    have hl := Real.log_le_log (by linarith : (0:ℝ)<(⌊Q⌋₊:ℝ)) hf.2.2
    have hs := pow_le_pow_left₀ (Real.log_nonneg hf.1) hl 2
    dsimp [Sn,Sr]
    rw [hB]
    exact add_le_add hs le_rfl
  have hstartn : Real.exp (Cstart*Sn)≤M :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hSn (by linarith : 0≤Cstart))).trans hstart
  have h25n : Real.exp (25*Sn)≤M :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h25 hSn0)).trans hstartn
  have hCsn : Real.exp (Cs*Sn)≤M :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCsC hSn0)).trans hstartn
  have hcut : Real.log (⌊Q⌋₊:ℝ)≤δ*Real.sqrt (Real.log (M:ℝ)) :=
    iw_source_cutoff_of_exp hδ hδC hf.1
      (by exact_mod_cast (show 1≤M by omega))
      (by dsimp [Sn]; exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg r)
        (Real.log_nonneg (iwDenominatorBound_one_le hU k ⌊Q⌋₊)))) hstartn
  obtain ⟨E₀,hsmall,hp⟩ := hprime U hU hUe r k ⌊Q⌋₊ M hr hk hfQ hM du h25n hcut
  have hs := hsquare U hU hUe r k ⌊Q⌋₊ M hr hk hfQ hM du hEven hCsn
  dsimp only at hs
  refine ⟨E₀,hsmall,?_⟩
  intro f
  obtain ⟨gp,hgp,hpt,hpn⟩ := hp f
  obtain ⟨gs,hgs,hst,hsn⟩ := hs f
  refine ⟨gp,gs,hgp,hgs,?_,?_,?_⟩
  · simpa only [du,realIWHighData,ha] using hpt
  · simpa only [du,realIWHighData,ha] using hst
  · have hb := realIWFloor_quarter_power hQ2
    have hp' := hpn.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb hKp.le) (norm_nonneg f))
    have hs' := hsn.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb hKs.le) (norm_nonneg f))
    exact (add_le_add hp' hs').trans_eq (by dsimp [K]; ring)

end PrimeSquares


set_option autoImplicit false
open MeasureTheory
open scoped ENNReal lp Classical
namespace PrimeSquares

theorem realIWMaximalCost_nonneg {C Q : ℝ} (hC : 2 ≤ C) (hQ : 1 ≤ Q) (r k : ℕ) :
    0 ≤ realIWMaximalCost C r k Q := by
  unfold realIWMaximalCost
  apply mul_nonneg (by positivity)
  apply Real.log_nonneg
  have he : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hb := Real.log_nonneg (realIWDenominatorBound_one_le hC (by linarith : 0≤Q) k)
  nlinarith [mul_nonneg (Nat.cast_nonneg r) hb]

theorem iwPrime_low_from_measures {c C ρ : ℝ} (D : PagePrimeSquareDistributionInputs c)
    {k Q : ℕ} (d : TaoArcConstructionData C ρ k Q) [NeZero d.period]
    (a : ℝ) (ha : 2 ≤ a) {p : ℝ≥0∞} (hp : 1 ≤ p) {K : ℝ} (hK : 0 ≤ K)
    (Hlow : ∀ ν : ZMod d.period → ℂ, cyclicVariation d.period ν ≤ 1 →
      ∀ β : ℝ, 0 < β → β ≤ 1 →
      AllInputLpMaximalBound (fun j => iwAnnularLowOperator d.S k d.period ν ((2:ℕ)^j)
        (one_le_pow₀ (by norm_num)) β a ha) p K)
    (E₀ : Option PageZeroDatum) (hsmall : ∀ E,E₀=some E → E.conductor ≤ Q) :
    AllInputLpMaximalBound (fun j => iwPrimeLowOperator D (iwFrequencySet d.S k) ((2:ℕ)^j)
      (one_le_pow₀ (by norm_num)) a ha E₀ Q) p (2*K) := by
  intro f hf
  obtain ⟨GP,hGP0,hGPm,hGPdom,hGPn⟩ := Hlow (cyclicSquareMeasure d.period 1)
    (cyclicSquareMeasure_variation_le_one d.period 1) 1 (by norm_num) le_rfl f hf
  cases E₀ with
  | none =>
    refine ⟨GP,hGP0,hGPm,?_,hGPn.trans ?_⟩
    · intro j x
      simpa only [iwPrimeLowOperator_none D d] using hGPdom j x
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith : K≤2*K)) _
  | some E =>
    have hE := hsmall E rfl
    let χ := DirichletCharacter.changeLevel (iw_period_divisible_small d E.conductor_two hE) E.character
    obtain ⟨GE,hGE0,hGEm,hGEdom,hGEn⟩ := Hlow (cyclicSquareMeasure d.period χ)
      (cyclicSquareMeasure_variation_le_one d.period χ) E.beta E.beta_pos E.beta_lt_one.le f hf
    refine ⟨fun x => GP x+GE x,fun x => add_nonneg (hGP0 x) (hGE0 x),
      (hGPm.add hGEm).ae_eq (Filter.Eventually.of_forall (fun _ => rfl)),?_,?_⟩
    · intro j x
      exact (iwPrimeLowOperator_some_norm D d ((2:ℕ)^j) (one_le_pow₀ (by norm_num)) a ha E hE f x).trans
        (add_le_add (hGPdom j x) (hGEdom j x))
    · change eLpNorm (GP+GE) _ _ ≤ _
      calc
        _ ≤ eLpNorm GP _ _+eLpNorm GE _ _ := eLpNorm_add_le hp
        _ ≤ ENNReal.ofReal K*eLpNorm (f:ℤ→ℂ) _ _+ENNReal.ofReal K*eLpNorm (f:ℤ→ℂ) _ _ :=
          add_le_add hGPn hGEn
        _ = _ := by rw [←add_mul,←ENNReal.ofReal_add hK hK]; congr 2; ring

theorem real_iw_prime_low_maximal_bound {c C Q Z R H S : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hQ : 1 ≤ Q)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    {r k : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData (C^2) (iwRho k) k ⌊Q⌋₊) [NeZero d.period]
    (E₀ : Option PageZeroDatum) (hsmall : ∀ E,E₀=some E → E.conductor ≤ ⌊Q⌋₊)
    (ha : 2 ≤ realIWCutoffScale (C^2) r k Q) :
    AllInputLpMaximalBound (fun j => iwPrimeLowOperator D (iwFrequencySet d.S k) ((2:ℕ)^j)
      (one_le_pow₀ (by norm_num)) (realIWCutoffScale (C^2) r k Q) ha E₀ ⌊Q⌋₊)
      (ENNReal.ofReal (iwNearOneExponent r))
      (4*iwCompleteLowConstant Z R H S*realIWMaximalCost (C^2) r k Q) := by
  have hC2 : 2≤C^2 := by nlinarith
  have hcost := realIWMaximalCost_nonneg hC2 hQ r k
  have hp : (1:ℝ≥0∞)≤ENNReal.ofReal (iwNearOneExponent r) := by
    rw [←ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (iwNearOneExponent_bounds hr).1.le
  have hlow := iwPrime_low_from_measures D d _ ha hp
    (mul_nonneg (mul_nonneg (by norm_num) (iwCompleteLowConstant_pos hZ hR hH hS).le) hcost)
    (fun ν hν β hβ0 hβ1 => real_iw_full_low_maximal_bound hC hCe hQ hZ hR hH hS HIW HCZ HY HRM
      Hmajor HShannon HHL HRT hr hk d ν hν hβ0 hβ1 ha) E₀ hsmall
  convert hlow using 1; ring

theorem real_iw_full_square_low_maximal_bound {C Q Z R H S : ℝ}
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hQ : 1 ≤ Q)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    {r k : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData (C^2) (iwRho k) k ⌊Q⌋₊) [NeZero d.period]
    (ha : 2 ≤ realIWCutoffScale (C^2) r k Q) :
    AllInputLpMaximalBound (fun j => iwFullSquareLowOperator d.S k d.period ((2:ℕ)^j)
      (one_le_pow₀ (by norm_num)) (realIWCutoffScale (C^2) r k Q) ha)
      (ENNReal.ofReal (iwNearOneExponent r))
      (2*iwCompleteLowConstant Z R H S*realIWMaximalCost (C^2) r k Q) := by
  exact real_iw_full_low_maximal_bound hC hCe hQ hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
    hr hk d (cyclicFullSquareMeasure d.period) (cyclicFullSquareMeasure_variation_le_one d.period)
    (by norm_num) (by norm_num) ha

end PrimeSquares
