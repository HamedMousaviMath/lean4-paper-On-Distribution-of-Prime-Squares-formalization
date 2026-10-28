import PrimeSquares.FullSquareApproximationMaximum
import PrimeSquares.IWFullSquareLowComparison
import PrimeSquares.IWPrimeHighSourceScale

set_option autoImplicit false
open scoped lp
namespace PrimeSquares

theorem iwFullSquareHigh_error_model (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 2 ≤ a) (Q : ℝ) :
    iwFullSquareHighOperator S k P N hN a ha = fullSquareCircleErrorOperator N hN Q+
      (integerMultiplier (varyingIndexAnnularBlock (sourceRationalCenters (sourceMajorArcScale N Q))
        N hN 1 rationalFullSquareGauss)-iwFullSquareLowOperator S k P N hN a ha) := by
  rw [fullSquareCircleErrorOperator_eq]
  unfold iwFullSquareHighOperator
  abel

def IWFullSquareHighBound (C : ℝ) (r k Q M : ℕ) (hC : 2 ≤ C) (hr : 2 ≤ r)
    (hM : 2 ≤ M) (K : ℝ) : Prop :=
  ∃ d : TaoArcConstructionData C (iwRho k) k Q,
    IWGood r k d.S (iwWidth C r k Q) ∧
    (∀ t ∈ iwFrequencySet d.S k, (t.den : ℝ) ≤ iwDenominatorBound C k Q) ∧
    (letI : NeZero d.period := ⟨d.period_pos.ne'⟩
      ∀ f : ℓ²(ℤ,ℂ), ∃ g : lp (fun _ : ℤ => ℝ) 2, (∀ x, 0 ≤ g x) ∧
        (∀ j x, ‖iwFullSquareHighOperator d.S k d.period ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j; omega) (iwCutoffScale C r k Q)
          (by have h := iwCutoffScale_four_le hC hr k Q; linarith) f x‖ ≤ g x) ∧
        ‖g‖ ≤ K*(Q : ℝ)^(-(1/4 : ℝ))*‖f‖)

theorem iw_full_square_high_source_scale {Cb E : ℝ} (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E) :
    ∃ Cstart K : ℝ, 0 < Cstart ∧ 0 < K ∧ ∀ (C : ℝ) (hC : 2 ≤ C), Real.exp 1 ≤ C →
      RawTaoArcConstructionInput C → ∀ (r k Q M : ℕ) (hr : 2 ≤ r), 4 ≤ k → 2^k ≤ Q →
      ∀ hM : 2 ≤ M, Even M →
      Real.exp (Cstart*((Real.log (Q : ℝ))^2+(r : ℝ)*Real.log (iwDenominatorBound C k Q))) ≤ M →
      IWFullSquareHighBound C r k Q M hC hr hM K := by
  obtain ⟨N₀, hN₀, hError⟩ := full_square_approximation_maximum hE HE
  let Cstart := max 64 (max 25 (Real.log ((N₀ : ℝ)+1)))
  let K := iwFullSquareModelConstant Cb+fullSquareErrorMaximalConstant
  have h64 : (64 : ℝ) ≤ Cstart := le_max_left _ _
  have h25 : (25 : ℝ) ≤ Cstart := (le_max_left _ _).trans (le_max_right _ _)
  have hlogStart : Real.log ((N₀ : ℝ)+1) ≤ Cstart := (le_max_right _ _).trans (le_max_right _ _)
  have hCstart : 0 < Cstart := by linarith
  have hK : 0 < K := add_pos (iwFullSquareModelConstant_pos hCb) fullSquareErrorMaximalConstant_pos
  refine ⟨Cstart, K, hCstart, hK, ?_⟩
  intro C hC hCe HT r k Q M hr hk hQ hM hEven hstart
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
  obtain ⟨d, hGood, hden⟩ := quantitative_iw_construction_good hC HT hr hk hQ
  let : NeZero d.period := ⟨d.period_pos.ne'⟩
  have hbudget := iw_starting_budget_of_source_scale hC hCe hr hk hQ1nat hM hstart25
  let R := fun j => sourceMajorArcScale (((2 : ℕ)^j*M : ℕ) : ℝ) (Q : ℝ)
  have hR : ∀ j, (Q : ℝ) ≤ R j := fun j => sourceMajorArcScale_cutoff_le hQ1 _
  refine ⟨d, hGood, hden, ?_⟩
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
