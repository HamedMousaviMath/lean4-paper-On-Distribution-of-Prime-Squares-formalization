import PrimeSquares.ContinuousAnnularInitialIncrement
import PrimeSquares.RealLineFourierMultipliers
import PrimeSquares.AnnularCutoffSymbol

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

theorem allAnnularCutoff_norm_one {N : ℕ} (hN : 1≤N) {β : ℝ}
    (hβ0 : 0≤β) (hβ1 : β≤1) (a θ : ℝ) : ‖annularCutoffSymbol N hN β a θ‖≤1 := by
  change ‖annularOscillatoryModel N β θ*Complex.ofReal (sourceArcCutoff (a*θ))‖≤1
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sourceArcCutoff_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (sourceArcCutoff_le_one _) (norm_nonneg _)).trans
    (by simpa only [mul_one] using annularOscillatoryModel_norm_one hN hβ0 hβ1 θ)

noncomputable def allAnnularBoundedSymbol (N : ℕ) (hN : 1≤N) (β : ℝ)
    (hβ0 : 0≤β) (hβ1 : β≤1) (a : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (annularCutoffSymbol N hN β a)
    (annularCutoffSymbol N hN β a).continuous 1 (allAnnularCutoff_norm_one hN hβ0 hβ1 a)

theorem allAnnularBoundedSymbol_apply (N : ℕ) (hN : 1≤N) (β : ℝ)
    (hβ0 : 0≤β) (hβ1 : β≤1) (a θ : ℝ) :
    allAnnularBoundedSymbol N hN β hβ0 hβ1 a θ=
      annularOscillatoryModel N β θ*Complex.ofReal (sourceArcCutoff (a*θ)) := rfl

noncomputable def continuousAnnularSignedSymbol (β : ℝ) (hβ0 : 0≤β) (hβ1 : β≤1)
    (a : ℝ) (J : ℕ) (σ : ℕ → ℂ) : BoundedContinuousFunction ℝ ℂ :=
  ∑ j∈range J,σ j •
    (allAnnularBoundedSymbol ((2 : ℕ)^(j+1)) (one_le_pow₀ (by norm_num)) β hβ0 hβ1 a-
      allAnnularBoundedSymbol ((2 : ℕ)^j) (one_le_pow₀ (by norm_num)) β hβ0 hβ1 a)

theorem continuousAnnularSignedSymbol_apply (β : ℝ) (hβ0 : 0≤β) (hβ1 : β≤1)
    (a : ℝ) (J : ℕ) (σ : ℕ → ℂ) (θ : ℝ) :
    continuousAnnularSignedSymbol β hβ0 hβ1 a J σ θ=
      (∑ j∈range J,σ j*(annularOscillatoryModel ((2 : ℕ)^(j+1)) β θ-
        annularOscillatoryModel ((2 : ℕ)^j) β θ))*Complex.ofReal (sourceArcCutoff (a*θ)) := by
  unfold continuousAnnularSignedSymbol
  change (BoundedContinuousFunction.evalCLM ℂ θ) (∑ j∈range J,_) = _
  rw [map_sum,sum_mul]
  apply sum_congr rfl
  intro j _
  simp only [BoundedContinuousFunction.evalCLM_apply,BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.sub_apply,allAnnularBoundedSymbol_apply,smul_eq_mul]
  ring

theorem continuousAnnularSignedSymbol_norm {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1)
    (a : ℝ) (J : ℕ) (σ : ℕ → ℂ) (hσ : ∀ j∈range J,‖σ j‖≤1) (θ : ℝ) :
    ‖continuousAnnularSignedSymbol β hβ0.le hβ1 a J σ θ‖≤continuousAnnularIncrementConstant+2 := by
  rw [continuousAnnularSignedSymbol_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sourceArcCutoff_nonneg _)]
  exact ((mul_le_mul_of_nonneg_left (sourceArcCutoff_le_one _) (norm_nonneg _)).trans_eq (mul_one _)).trans
    (continuousAnnularSignedIncrement_one_start hβ0 hβ1 J σ hσ θ)

theorem continuousAnnularSignedSymbol_untruncated (β : ℝ) (hβ0 : 0≤β) (hβ1 : β≤1)
    (J : ℕ) (σ : ℕ → ℂ) (θ : ℝ) :
    continuousAnnularSignedSymbol β hβ0 hβ1 0 J σ θ=
      ∑ j∈range J,σ j*(annularOscillatoryModel ((2 : ℕ)^(j+1)) β θ-
        annularOscillatoryModel ((2 : ℕ)^j) β θ) := by
  rw [continuousAnnularSignedSymbol_apply,zero_mul,
    sourceArcCutoff_core (by norm_num : |(0 : ℝ)|≤1/2),Complex.ofReal_one,mul_one]

theorem continuousAnnularSignedMultiplier_opNorm {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1)
    (a : ℝ) (J : ℕ) (σ : ℕ → ℂ) (hσ : ∀ j∈range J,‖σ j‖≤1) :
    ‖realLineMultiplier (continuousAnnularSignedSymbol β hβ0.le hβ1 a J σ)‖≤
      continuousAnnularIncrementConstant+2 := by
  apply realLineMultiplier_opNorm_le_of_bound _
    (by have h := continuousAnnularIncrementConstant_pos;linarith)
  exact continuousAnnularSignedSymbol_norm hβ0 hβ1 a J σ hσ

theorem continuousAnnularSignedMultiplier_L2 {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1)
    (a : ℝ) (J : ℕ) (σ : ℕ → ℂ) (hσ : ∀ j∈range J,‖σ j‖≤1) (f : RealLineL2) :
    ‖realLineMultiplier (continuousAnnularSignedSymbol β hβ0.le hβ1 a J σ) f‖≤
      (continuousAnnularIncrementConstant+2)*‖f‖ :=
  ((realLineMultiplier _).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (continuousAnnularSignedMultiplier_opNorm hβ0 hβ1 a J σ hσ) (norm_nonneg _))

theorem realLpMultiplierBound_two_of_bound (m : BoundedContinuousFunction ℝ ℂ)
    {K : ℝ} (hK : 0≤K) (hm : ∀ θ,‖m θ‖≤K) : RealLpMultiplierBound 2 m K := by
  intro f _hf
  refine ⟨Lp.memLp _,?_⟩
  rw [←Lp.enorm_def,←Lp.enorm_def,←ofReal_norm,←ofReal_norm,←ENNReal.ofReal_mul hK]
  apply ENNReal.ofReal_le_ofReal
  exact ((realLineMultiplier m).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (realLineMultiplier_opNorm_le_of_bound m hK hm) (norm_nonneg _))

theorem continuousAnnularSignedMultiplier_Lp_two {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1)
    (a : ℝ) (J : ℕ) (σ : ℕ → ℂ) (hσ : ∀ j∈range J,‖σ j‖≤1) :
    RealLpMultiplierBound 2 (continuousAnnularSignedSymbol β hβ0.le hβ1 a J σ)
      (continuousAnnularIncrementConstant+2) :=
  realLpMultiplierBound_two_of_bound _ (by have h := continuousAnnularIncrementConstant_pos;linarith)
    (continuousAnnularSignedSymbol_norm hβ0 hβ1 a J σ hσ)

end PrimeSquares
