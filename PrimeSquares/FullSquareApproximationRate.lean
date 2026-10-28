import PrimeSquares.FullSquareCircleError
import PrimeSquares.SourceModelLogarithmicRate
import PrimeSquares.MajorArcBudgetGeometry

set_option autoImplicit false
open Filter
open scoped Topology
namespace PrimeSquares

noncomputable def fullSquareLogCost (E R : ℝ) : ℝ :=
  (6*quadraticIntegralConstant+16*E+100/Real.pi+
    (20/(Real.pi*Real.log 2))*Real.log R)*R^(-(1/2 : ℝ))

theorem fullSquareApproxBudget_log_bound {E R : ℝ} (hE : 0 ≤ E) {N : ℕ}
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hRN : R ≤ (N : ℝ)) :
    fullSquareApproxBudget E N R ≤ fullSquareLogCost E R := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R := by linarith
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hRp
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNp
  have hsR2 := Real.sq_sqrt hRp.le
  have hroot : Real.sqrt R/(N : ℝ) ≤ 1/Real.sqrt R := by
    apply (div_le_div_iff₀ hNp hsR).mpr
    simpa only [one_mul, ←pow_two, hsR2] using hRN
  have hmajor : 4*E*Real.sqrt R/(N : ℝ) ≤ 4*E/Real.sqrt R := by
    have h := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 4*E by positivity)
    simpa only [div_eq_mul_inv, mul_assoc, one_mul] using h
  have hminor : 12*E/Real.sqrt (N : ℝ) ≤ 12*E/Real.sqrt R :=
    div_le_div_of_nonneg_left (by positivity) hsR (Real.sqrt_le_sqrt hRN)
  calc
    _ ≤ 4*E/Real.sqrt R+6*quadraticIntegralConstant/Real.sqrt R+
        12*E/Real.sqrt R+5*fullSquareRealTailBudget R := by
      unfold fullSquareApproxBudget
      linarith
    _ = _ := by
      unfold fullSquareLogCost fullSquareRealTailBudget
      rw [Real.rpow_neg hRp.le, ←Real.sqrt_eq_rpow]
      have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
      field_simp
      ring

theorem eventually_fullSquareLogCost (E : ℝ) :
    ∀ᶠ R : ℝ in atTop, fullSquareLogCost E R ≤ R^(-(1/6 : ℝ)) := by
  have h := eventually_affine_log_le_rpow (6*quadraticIntegralConstant+16*E+100/Real.pi)
    (20/(Real.pi*Real.log 2)) (by norm_num : (0 : ℝ) < 1/3)
  filter_upwards [eventually_gt_atTop (0 : ℝ), h] with R hR hbound
  calc
    _ ≤ R^(1/3 : ℝ)*R^(-(1/2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hR.le _)
    _ = _ := by rw [←Real.rpow_add hR]; norm_num

theorem fullSquareLogCost_uniform (E : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      fullSquareLogCost E (sourceMajorArcScale N Q) ≤
        4*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-(2 : ℝ)) := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp (eventually_fullSquareLogCost E)
  obtain ⟨N₁, hN₁⟩ := sourceMajorArcScale_uniform_lower B
  obtain ⟨N₂, hN₂⟩ := sourceMajorArcScale_logarithmic_rate (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN Q hQ
  have h := (hB _ (hN₁ N ((le_max_left _ _).trans hN) Q)).trans
    (hN₂ N ((le_max_right _ _).trans hN) Q hQ)
  norm_num only [Real.rpow_two] at h
  exact h

theorem sourceFullSquare_arc_conditions :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (1/8 : ℝ)*Real.sqrt (Real.log N) →
      1 ≤ sourceMajorArcScale N Q ∧ 32*sourceMajorArcScale N Q ≤ (N : ℝ) ∧
      2*(sourceMajorArcScale N Q)^3 < (N : ℝ)^2 ∧
      2*(sourceMajorArcScale N Q)^4 ≤ (N : ℝ)^2 := by
  obtain ⟨N₁, _hN₁, hp⟩ := sourceMajorArc_parameter_threshold (by norm_num : (0 : ℝ) < 7)
  obtain ⟨N₂, _hN₂, hg⟩ := sourceMajorArc_uniform_geometry (by norm_num : (0 : ℝ) < 7)
  let N₀ := max N₁ (max N₂ (max ⌈Real.exp 1⌉₊ 1024))
  refine ⟨N₀, by dsimp [N₀]; omega, ?_⟩
  intro N hN Q hQ hcut
  have hn1 : N₁ ≤ N := (le_max_left _ _).trans hN
  have hn2 : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hceil : ⌈Real.exp 1⌉₊ ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hn1024 : 1024 ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcut' : Real.log Q ≤ (min ((7 : ℝ)/7) 1 /8)*Real.sqrt (Real.log N) := by norm_num; exact hcut
  obtain ⟨hR, _hlog, hbudget, _hexp⟩ := hp N hn1 Q hQ hcut'
  obtain ⟨hsep, hcore⟩ := hg N hn2 Q hQ hcut'
  have hEN : Real.exp 1 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hlogN : 1 ≤ Real.log (N : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hEN
  let R := sourceMajorArcScale N Q
  have hR0 : 0 ≤ R := by dsimp [R]; linarith
  have hpow : R ≤ R^5 := le_self_pow₀ hR (by decide)
  have hpow' : R^5 ≤ R^5*Real.log (N : ℝ) := le_mul_of_one_le_right (by positivity) hlogN
  have hroot : R ≤ Real.sqrt (N : ℝ) := hpow.trans (hpow'.trans hbudget)
  have hs2 := Real.sq_sqrt hNp.le
  have hs0 := Real.sqrt_nonneg (N : ℝ)
  have hnR : (1024 : ℝ) ≤ N := by exact_mod_cast hn1024
  have hs32 : 32 ≤ Real.sqrt (N : ℝ) := by nlinarith
  have hrootN : 32*Real.sqrt (N : ℝ) ≤ (N : ℝ) := by nlinarith
  exact ⟨hR, (mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 32)).trans hrootN, hsep, hcore⟩

theorem fullSquareCircleError_uniform {E : ℝ} (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (1/8 : ℝ)*Real.sqrt (Real.log N) → ∀ hN : 1 ≤ N, ∀ θ : PrimeCircle,
      ‖fullSquareCircleError (sourceRationalCenters (sourceMajorArcScale N Q)) N hN θ‖ ≤
        4*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-(2 : ℝ)) := by
  obtain ⟨N₁, hN₁, hgeom⟩ := sourceFullSquare_arc_conditions
  obtain ⟨N₂, hcost⟩ := fullSquareLogCost_uniform E
  refine ⟨max N₁ N₂, by omega, ?_⟩
  intro N hn hEven Q hQ hcut hN θ
  have hn1 : N₁ ≤ N := (le_max_left _ _).trans hn
  have hn2 : N₂ ≤ N := (le_max_right _ _).trans hn
  obtain ⟨hR, hNR, hsep, hcore⟩ := hgeom N hn1 Q hQ hcut
  have hRN : sourceMajorArcScale N Q ≤ (N : ℝ) := by linarith
  obtain ⟨M, rfl⟩ := hEven.two_dvd
  have hM : 1 ≤ M := by omega
  exact (fullSquareCircleError_bound hE HE hM hR hNR hsep hcore θ).trans
    ((fullSquareApproxBudget_log_bound hE hN hR hRN).trans (hcost _ hn2 Q hQ))

end PrimeSquares
