import PrimeSquares.AnnularModelDecay
import PrimeSquares.SourceArcCutoff
import PrimeSquares.TwistedGaussBound

/-!
# Actual ordinary and exceptional Gauss-model tail bounds

All Gauss estimates consumed here are already proved unconditionally in this
project. The frequency decay is for the genuine normalized annular integral.
-/

namespace PrimeSquares

noncomputable def annularGaussModel (N q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (κ : ℂ) (β : ℝ) (a : ZMod q) (θ : ℝ) : ℂ :=
  principalSquareSum q a * annularOscillatoryModel N 1 θ -
    twistedSquareSum q χ a * (κ * annularOscillatoryModel N β θ)

noncomputable def localizedAnnularGaussModel (N q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (κ : ℂ) (β : ℝ) (a : ZMod q) (s : ℕ) (θ : ℝ) : ℂ :=
  annularGaussModel N q χ κ β a θ * Complex.ofReal (sourceArcCutoffScale s θ)

theorem annularGaussModel_ordinary (N q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (β : ℝ) (a : ZMod q) (θ : ℝ) :
    annularGaussModel N q χ 0 β a θ =
      principalSquareSum q a * annularOscillatoryModel N 1 θ := by
  simp only [annularGaussModel, zero_mul, mul_zero, sub_zero]

theorem annularGaussModel_norm_from_bounds (N q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (κ : ℂ) (β : ℝ) (a : ZMod q) (θ : ℝ)
    {B L : ℝ} (hB : 0 ≤ B)
    (hp : ‖principalSquareSum q a‖ ≤ B) (ht : ‖twistedSquareSum q χ a‖ ≤ B)
    (hκ : ‖κ‖ ≤ 1)
    (hm1 : ‖annularOscillatoryModel N 1 θ‖ ≤ L)
    (hmβ : ‖annularOscillatoryModel N β θ‖ ≤ L) :
    ‖annularGaussModel N q χ κ β a θ‖ ≤ 2*B*L := by
  have hk : ‖κ * annularOscillatoryModel N β θ‖ ≤ L := by
    rw [norm_mul]
    exact (mul_le_mul hκ hmβ (norm_nonneg _) (by norm_num)).trans (by simp)
  calc
    _ ≤ ‖principalSquareSum q a * annularOscillatoryModel N 1 θ‖ +
        ‖twistedSquareSum q χ a * (κ * annularOscillatoryModel N β θ)‖ :=
      norm_sub_le _ _
    _ ≤ B*L + B*L := add_le_add
      (by rw [norm_mul]; exact mul_le_mul hp hm1 (norm_nonneg _) hB)
      (by rw [norm_mul]; exact mul_le_mul ht hk (norm_nonneg _) hB)
    _ = _ := by ring

theorem gauss_tail_power_budget {q R : ℝ} (hq : 0 < q) (hqR : q ≤ R) :
    q^(-(5/12 : ℝ)) * q / R ≤ R^(-(5/12 : ℝ)) := by
  have hR : 0 < R := hq.trans_le hqR
  have hp : q^(-(5/12 : ℝ))*q = q^(7/12 : ℝ) := by
    calc
      _ = q^(-(5/12 : ℝ))*q^(1 : ℝ) := by rw [Real.rpow_one]
      _ = q^(-(5/12 : ℝ)+1) := (Real.rpow_add hq _ _).symm
      _ = _ := by norm_num
  rw [hp]
  calc
    _ ≤ R^(7/12 : ℝ)/R :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow hq.le hqR (by norm_num)) hR.le
    _ = R^(7/12 : ℝ)/R^(1 : ℝ) := by rw [Real.rpow_one]
    _ = R^((7/12 : ℝ)-1) := (Real.rpow_sub hR _ _).symm
    _ = _ := by norm_num

theorem annularGaussModel_uniform_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (N q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q) (κ : ℂ) (β : ℝ) (a : ZMod q),
      2 ≤ N → 0 ≤ β → β ≤ 1 → IsUnit a → ‖κ‖ ≤ 1 →
      (∀ θ : ℝ, ‖annularGaussModel N q χ κ β a θ‖ ≤ C*(q : ℝ)^(-(5/12 : ℝ))) ∧
      (∀ R : ℝ, (q : ℝ) ≤ R → ∀ θ : ℝ,
        R/((q : ℝ)*(N : ℝ)^2) ≤ |θ| →
        ‖annularGaussModel N q χ κ β a θ‖ ≤ (4*C/Real.pi)*R^(-(5/12 : ℝ))) := by
  obtain ⟨C, hC, hc⟩ := twistedSquareSum_uniform_bound (1/12) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro N q inst χ κ β a hN hβ0 hβ1 ha hκ
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have he : -(1/2 : ℝ)+1/12 = -(5/12 : ℝ) := by norm_num
  have hp : ‖principalSquareSum q a‖ ≤ C*(q : ℝ)^(-(5/12 : ℝ)) := by
    simpa only [twistedSquareSum_principal, he] using hc q 1 a ha
  have ht : ‖twistedSquareSum q χ a‖ ≤ C*(q : ℝ)^(-(5/12 : ℝ)) := by
    simpa only [he] using hc q χ a ha
  constructor
  · intro θ
    have h := annularGaussModel_norm_from_bounds N q χ κ β a θ
      (B := C*(q : ℝ)^(-(5/12 : ℝ))) (L := 1/2)
      (mul_nonneg hC.le (Real.rpow_nonneg hq.le _))
      hp ht hκ (annularOscillatoryModel_norm_half hN (by norm_num) θ)
      (annularOscillatoryModel_norm_half hN hβ1 θ)
    nlinarith only [h]
  · intro R hqR θ hθ
    have hR : 0 < R := hq.trans_le hqR
    have h := annularGaussModel_norm_from_bounds N q χ κ β a θ
      (B := C*(q : ℝ)^(-(5/12 : ℝ))) (L := 2*(q : ℝ)/(Real.pi*R))
      (mul_nonneg hC.le (Real.rpow_nonneg hq.le _))
      hp ht hκ (annularOscillatoryModel_outside_arc hN (by norm_num) (by norm_num) hq hR hθ)
      (annularOscillatoryModel_outside_arc hN hβ0 hβ1 hq hR hθ)
    calc
      _ ≤ 2*(C*(q : ℝ)^(-(5/12 : ℝ)))*(2*(q : ℝ)/(Real.pi*R)) := h
      _ = (4*C/Real.pi)*((q : ℝ)^(-(5/12 : ℝ))*(q : ℝ)/R) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (gauss_tail_power_budget hq hqR) (by positivity)

theorem localizedAnnularGaussModel_norm_le (N q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (κ : ℂ) (β : ℝ) (a : ZMod q) (s : ℕ) (θ : ℝ) :
    ‖localizedAnnularGaussModel N q χ κ β a s θ‖ ≤
      ‖annularGaussModel N q χ κ β a θ‖ := by
  rw [localizedAnnularGaussModel, norm_mul, Complex.norm_real, Real.norm_eq_abs, sourceArcCutoffScale,
    abs_of_nonneg (sourceArcCutoff_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (sourceArcCutoff_le_one _) (norm_nonneg _)).trans (by simp)

end PrimeSquares
