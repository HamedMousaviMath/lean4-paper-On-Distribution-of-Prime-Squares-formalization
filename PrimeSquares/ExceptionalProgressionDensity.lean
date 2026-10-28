import PrimeSquares.ProgressionModelError
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The actual ordinary and exceptional progression densities

On a positive interval, differentiating x^beta/beta gives x^(beta-1).
The source oscillatory integrals are defined with their exact 1/N factor.
-/

open MeasureTheory

namespace PrimeSquares

noncomputable def exceptionalPrimitive (β t : ℝ) : ℝ := t^β / β

noncomputable def progressionPowerModel (q : ℕ) (z : ℂ) (β t : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ((t : ℂ) - z * Complex.ofReal (exceptionalPrimitive β t))

noncomputable def progressionPowerDensity (q : ℕ) (z : ℂ) (β t : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * (1 - z * Complex.ofReal (t^(β-1)))

noncomputable def annularOscillatoryModel (N : ℕ) (β θ : ℝ) : ℂ :=
  Complex.ofReal ((N : ℝ)⁻¹) *
    ∫ t in Set.Ioc ((N : ℝ)/2) N, Complex.ofReal (t^(β-1)) * quadraticOscillation θ t

theorem exceptionalPrimitive_hasDerivAt {β t : ℝ} (hβ : 0 < β) (ht : 0 < t) :
    HasDerivAt (exceptionalPrimitive β) (t^(β-1)) t := by
  convert (Real.hasDerivAt_rpow_const (x := t) (p := β) (Or.inl ht.ne')).div_const β using 1
  · rfl
  · field_simp [hβ.ne']

theorem exceptionalDensity_continuousOn (β : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => t^(β-1)) (Set.Icc a b) := by
  intro t ht
  exact (Real.continuousAt_rpow_const t (β-1) (Or.inl (ha.trans_le ht.1).ne')).continuousWithinAt

theorem progressionPowerModel_hasDerivAt (q : ℕ) (z : ℂ) {β t : ℝ}
    (hβ : 0 < β) (ht : 0 < t) :
    HasDerivAt (progressionPowerModel q z β) (progressionPowerDensity q z β t) t := by
  have hx : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have hp := (exceptionalPrimitive_hasDerivAt hβ ht).ofReal_comp
  exact (hx.sub (hp.const_mul z)).const_mul ((q.totient : ℂ)⁻¹)

theorem progressionPowerDensity_continuousOn (q : ℕ) (z : ℂ) (β : ℝ)
    {a b : ℝ} (ha : 0 < a) : ContinuousOn (progressionPowerDensity q z β) (Set.Icc a b) := by
  have hp := Complex.continuous_ofReal.comp_continuousOn
    (exceptionalDensity_continuousOn β (b := b) ha)
  exact continuousOn_const.mul (continuousOn_const.sub (continuousOn_const.mul hp))

theorem annularPowerModel_hasDerivAt {N : ℕ} (hN : 1 ≤ N) (q : ℕ) (z : ℂ)
    {β : ℝ} (hβ : 0 < β) :
    ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      HasDerivAt (progressionPowerModel q z β) (progressionPowerDensity q z β t) t := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  intro t ht
  exact progressionPowerModel_hasDerivAt q z hβ ((by positivity : (0 : ℝ) < (N : ℝ)/2).trans_le ht.1)

theorem annularPowerDensity_intervalIntegrable {N : ℕ} (hN : 1 ≤ N)
    (q : ℕ) (z : ℂ) (β : ℝ) :
    IntervalIntegrable (progressionPowerDensity q z β) volume ((N : ℝ)/2) N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact (progressionPowerDensity_continuousOn q z β (by positivity)).intervalIntegrable_of_Icc (by linarith)

theorem annularOscillatoryIntegrand_integrable {N : ℕ} (hN : 1 ≤ N) (β θ : ℝ) :
    IntegrableOn (fun t => Complex.ofReal (t^(β-1)) * quadraticOscillation θ t)
      (Set.Ioc ((N : ℝ)/2) N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp := Complex.continuous_ofReal.comp_continuousOn
    (exceptionalDensity_continuousOn β (a := (N : ℝ)/2) (b := N) (by positivity))
  exact (hp.mul (quadraticOscillation_continuous θ).continuousOn).integrableOn_Icc.mono_set
    Set.Ioc_subset_Icc_self

theorem annularOscillatoryModel_one (N : ℕ) (θ : ℝ) :
    annularOscillatoryModel N 1 θ = Complex.ofReal ((N : ℝ)⁻¹) *
      ∫ t in Set.Ioc ((N : ℝ)/2) N, quadraticOscillation θ t := by
  simp only [annularOscillatoryModel, sub_self, Real.rpow_zero, Complex.ofReal_one, one_mul]

theorem annularOscillatoryModel_interval (N : ℕ) (β θ : ℝ) :
    annularOscillatoryModel N β θ = Complex.ofReal ((N : ℝ)⁻¹) *
      ∫ t in (N : ℝ)/2..N, Complex.ofReal (t^(β-1)) * quadraticOscillation θ t := by
  have hab : (N : ℝ)/2 ≤ N := by nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  rw [annularOscillatoryModel, intervalIntegral.integral_of_le hab]

theorem annularOscillatoryModel_one_zero {N : ℕ} (hN : 1 ≤ N) :
    annularOscillatoryModel N 1 0 = (1/2 : ℂ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hab : (N : ℝ)/2 ≤ N := by linarith
  rw [annularOscillatoryModel_one, ← intervalIntegral.integral_of_le hab]
  simp only [quadraticOscillation, mul_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, intervalIntegral.integral_const, Complex.real_smul, mul_one]
  push_cast
  have hNz : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  field_simp [hNz]
  ring

theorem progressionPowerDensity_integral {N : ℕ} (hN : 1 ≤ N)
    (q : ℕ) (z : ℂ) (β θ : ℝ) :
    Complex.ofReal ((N : ℝ)⁻¹) * ∫ t in Set.Ioc ((N : ℝ)/2) N,
      quadraticOscillation θ t * progressionPowerDensity q z β t =
    (q.totient : ℂ)⁻¹ * (annularOscillatoryModel N 1 θ - z * annularOscillatoryModel N β θ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hab : (N : ℝ)/2 ≤ N := by linarith
  have hg : IntegrableOn (quadraticOscillation θ) (Set.Ioc ((N : ℝ)/2) N) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (quadraticOscillation_intervalIntegrable θ _ _)
  have hp := annularOscillatoryIntegrand_integrable hN β θ
  have hi : (∫ t in Set.Ioc ((N : ℝ)/2) N,
        quadraticOscillation θ t * progressionPowerDensity q z β t) =
      (q.totient : ℂ)⁻¹ * ((∫ t in Set.Ioc ((N : ℝ)/2) N, quadraticOscillation θ t) -
        z * ∫ t in Set.Ioc ((N : ℝ)/2) N, Complex.ofReal (t^(β-1)) * quadraticOscillation θ t) := by
    calc
      _ = ∫ t in Set.Ioc ((N : ℝ)/2) N, (q.totient : ℂ)⁻¹ *
          (quadraticOscillation θ t - z * (Complex.ofReal (t^(β-1)) * quadraticOscillation θ t)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => by unfold progressionPowerDensity; ring
      _ = _ := by rw [integral_const_mul, integral_sub hg (hp.const_mul z), integral_const_mul]
  rw [hi, annularOscillatoryModel_one, annularOscillatoryModel]
  ring

theorem progressionPowerModel_zero (q : ℕ) (β t : ℝ) :
    progressionPowerModel q 0 β t = (q.totient : ℂ)⁻¹ * (t : ℂ) := by
  simp only [progressionPowerModel, zero_mul, sub_zero]

end PrimeSquares
