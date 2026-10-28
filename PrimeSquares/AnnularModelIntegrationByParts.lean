import PrimeSquares.ExceptionalProgressionDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Exact integration by parts on the positive quadratic annulus

Multiplication by -4*pi*i*theta avoids dividing by theta; the identity
therefore also holds at zero frequency. No endpoints or floor cutoffs change.
-/

open MeasureTheory

namespace PrimeSquares

noncomputable def quadraticPhaseSlope (θ : ℝ) : ℂ :=
  Complex.ofReal (-4 * Real.pi * θ) * Complex.I

noncomputable def annularBoundaryWeight (β t : ℝ) : ℂ :=
  Complex.ofReal (t^(β-2))

noncomputable def annularBoundaryDerivative (β t : ℝ) : ℂ :=
  Complex.ofReal ((β-2) * t^(β-3))

theorem annularBoundaryWeight_hasDerivAt (β : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (annularBoundaryWeight β) (annularBoundaryDerivative β t) t := by
  have he : β-2-1 = β-3 := by ring
  convert! (Real.hasDerivAt_rpow_const (x := t) (p := β-2)
    (Or.inl ht.ne')).ofReal_comp using 1
  simp only [annularBoundaryDerivative, he]

theorem annularBoundaryWeight_continuousOn (β : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (annularBoundaryWeight β) (Set.Icc a b) := by
  intro t ht
  exact (annularBoundaryWeight_hasDerivAt β (ha.trans_le ht.1)).continuousAt.continuousWithinAt

theorem annularBoundaryDerivative_continuousOn (β : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (annularBoundaryDerivative β) (Set.Icc a b) := by
  have hp := exceptionalDensity_continuousOn (β-2) (b := b) ha
  have he : β-2-1 = β-3 := by ring
  have hp' : ContinuousOn (fun t : ℝ => t^(β-3)) (Set.Icc a b) := by
    simpa only [he] using hp
  exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hp')

theorem annularBoundaryWeight_phase_derivative (β θ : ℝ) {t : ℝ} (ht : 0 < t) :
    annularBoundaryWeight β t * quadraticOscillationDerivative θ t =
      quadraticPhaseSlope θ *
        (Complex.ofReal (t^(β-1)) * quadraticOscillation θ t) := by
  have hp : t^(β-2) * t = t^(β-1) := by
    calc
      t^(β-2) * t = t^(β-2) * t^(1 : ℝ) := by rw [Real.rpow_one]
      _ = t^((β-2)+1) := (Real.rpow_add ht _ _).symm
      _ = _ := by congr 1; ring
  simp only [annularBoundaryWeight, quadraticOscillationDerivative, quadraticPhaseSlope]
  have hpc := congrArg Complex.ofReal hp
  push_cast at hpc
  calc
    _ = (Complex.ofReal (-4*Real.pi*θ) * Complex.I) *
        ((Complex.ofReal (t^(β-2)) * Complex.ofReal t) * quadraticOscillation θ t) := by
      push_cast
      ring
    _ = _ := by rw [hpc]

theorem annularBoundaryDerivative_intervalIntegrable {N : ℕ} (hN : 1 ≤ N) (β : ℝ) :
    IntervalIntegrable (annularBoundaryDerivative β) volume ((N : ℝ)/2) N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  exact (annularBoundaryDerivative_continuousOn β (by positivity)).intervalIntegrable_of_Icc
    (by linarith)

theorem annularOscillatory_integrationByParts {N : ℕ} (hN : 1 ≤ N) (β θ : ℝ) :
    quadraticPhaseSlope θ *
      (∫ t in (N : ℝ)/2..N, Complex.ofReal (t^(β-1)) * quadraticOscillation θ t) =
      annularBoundaryWeight β N * quadraticOscillation θ N -
      annularBoundaryWeight β ((N : ℝ)/2) * quadraticOscillation θ ((N : ℝ)/2) -
      ∫ t in (N : ℝ)/2..N, annularBoundaryDerivative β t * quadraticOscillation θ t := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hab : (N : ℝ)/2 ≤ N := by linarith
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (N : ℝ)/2) (b := (N : ℝ))
    (u := annularBoundaryWeight β) (u' := annularBoundaryDerivative β)
    (v := quadraticOscillation θ) (v' := quadraticOscillationDerivative θ)
    (by
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact annularBoundaryWeight_hasDerivAt β
        ((by positivity : (0 : ℝ) < (N : ℝ)/2).trans_le ht.1))
    (fun t _ => quadraticOscillation_hasDerivAt θ t)
    (annularBoundaryDerivative_intervalIntegrable hN β)
    (quadraticOscillationDerivative_intervalIntegrable θ _ _)
  have he :
      (∫ t in (N : ℝ)/2..N,
        annularBoundaryWeight β t * quadraticOscillationDerivative θ t) =
      quadraticPhaseSlope θ *
        ∫ t in (N : ℝ)/2..N, Complex.ofReal (t^(β-1)) * quadraticOscillation θ t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact annularBoundaryWeight_phase_derivative β θ
      ((by positivity : (0 : ℝ) < (N : ℝ)/2).trans_le ht.1)
  rw [he] at hparts
  exact hparts

end PrimeSquares
