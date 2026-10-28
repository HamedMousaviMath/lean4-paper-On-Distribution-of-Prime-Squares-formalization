import PrimeSquares.SquareResidueGrouping

/-!
# The real quadratic oscillation used in partial summation

This is the actual negative phase at real t, with its exact real derivative,
unit norm, continuity and uniform derivative bound on a nonnegative interval.
-/

namespace PrimeSquares

noncomputable def quadraticOscillation (θ t : ℝ) : ℂ :=
  Complex.exp (Complex.ofReal (-2 * Real.pi * θ * t^2) * Complex.I)

noncomputable def quadraticOscillationDerivative (θ t : ℝ) : ℂ :=
  quadraticOscillation θ t * (Complex.ofReal (-4 * Real.pi * θ * t) * Complex.I)

theorem quadraticOscillation_norm (θ t : ℝ) : ‖quadraticOscillation θ t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem quadraticOscillation_nat (θ : ℝ) (n : ℕ) :
    quadraticOscillation θ n = negativeFourierCharacter ((n : ℤ)^2) (θ : PrimeCircle) := by
  rw [quadraticOscillation, negativeFourierCharacter_real]
  congr 1
  push_cast
  ring

theorem quadraticOscillation_hasDerivAt (θ t : ℝ) :
    HasDerivAt (quadraticOscillation θ) (quadraticOscillationDerivative θ t) t := by
  have h : HasDerivAt (fun x : ℝ => -2 * Real.pi * θ * x^2)
      (-4 * Real.pi * θ * t) t := by
    convert ((hasDerivAt_id t).pow 2).const_mul (-2 * Real.pi * θ) using 1
    · rfl
    · dsimp
      ring
  exact (h.ofReal_comp.mul_const Complex.I).cexp

theorem quadraticOscillation_deriv (θ : ℝ) :
    deriv (quadraticOscillation θ) = quadraticOscillationDerivative θ := by
  funext t
  exact (quadraticOscillation_hasDerivAt θ t).deriv

theorem quadraticOscillation_continuous (θ : ℝ) : Continuous (quadraticOscillation θ) := by
  unfold quadraticOscillation
  fun_prop

theorem quadraticOscillationDerivative_continuous (θ : ℝ) :
    Continuous (quadraticOscillationDerivative θ) := by
  unfold quadraticOscillationDerivative
  exact (quadraticOscillation_continuous θ).mul (by fun_prop)

theorem quadraticOscillationDerivative_norm (θ t : ℝ) :
    ‖quadraticOscillationDerivative θ t‖ = 4 * Real.pi * |θ| * |t| := by
  simp only [quadraticOscillationDerivative, norm_mul, quadraticOscillation_norm,
    Complex.norm_I, mul_one, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos Real.pi_pos]
  norm_num

theorem quadraticOscillationDerivative_bound (θ : ℝ) {t N : ℝ}
    (ht : 0 ≤ t) (htN : t ≤ N) :
    ‖quadraticOscillationDerivative θ t‖ ≤ 4 * Real.pi * |θ| * N := by
  rw [quadraticOscillationDerivative_norm, abs_of_nonneg ht]
  exact mul_le_mul_of_nonneg_left htN (by positivity)

theorem quadraticOscillation_intervalIntegrable (θ a b : ℝ) :
    IntervalIntegrable (quadraticOscillation θ) MeasureTheory.volume a b :=
  (quadraticOscillation_continuous θ).intervalIntegrable a b

theorem quadraticOscillationDerivative_intervalIntegrable (θ a b : ℝ) :
    IntervalIntegrable (quadraticOscillationDerivative θ) MeasureTheory.volume a b :=
  (quadraticOscillationDerivative_continuous θ).intervalIntegrable a b

end PrimeSquares
