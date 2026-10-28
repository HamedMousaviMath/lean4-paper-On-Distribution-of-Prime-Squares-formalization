import PrimeSquares.GoldbachCountingPartialSummation
import PrimeSquares.RealFourierPhase

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

noncomputable def goldbachSquareIntegral (U γ : ℝ) : ℂ :=
  ∫ t in Set.Ioc 2 U,quadraticOscillation (-γ) t*((Real.log t)⁻¹:ℝ)

noncomputable def goldbachLinearIntegral (U β : ℝ) : ℂ :=
  ∫ t in Set.Ioc 2 U,realFourierPhase (β*t)*((Real.log t)⁻¹:ℝ)

noncomputable def goldbachLinearDerivative (β t : ℝ) : ℂ :=
  realFourierPhase (β*t)*(Complex.ofReal (2*Real.pi*β)*Complex.I)

theorem goldbach_linear_hasDerivAt (β t : ℝ) :
    HasDerivAt (fun x => realFourierPhase (β*x)) (goldbachLinearDerivative β t) t := by
  have h : HasDerivAt (fun x : ℝ => 2*Real.pi*(β*x)) (2*Real.pi*β) t := by
    simpa only [id_eq,mul_one] using
      ((hasDerivAt_id t).const_mul β).const_mul (2*Real.pi)
  exact (h.ofReal_comp.mul_const Complex.I).cexp

theorem goldbachLinearDerivative_continuous (β : ℝ) : Continuous (goldbachLinearDerivative β) := by
  unfold goldbachLinearDerivative
  exact (realFourierPhase_continuous.comp (by fun_prop)).mul continuous_const

theorem goldbachLinearDerivative_norm (β t : ℝ) :
    ‖goldbachLinearDerivative β t‖=2*Real.pi*|β| := by
  simp only [goldbachLinearDerivative,norm_mul,realFourierPhase_norm,one_mul,
    Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0:ℝ)≤2),abs_of_pos Real.pi_pos]

theorem goldbach_square_density_integral (k : ℕ) (U γ : ℝ) :
    (∫ t in Set.Ioc 2 U,quadraticOscillation (-γ) t*goldbachPrimeProgressionDensity k t)=
      (k.totient:ℂ)⁻¹*goldbachSquareIntegral U γ := by
  unfold goldbachPrimeProgressionDensity goldbachSquareIntegral
  rw [←integral_const_mul]
  congr 1
  ext t
  ring

theorem goldbach_linear_density_integral (k : ℕ) (U β : ℝ) :
    (∫ t in Set.Ioc 2 U,realFourierPhase (β*t)*goldbachPrimeProgressionDensity k t)=
      (k.totient:ℂ)⁻¹*goldbachLinearIntegral U β := by
  unfold goldbachPrimeProgressionDensity goldbachLinearIntegral
  rw [←integral_const_mul]
  congr 1
  ext t
  ring

theorem goldbach_prime_quadratic_count_error (k a : ℕ) {U B : ℝ}
    (hU : 2≤U) (hB : 0≤B) (γ : ℝ)
    (herr : ∀ t∈Set.Icc 2 U,
      ‖(goldbachPrimeProgressionCount k a t:ℂ)-goldbachPrimeProgressionModel k t‖≤B) :
    ‖(∑ n∈goldbachPrimeProgressionCutoff k a U,quadraticOscillation (-γ) n)-
      (k.totient:ℂ)⁻¹*goldbachSquareIntegral U γ‖≤B*(1+4*Real.pi*|γ| *U^2) := by
  have hU0 : 0≤U := by linarith
  have hD : 0≤4*Real.pi*|γ| *U := by positivity
  have h := goldbach_prime_progression_partial_error k a hU hB hD
    (quadraticOscillation (-γ)) (quadraticOscillationDerivative (-γ))
    (quadraticOscillation_hasDerivAt (-γ)) (quadraticOscillationDerivative_continuous (-γ))
    (by rw [quadraticOscillation_norm])
    (fun t ht => by simpa only [abs_neg] using
      quadraticOscillationDerivative_bound (-γ) (by linarith [ht.1]) ht.2) herr
  rw [goldbach_square_density_integral] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hB
  have hp : 0≤4*Real.pi*|γ| := by positivity
  nlinarith

theorem goldbach_prime_linear_count_error (k a : ℕ) {U B : ℝ}
    (hU : 2≤U) (hB : 0≤B) (β : ℝ)
    (herr : ∀ t∈Set.Icc 2 U,
      ‖(goldbachPrimeProgressionCount k a t:ℂ)-goldbachPrimeProgressionModel k t‖≤B) :
    ‖(∑ n∈goldbachPrimeProgressionCutoff k a U,realFourierPhase (β*n))-
      (k.totient:ℂ)⁻¹*goldbachLinearIntegral U β‖≤B*(1+2*Real.pi*|β| *U) := by
  have hD : 0≤2*Real.pi*|β| := by positivity
  have h := goldbach_prime_progression_partial_error k a hU hB hD
    (fun t => realFourierPhase (β*t)) (goldbachLinearDerivative β)
    (goldbach_linear_hasDerivAt β) (goldbachLinearDerivative_continuous β)
    (by rw [realFourierPhase_norm])
    (fun t _ => (goldbachLinearDerivative_norm β t).le) herr
  rw [goldbach_linear_density_integral] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hB
  nlinarith

end PrimeSquares
