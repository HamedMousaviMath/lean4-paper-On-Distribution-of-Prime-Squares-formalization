import PrimeSquares.QuadraticOscillation
import Mathlib.NumberTheory.AbelSummation

/-!
# Abel summation for the actual progression von Mangoldt sum

Natural floor endpoints are retained. The annular specialization uses the
real lower endpoint N/2 and proves its exact agreement with the natural
cutoff, including odd N and the zero cutoff.
-/

open Finset MeasureTheory

namespace PrimeSquares

noncomputable def progressionMangoldtCoeff (q : ℕ) (r : ZMod q) (n : ℕ) : ℂ :=
  if (n : ZMod q) = r then (ArithmeticFunction.vonMangoldt n : ℂ) else 0

noncomputable def progressionMangoldtPrefix (q : ℕ) (r : ZMod q) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 0 ⌊x⌋₊, progressionMangoldtCoeff q r n

theorem progressionMangoldtCoeff_zero (q : ℕ) (r : ZMod q) :
    progressionMangoldtCoeff q r 0 = 0 := by
  simp [progressionMangoldtCoeff]

theorem progressionMangoldtPrefix_zero (q : ℕ) (r : ZMod q) :
    progressionMangoldtPrefix q r 0 = 0 := by
  simp [progressionMangoldtPrefix, progressionMangoldtCoeff_zero]

theorem squareResidueSum_as_coeff (S : Finset ℕ) (q : ℕ) (r : ZMod q) (θ : ℝ) :
    squareResidueSum S q r ArithmeticFunction.vonMangoldt (θ : PrimeCircle) =
      ∑ n ∈ S, quadraticOscillation θ n * progressionMangoldtCoeff q r n := by
  classical
  simp only [squareResidueSum, sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases h : (n : ZMod q) = r
  · rw [ite_eq_left h, progressionMangoldtCoeff, ite_eq_left h, quadraticOscillation_nat]
    exact mul_comm _ _
  · rw [ite_eq_right h, progressionMangoldtCoeff, ite_eq_right h, mul_zero]

theorem progression_quadratic_abel (q : ℕ) (r : ZMod q) (θ : ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, quadraticOscillation θ n * progressionMangoldtCoeff q r n) =
      quadraticOscillation θ b * progressionMangoldtPrefix q r b -
      quadraticOscillation θ a * progressionMangoldtPrefix q r a -
      ∫ t in Set.Ioc a b, quadraticOscillationDerivative θ t * progressionMangoldtPrefix q r t := by
  have h := sum_mul_eq_sub_sub_integral_mul (progressionMangoldtCoeff q r) ha hab
    (fun t _ => (quadraticOscillation_hasDerivAt θ t).differentiableAt)
    (by rw [quadraticOscillation_deriv]; exact (quadraticOscillationDerivative_continuous θ).integrableOn_Icc)
  simpa only [quadraticOscillation_deriv, progressionMangoldtPrefix] using h

theorem squareResidueSum_abel (q : ℕ) (r : ZMod q) (θ : ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    squareResidueSum (Ioc ⌊a⌋₊ ⌊b⌋₊) q r ArithmeticFunction.vonMangoldt (θ : PrimeCircle) =
      quadraticOscillation θ b * progressionMangoldtPrefix q r b -
      quadraticOscillation θ a * progressionMangoldtPrefix q r a -
      ∫ t in Set.Ioc a b, quadraticOscillationDerivative θ t * progressionMangoldtPrefix q r t := by
  rw [squareResidueSum_as_coeff]
  exact progression_quadratic_abel q r θ ha hab

theorem annularMangoldtResidue_abel (N q : ℕ) (r : ZMod q) (θ : ℝ) :
    squareResidueSum (Ioc (N/2) N) q r ArithmeticFunction.vonMangoldt (θ : PrimeCircle) =
      quadraticOscillation θ N * progressionMangoldtPrefix q r N -
      quadraticOscillation θ ((N : ℝ)/2) * progressionMangoldtPrefix q r ((N : ℝ)/2) -
      ∫ t in Set.Ioc ((N : ℝ)/2) N,
        quadraticOscillationDerivative θ t * progressionMangoldtPrefix q r t := by
  have h := squareResidueSum_abel q r θ
    (a := (N : ℝ)/2) (b := N) (by positivity)
    (by nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
  have hf : ⌊(N : ℝ)/2⌋₊ = N/2 := by
    exact Nat.floor_div_eq_div N 2
  simpa only [hf, Nat.floor_natCast] using h

end PrimeSquares
