import PrimeSquares.PositiveAverageMaximum
import PrimeSquares.TheoremOneOne
import Mathlib.NumberTheory.PrimeCounting

open Finset
namespace PrimeSquares

noncomputable def mangoldtPositiveFamily : PositiveAverageFamily where
  indices n := Ioc 0 (n+2)
  shift j := (j : ℤ)^2
  weight n j := ((n+2 : ℕ) : ℝ)⁻¹*ArithmeticFunction.vonMangoldt j
  mass := primeSquareChebyshevConstant
  mass_one_le := by
    unfold primeSquareChebyshevConstant
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ)≤4)]
  nonnegative _ _ _ := mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg
  mass_bound n := by
    rw [←mul_sum]
    exact normalized_square_mass_le (by omega) _ Subset.rfl _
      (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (mangoldt_square_mass_bound (n+2))

noncomputable def ordinaryPositiveFamily : PositiveAverageFamily where
  indices n := Ioc 0 (n+2)
  shift j := (j : ℤ)^2
  weight n _ := ((n+2 : ℕ) : ℝ)⁻¹
  mass := 1
  mass_one_le := le_rfl
  nonnegative _ _ _ := by positivity
  mass_bound n := by
    simp only [sum_const,Nat.card_Ioc,nsmul_eq_mul,Nat.sub_zero]
    exact le_of_eq (mul_inv_cancel₀ (by positivity : ((n+2 : ℕ) : ℝ)≠0))

noncomputable def primePositiveFamily : PositiveAverageFamily where
  indices n := Nat.primesLE (n+2)
  shift j := (j : ℤ)^2
  weight n _ := ((Nat.primeCounting (n+2) : ℕ) : ℝ)⁻¹
  mass := 1
  mass_one_le := le_rfl
  nonnegative _ _ _ := by positivity
  mass_bound n := by
    simp only [sum_const,nsmul_eq_mul,Nat.primesLE_card_eq_primeCounting]
    by_cases h : Nat.primeCounting (n+2)=0
    · simp [h]
    · exact le_of_eq (mul_inv_cancel₀ (by exact_mod_cast h : ((Nat.primeCounting (n+2) : ℕ) : ℝ)≠0))

noncomputable def ordinarySquareFullValue (N : ℕ) (f : ℤ → ℂ) (x : ℤ) : ℂ :=
  (((N : ℝ)⁻¹) : ℂ)*∑ j∈Ioc 0 N,f (x-(j : ℤ)^2)

noncomputable def unweightedPrimeSquareValue (N : ℕ) (f : ℤ → ℂ) (x : ℤ) : ℂ :=
  (((Nat.primeCounting N : ℝ)⁻¹) : ℂ)*∑ j∈Nat.primesLE N,f (x-(j : ℤ)^2)

theorem mangoldtPositiveFamily_apply (n : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    positiveAverage mangoldtPositiveFamily n f x=primeSquareAverageValue (n+2) f x := by
  unfold positiveAverage primeSquareAverageValue
  change (∑ j∈Ioc 0 (n+2),((((n+2 : ℕ) : ℝ)⁻¹*ArithmeticFunction.vonMangoldt j : ℝ) : ℂ)*f (x-(j : ℤ)^2))=_
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  push_cast
  ring

theorem ordinaryPositiveFamily_apply (n : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    positiveAverage ordinaryPositiveFamily n f x=ordinarySquareFullValue (n+2) f x := by
  simp only [positiveAverage,ordinaryPositiveFamily,ordinarySquareFullValue,mul_sum,Complex.ofReal_inv]

theorem primePositiveFamily_apply (n : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    positiveAverage primePositiveFamily n f x=unweightedPrimeSquareValue (n+2) f x := by
  simp only [positiveAverage,primePositiveFamily,unweightedPrimeSquareValue,mul_sum,Complex.ofReal_inv]

theorem positiveSquareFamilies_uniform_mass :
    ordinaryPositiveFamily.mass≤primeSquareChebyshevConstant ∧
      primePositiveFamily.mass≤primeSquareChebyshevConstant ∧
      mangoldtPositiveFamily.mass≤primeSquareChebyshevConstant := by
  have h : 1≤primeSquareChebyshevConstant := mangoldtPositiveFamily.mass_one_le
  exact ⟨h,h,le_rfl⟩

theorem mangoldtPositiveFamily_maximal (f : ℤ → ℂ) (x : ℤ) :
    positiveMaximal mangoldtPositiveFamily f x=⨆ j : ℕ,‖primeSquareAverageValue (j+2) f x‖ := by
  simp only [positiveMaximal,mangoldtPositiveFamily_apply]

theorem ordinaryPositiveFamily_maximal (f : ℤ → ℂ) (x : ℤ) :
    positiveMaximal ordinaryPositiveFamily f x=⨆ j : ℕ,‖ordinarySquareFullValue (j+2) f x‖ := by
  simp only [positiveMaximal,ordinaryPositiveFamily_apply]

theorem primePositiveFamily_maximal (f : ℤ → ℂ) (x : ℤ) :
    positiveMaximal primePositiveFamily f x=⨆ j : ℕ,‖unweightedPrimeSquareValue (j+2) f x‖ := by
  simp only [positiveMaximal,primePositiveFamily_apply]

end PrimeSquares
