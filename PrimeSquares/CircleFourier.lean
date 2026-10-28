import PrimeSquares.FiniteSquareOperators
import Mathlib.Analysis.Fourier.AddCircle

/-!
# The paper's negative-phase Fourier transform on the integers

The circle has period one and Haar mass one. Reindexing Mathlib's Fourier
Hilbert basis by negation gives the paper's convention exp(-2 pi i n theta).
The resulting transform is an actual complex-linear isometric equivalence
between integer l2 and circle L2, not an assumed Plancherel identity.
-/

open Finset MeasureTheory
open scoped lp

namespace PrimeSquares

abbrev PrimeCircle := AddCircle (1 : ℝ)

noncomputable abbrev PrimeCircleL2 := Lp ℂ 2 (@AddCircle.haarAddCircle 1 inferInstance)

noncomputable def negativeFourierCharacter (n : ℤ) : C(PrimeCircle, ℂ) := fourier (-n)

theorem negativeFourierCharacter_real (n : ℤ) (θ : ℝ) :
    negativeFourierCharacter n (θ : PrimeCircle) =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (θ : ℂ))) := by
  rw [negativeFourierCharacter, fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem negativeFourierCharacter_add (m n : ℤ) (θ : PrimeCircle) :
    negativeFourierCharacter (m+n) θ =
      negativeFourierCharacter m θ * negativeFourierCharacter n θ := by
  simpa only [negativeFourierCharacter, neg_add] using
    (fourier_add (T := (1 : ℝ)) (m := -m) (n := -n) (x := θ))

theorem negativeFourierCharacter_norm (n : ℤ) (θ : PrimeCircle) :
    ‖negativeFourierCharacter n θ‖ = 1 := Circle.norm_coe _

theorem negativeFourierCharacter_sup_norm (n : ℤ) :
    ‖negativeFourierCharacter n‖ = 1 := fourier_norm (-n)

theorem negativeFourier_orthonormal :
    Orthonormal ℂ (fun n : ℤ => fourierLp (T := (1 : ℝ)) 2 (-n)) :=
  orthonormal_fourier.comp (fun n : ℤ => -n) neg_injective

theorem negativeFourier_dense :
    ⊤ ≤ (Submodule.span ℂ
      (Set.range (fun n : ℤ => fourierLp (T := (1 : ℝ)) 2 (-n)))).topologicalClosure := by
  have hr : Set.range (fun n : ℤ => fourierLp (T := (1 : ℝ)) 2 (-n)) =
      Set.range (fourierLp (T := (1 : ℝ)) 2) := by
    ext f
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨-n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨-n, by simp⟩
  rw [hr, span_fourierLp_closure_eq_top (by norm_num)]

noncomputable def negativeFourierBasis : HilbertBasis ℤ ℂ PrimeCircleL2 :=
  HilbertBasis.mk negativeFourier_orthonormal negativeFourier_dense

theorem negativeFourierBasis_apply (n : ℤ) :
    negativeFourierBasis n = fourierLp (T := (1 : ℝ)) 2 (-n) :=
  congrFun (HilbertBasis.coe_mk negativeFourier_orthonormal negativeFourier_dense) n

noncomputable def integerFourier : ℓ²(ℤ, ℂ) ≃ₗᵢ[ℂ] PrimeCircleL2 :=
  negativeFourierBasis.repr.symm

theorem integerFourier_norm (f : ℓ²(ℤ, ℂ)) : ‖integerFourier f‖ = ‖f‖ :=
  integerFourier.norm_map f

theorem integerFourier_inverse (g : PrimeCircleL2) :
    integerFourier (integerFourier.symm g) = g := integerFourier.apply_symm_apply g

theorem integerFourier_single (n : ℤ) (z : ℂ) :
    integerFourier (lp.single 2 n z) = z • fourierLp (T := (1 : ℝ)) 2 (-n) := by
  have hs : lp.single (E := fun _ : ℤ => ℂ) 2 n z = z • lp.single 2 n (1 : ℂ) := by
    simpa only [smul_eq_mul, mul_one] using lp.single_smul (E := fun _ : ℤ => ℂ) 2 n z (1 : ℂ)
  rw [hs, map_smul]
  exact congrArg (fun g : PrimeCircleL2 => z • g)
    ((negativeFourierBasis.repr_symm_single n).trans (negativeFourierBasis_apply n))

theorem integerFourier_coefficient (f : ℓ²(ℤ, ℂ)) (n : ℤ) :
    fourierCoeff (integerFourier f) (-n) = f n := by
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply]
  rw [coe_fourierBasis]
  rw [← negativeFourierBasis_apply, ← HilbertBasis.repr_apply_apply]
  exact congrArg (fun g : ℓ²(ℤ, ℂ) => g n) (negativeFourierBasis.repr.apply_symm_apply f)

noncomputable def finiteFourierPolynomial (F : Finset ℤ) (f : ℤ → ℂ) :
    C(PrimeCircle, ℂ) := ∑ n ∈ F, f n • negativeFourierCharacter n

theorem finiteFourierPolynomial_apply (F : Finset ℤ) (f : ℤ → ℂ) (θ : PrimeCircle) :
    finiteFourierPolynomial F f θ = ∑ n ∈ F, f n * negativeFourierCharacter n θ := by
  simp only [finiteFourierPolynomial, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]

theorem finiteFourierPolynomial_real (F : Finset ℤ) (f : ℤ → ℂ) (θ : ℝ) :
    finiteFourierPolynomial F f (θ : PrimeCircle) =
      ∑ n ∈ F, f n *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (θ : ℂ))) := by
  simp only [finiteFourierPolynomial_apply, negativeFourierCharacter_real]

theorem integerFourier_finiteInput (F : Finset ℤ) (f : ℤ → ℂ) :
    integerFourier (finiteInputLp F f 2) =
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (finiteFourierPolynomial F f) := by
  simp only [finiteInputLp, finiteFourierPolynomial, map_sum, map_smul,
    integerFourier_single, negativeFourierCharacter, fourierLp]

theorem finiteFourierPolynomial_parseval (F : Finset ℤ) (f : ℤ → ℂ) :
    ‖ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (finiteFourierPolynomial F f)‖ ^ 2 =
      ∑ n ∈ F, ‖f n‖ ^ 2 := by
  rw [← integerFourier_finiteInput, integerFourier_norm]
  simpa using finiteInputLp_norm_rpow F f 2 (by norm_num)

end PrimeSquares
