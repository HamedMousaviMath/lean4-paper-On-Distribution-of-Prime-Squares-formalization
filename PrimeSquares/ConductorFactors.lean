import PrimeSquares.TwistedSupport
import PrimeSquares.TwistedCorrelation

/-!
# The finite maxima and products in Lemma 3.27

`conductorSigma` is precisely the maximum over the six dyadic multiples and
their unit coefficients. Suprema over these finite nonempty sets are maxima.
The conductor majorant used later is deliberately coarse: the lemma only
asks for an admissible B₀, and the elementary uniform Gauss bound already
gives sufficient decay for this choice.
-/

open Finset

namespace PrimeSquares

noncomputable def dyadicTwistNorm (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (j : Fin 6) : NNReal :=
  (univ : Finset (ZMod (q₀ * 2 ^ j.val))ˣ).sup (fun a =>
    ‖twistedSquareSum (q₀ * 2 ^ j.val)
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ (2 ^ j.val)) χ₀) a‖₊)

noncomputable def conductorSigma (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) : ℝ :=
  ((univ : Finset (Fin 6)).sup (dyadicTwistNorm q₀ χ₀) : NNReal)

noncomputable def conductorRho (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors, gaussOddPrimeFactor p

noncomputable def conductorCorrelationProduct (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, ((p : ℝ) + 1) / ((p : ℝ) - 1)

noncomputable def conductorMajorant (q₀ : ℕ) : ℝ :=
  64 * (8 : ℝ) ^ q₀.primeFactors.card * Real.sqrt q₀

theorem conductorSigma_nonneg (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) :
    0 ≤ conductorSigma q₀ χ₀ := NNReal.coe_nonneg _

theorem norm_inducedSquareSum_le_sigma (q₀ j : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (hj : j ≤ 5) (a : (ZMod (q₀ * 2 ^ j))ˣ) :
    ‖twistedSquareSum (q₀ * 2 ^ j)
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ (2 ^ j)) χ₀) a‖ ≤
      conductorSigma q₀ χ₀ := by
  let i : Fin 6 := ⟨j, by omega⟩
  change ((‖twistedSquareSum (q₀ * 2 ^ i.val)
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ (2 ^ i.val)) χ₀) a‖₊ : NNReal) : ℝ) ≤ _
  have h₁ : ‖twistedSquareSum (q₀ * 2 ^ i.val)
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ (2 ^ i.val)) χ₀) a‖₊ ≤
      dyadicTwistNorm q₀ χ₀ i := by
        unfold dyadicTwistNorm
        exact Finset.le_sup (f := fun b : (ZMod (q₀ * 2 ^ i.val))ˣ => ‖twistedSquareSum (q₀ * 2 ^ i.val)
          (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ (2 ^ i.val)) χ₀) b‖₊) (mem_univ a)
  have h₂ : dyadicTwistNorm q₀ χ₀ i ≤
      (univ : Finset (Fin 6)).sup (dyadicTwistNorm q₀ χ₀) := Finset.le_sup (mem_univ i)
  exact NNReal.coe_le_coe.mpr (h₁.trans h₂)

theorem conductorSigma_le_of_forall (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ j : ℕ, j ≤ 5 → ∀ a : (ZMod (q₀ * 2 ^ j))ˣ,
      ‖twistedSquareSum (q₀ * 2 ^ j)
        (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ (2 ^ j)) χ₀) a‖ ≤ B) :
    conductorSigma q₀ χ₀ ≤ B := by
  change (((univ : Finset (Fin 6)).sup (dyadicTwistNorm q₀ χ₀) : NNReal) : ℝ) ≤
    ((⟨B, hB⟩ : NNReal) : ℝ)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro j _
  change (univ : Finset (ZMod (q₀ * 2 ^ j.val))ˣ).sup _ ≤ _
  apply Finset.sup_le
  intro a _
  exact NNReal.coe_le_coe.mp (h j.val (by omega) a)

attribute [irreducible] conductorSigma dyadicTwistNorm

theorem conductorSigma_le_one (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) :
    conductorSigma q₀ χ₀ ≤ 1 := by
  apply conductorSigma_le_of_forall q₀ χ₀ 1 (by norm_num)
  intro j _ a
  exact norm_twistedSquareSum_le_one (q₀ * 2 ^ j)
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ (2 ^ j)) χ₀) a

theorem one_le_gaussPrimeFactor (p : ℕ) (hp : 2 ≤ p) : 1 ≤ gaussOddPrimeFactor p := by
  have hpos := gaussOddPrimeFactor_pos p hp
  have hd : 0 < 1 - (Real.sqrt (p : ℝ))⁻¹ := inv_pos.mp hpos
  exact (one_le_inv₀ hd).mpr (by have := inv_nonneg.mpr (Real.sqrt_nonneg (p : ℝ)); linarith)

theorem conductorRho_one_le (d : ℕ) : 1 ≤ conductorRho d := by
  apply Finset.one_le_prod₀
  intro p hp
  exact one_le_gaussPrimeFactor p (Nat.prime_of_mem_primeFactors hp).two_le

theorem conductorRho_mono {m n : ℕ} (h : m ∣ n) (hn : n ≠ 0) :
    conductorRho m ≤ conductorRho n := by
  apply prod_le_prod_of_subset_of_one_le₀ (Nat.primeFactors_mono h hn)
  · intro p hp
    exact (gaussOddPrimeFactor_pos p (Nat.prime_of_mem_primeFactors hp).two_le).le
  · intro p hp _
    exact one_le_gaussPrimeFactor p (Nat.prime_of_mem_primeFactors hp).two_le

theorem gaussOddProduct_le_conductorRho (d : ℕ) : gaussOddProduct d ≤ conductorRho d := by
  apply prod_le_prod_of_subset_of_one_le₀ (filter_subset _ _)
  · intro p hp
    exact (gaussOddPrimeFactor_pos p (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).two_le).le
  · intro p hp _
    exact one_le_gaussPrimeFactor p (Nat.prime_of_mem_primeFactors hp).two_le

theorem conductorCorrelationProduct_one_le (d : ℕ) : 1 ≤ conductorCorrelationProduct d := by
  apply Finset.one_le_prod₀
  intro p hp
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  exact (one_le_div (by linarith)).mpr (by linarith)

theorem conductorCorrelationProduct_mono {m n : ℕ} (h : m ∣ n) (hn : n ≠ 0) :
    conductorCorrelationProduct m ≤ conductorCorrelationProduct n := by
  apply prod_le_prod_of_subset_of_one_le₀ (Nat.primeFactors_mono h hn)
  · intro p hp
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact div_nonneg (by positivity) (by linarith)
  · intro p hp _
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact (one_le_div (by linarith)).mpr (by linarith)

theorem conductorMajorant_one_le (q₀ : ℕ) (hq₀ : 0 < q₀) : 1 ≤ conductorMajorant q₀ := by
  have hs : 1 ≤ Real.sqrt (q₀ : ℝ) := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (show (1 : ℝ) ≤ q₀ by exact_mod_cast hq₀)
  have hp : (1 : ℝ) ≤ 8 ^ q₀.primeFactors.card := one_le_pow₀ (by norm_num)
  dsimp only [conductorMajorant]
  nlinarith

/-- Every dyadic multiple occurring in sigma has the same epsilon bound. -/
theorem conductorSigma_uniform_bound (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀),
      conductorSigma q₀ χ₀ ≤ C * (q₀ : ℝ) ^ (-(1 / 2 : ℝ) + ε) := by
  obtain ⟨C, hC, hc⟩ := twistedSquareSum_uniform_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro q₀ inst χ₀
  apply conductorSigma_le_of_forall q₀ χ₀ _ (by positivity)
  intro j _ a
  have hq : (0 : ℝ) < q₀ := by exact_mod_cast NeZero.pos q₀
  have hj : q₀ ≤ q₀ * 2 ^ j := Nat.le_mul_of_pos_right q₀ (by positivity)
  exact (hc (q₀ * 2 ^ j)
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ (2 ^ j)) χ₀) a a.isUnit).trans
    (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hq (by exact_mod_cast hj) (by linarith)) hC.le)

end PrimeSquares
