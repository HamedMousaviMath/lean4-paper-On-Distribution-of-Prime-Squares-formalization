import PrimeSquares.FiniteAnnularMaximum
import PrimeSquares.SourceLocalMass

/-!
# Explicit independent analytic boundaries for sparse applications

These are predicates, not axioms and not imported Mathlib theorems.
Their existence remains unproved. The ordinary-square boundary is the
local low/high stopping decomposition underlying Han--Lacey--Yang (5.1),
proved there using Lemmas 5.1--5.6. It is stronger than this project's
earlier fixed-scale FullSquareDecompositionInput. The normalization,
fivefold support convention, admissibility formulation and sign in this
interface remain part of its unformalized independent analytic scope.

The second boundary is the complementary-exponent restricted consequence
of the independent prime polynomial maximal Lp theorem (Mehlhop,
Theorem 1). Its interface uses the actual von Mangoldt annular averages;
the published-prime normalization and prime-power extension remain within
the unproved input scope. No endpoint improving or sparse conclusion of
the current paper is a field of either predicate.
-/

open Finset
open scoped lp
namespace PrimeSquares

noncomputable def ordinaryDyadicValue (j : ℕ) (F : Finset ℤ) (x : ℤ) : ℂ :=
  indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^j*2) (fun _ => 1)) F x

def OrdinarySquareStoppingInput (CS : ℝ) : Prop :=
  ∀ (I : SparseIntegerInterval) (F G : Finset ℤ) (τ : ℤ → ℕ) (B : ℝ),
    1 ≤ B → F ⊆ I.five.points → G ⊆ I.points →
    (∀ x ∈ G, ((2 : ℕ)^(τ x)*2)^2 ≤ I.length) →
    (∀ x ∈ G, sourceLocalMass ((2 : ℕ)^(τ x)*2) (finiteIndicatorLp F 1) x ≤
      B * ((F.card : ℝ) / I.length)) →
    ∀ k : ℕ, 2 ≤ (2 : ℝ)^k →
      ∃ lo : ℤ → ℂ, ∃ hi : ℓ²(ℤ, ℂ),
        (∀ x ∈ G, ordinaryDyadicValue (τ x) F x = lo x + hi x) ∧
        (∀ x ∈ G, ‖lo x‖ ≤ CS * B * ((F.card : ℝ) / I.length) *
          ((2 : ℝ)^k) * (Real.log ((2 : ℝ)^k))^(2 : ℝ)) ∧
        ‖hi‖ ≤ CS * ((2 : ℝ)^k)^(-(1/2 : ℝ)) * Real.log ((2 : ℝ)^k) *
          Real.sqrt (F.card : ℝ)

def IndependentPrimeMaximalInput : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 → ∃ C : ℝ, 0 < C ∧
    ∀ (F G : Finset ℤ) (τ : ℤ → ℕ),
      ‖∑ x ∈ G, annularDyadicValue (τ x) F x‖ ≤
        C * (F.card : ℝ)^a * (G.card : ℝ)^(1-a)

theorem ordinarySquareStoppingInput_mono {CS DS : ℝ}
    (H : OrdinarySquareStoppingInput CS) (hCD : CS ≤ DS) : OrdinarySquareStoppingInput DS := by
  intro I F G τ B hB hF hG hscale hadm k hk
  obtain ⟨lo, hi, heq, hlo, hhi⟩ := H I F G τ B hB hF hG hscale hadm k hk
  have hlog : 0 ≤ Real.log ((2 : ℝ)^k) := Real.log_nonneg (by linarith)
  refine ⟨lo, hi, heq, ?_, ?_⟩
  · intro x hx
    exact (hlo x hx).trans (by gcongr)
  · exact hhi.trans (by gcongr)

theorem independentPrimeMaximal_restrict_tests (H : IndependentPrimeMaximalInput)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F G G' : Finset ℤ) (τ : ℤ → ℕ), G ⊆ G' →
      ‖∑ x ∈ G, annularDyadicValue (τ x) F x‖ ≤
        C * (F.card : ℝ)^a * (G'.card : ℝ)^(1-a) := by
  obtain ⟨C, hC, hb⟩ := H a ha ha1
  refine ⟨C, hC, ?_⟩
  intro F G G' τ hGG
  exact (hb F G τ).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast card_le_card hGG) (by linarith))
    (by positivity))

end PrimeSquares
