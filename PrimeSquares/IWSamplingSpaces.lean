import PrimeSquares.IWAnnularLp
import PrimeSquares.CutoffInverseSchwartz
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
open MeasureTheory Finset
open scoped FourierTransform ENNReal
namespace PrimeSquares

/-- The real Lp norm followed by the normalized finite cyclic Lp norm.
Fibre membership is supplied explicitly in every norm comparison. -/
noncomputable def cyclicRealLpSize {E : Type*} [NormedAddCommGroup E] (P : ℕ) (p : ℝ≥0∞)
    (F : ZMod P → ℝ → E) : ℝ≥0∞ :=
  (P : ℝ≥0∞)^(-(p.toReal)⁻¹) *
    eLpNorm (fun y : ZMod P => (eLpNorm (F y) p volume).toReal) p Measure.count

noncomputable def cyclicSynthesis (Γ : Finset ℚ) (P : ℕ)
    (u : ℚ → SchwartzMap ℝ ℂ) (y : ZMod P) (x : ℝ) : ℂ :=
  ∑ α ∈ Γ, u α x * negativeFourierCharacter (-(y.val : ℤ)) ((α : ℝ) : PrimeCircle)

noncomputable def cyclicDiagonal (P : ℕ) (F : ZMod P → ℝ → ℂ) (n : ℤ) : ℂ :=
  F (n : ZMod P) (n : ℝ)

/-- A direct scalar finite-cyclic specialization of Tao Theorem 1.6.
It is quantified over arbitrary bandlimited Schwartz components and contains
no annular kernel, low/high decomposition or maximal conclusion. -/
def RawMajorArcSamplingInput (C : ℝ) : Prop :=
  ∀ (r k : ℕ), 2 ≤ r → 1 ≤ k → ∀ S : Finset ℕ,
    (∀ s ∈ S, 0 < s) → (S : Set ℕ).Pairwise Nat.Coprime →
    ∀ (P : ℕ) [NeZero P], (∀ α ∈ iwFrequencySet S k, α.den ∣ P) →
    ∀ ε : ℝ, IWGood r k S ε → ∀ p : ℝ,
    iwNearOneExponent r ≤ p → p ≤ 2*(r : ℝ) →
    ∀ u : ℚ → SchwartzMap ℝ ℂ,
    (∀ α ∈ iwFrequencySet S k, ∀ θ : ℝ, ε ≤ |θ| → 𝓕 (u α : ℝ → ℂ) θ = 0) →
    MemLp (cyclicDiagonal P (cyclicSynthesis (iwFrequencySet S k) P u))
      (ENNReal.ofReal p) Measure.count →
    cyclicRealLpSize P (ENNReal.ofReal p) (cyclicSynthesis (iwFrequencySet S k) P u) ≤
      ENNReal.ofReal (iwMultiplierConstant C r k) *
        eLpNorm (cyclicDiagonal P (cyclicSynthesis (iwFrequencySet S k) P u))
          (ENNReal.ofReal p) Measure.count

noncomputable def finiteCoordinateMaximum {X : Type*} (I : Finset ℕ)
    (u : ℕ → X → ℂ) (x : X) : ℝ :=
  (I.sup (fun i => ‖u i x‖₊) : NNReal)

/-- The finite-target scalar-coordinate form of quantitative Shannon sampling,
Tao Proposition 1.5, with c=1/100.  The arbitrary finite coordinate maximum
represents the norm of a finite dimensional l-infinity target. -/
def RawNarrowShannonInput (C : ℝ) : Prop :=
  ∀ (P : ℕ) [NeZero P], ∀ δ : ℝ, 0 < δ → δ ≤ 1/(100*(P : ℝ)) →
    ∀ p : ℝ, 1 ≤ p → p ≤ 2 → ∀ I : Finset ℕ,
    ∀ G : ℕ → ZMod P → SchwartzMap ℝ ℂ,
    (∀ i ∈ I, ∀ y : ZMod P, ∀ θ : ℝ, δ ≤ |θ| → 𝓕 (G i y : ℝ → ℂ) θ = 0) →
    MemLp (fun n : ℤ => finiteCoordinateMaximum I
        (fun i (n : ℤ) => G i (n : ZMod P) (n : ℝ)) n)
      (ENNReal.ofReal p) Measure.count ∧
    eLpNorm (fun n : ℤ => finiteCoordinateMaximum I
        (fun i (n : ℤ) => G i (n : ZMod P) (n : ℝ)) n)
      (ENNReal.ofReal p) Measure.count ≤ ENNReal.ofReal C *
        cyclicRealLpSize P (ENNReal.ofReal p)
          (fun y x => finiteCoordinateMaximum I (fun i x => G i y x) x)

noncomputable def cyclicSynthesisSchwartz (Γ : Finset ℚ) (P : ℕ)
    (u : ℚ → SchwartzMap ℝ ℂ) (y : ZMod P) : SchwartzMap ℝ ℂ :=
  ∑ α ∈ Γ, negativeFourierCharacter (-(y.val : ℤ)) ((α : ℝ) : PrimeCircle) • u α

theorem cyclicSynthesisSchwartz_apply (Γ : Finset ℚ) (P : ℕ)
    (u : ℚ → SchwartzMap ℝ ℂ) (y : ZMod P) (x : ℝ) :
    cyclicSynthesisSchwartz Γ P u y x = cyclicSynthesis Γ P u y x := by
  simp only [cyclicSynthesisSchwartz, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, cyclicSynthesis]
  apply Finset.sum_congr rfl
  intro α _
  exact mul_comm _ _

theorem finiteCoordinateMaximum_nonneg {X : Type*} (I : Finset ℕ)
    (u : ℕ → X → ℂ) (x : X) : 0 ≤ finiteCoordinateMaximum I u x := by
  exact NNReal.coe_nonneg _

theorem finiteCoordinateMaximum_le {X : Type*} (I : Finset ℕ)
    (u : ℕ → X → ℂ) (x : X) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i ∈ I, ‖u i x‖ ≤ B) : finiteCoordinateMaximum I u x ≤ B := by
  change ((I.sup (fun i => ‖u i x‖₊) : NNReal) : ℝ) ≤ B
  exact_mod_cast (Finset.sup_le (fun i hi => show ‖u i x‖₊ ≤ ⟨B, hB⟩ from h i hi))

theorem finiteCoordinateMaximum_dominates {X : Type*} (I : Finset ℕ)
    (u : ℕ → X → ℂ) (x : X) {i : ℕ} (hi : i ∈ I) :
    ‖u i x‖ ≤ finiteCoordinateMaximum I u x := by
  exact_mod_cast (Finset.le_sup (f := fun i => ‖u i x‖₊) hi)

theorem quantitative_iw_sampling {C : ℝ} (hC : 2 ≤ C)
    (HS : RawMajorArcSamplingInput C) {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (u : ℚ → SchwartzMap ℝ ℂ)
    (hu : ∀ α ∈ iwFrequencySet d.S k, ∀ θ : ℝ,
      iwWidth C r k Q ≤ |θ| → 𝓕 (u α : ℝ → ℂ) θ = 0)
    (hdiag : MemLp (cyclicDiagonal d.period (cyclicSynthesis (iwFrequencySet d.S k) d.period u))
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count) :
    cyclicRealLpSize d.period (ENNReal.ofReal (iwNearOneExponent r))
      (cyclicSynthesis (iwFrequencySet d.S k) d.period u) ≤
      ENNReal.ofReal (iwMultiplierConstant C r k) *
        eLpNorm (cyclicDiagonal d.period (cyclicSynthesis (iwFrequencySet d.S k) d.period u))
          (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  have hp2r : iwNearOneExponent r ≤ 2*(r : ℝ) := by
    have hp := iwNearOneExponent_bounds hr
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  exact HS r k hr (by omega) d.S d.positive d.coprime d.period d.periodic
    (iwWidth C r k Q) (quantitative_iw_goodness hC hr hk d) _ le_rfl hp2r u hu hdiag

end PrimeSquares
