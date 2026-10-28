import PrimeSquares.ReflectedConvolution
import PrimeSquares.FiniteTemporalMajorants

/-!
# Maximal estimates commute with spatial reflection

This is a general transfer principle for an already given family of maps.
It proves no analytic maximal estimate. The boundedness of the coordinate
norm ranges is included so the real supremum is the actual maximum value,
rather than relying on a totalized supremum of an unbounded set.
-/

open scoped lp

namespace PrimeSquares

def LpFamilyMaximalBound {ι : Type*} {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (T : ι → ℓ^p(ℤ, ℂ) → ℓ^q(ℤ, ℂ)) (C : ℝ) : Prop :=
  ∀ f : ℓ^p(ℤ, ℂ), ∃ g : ℓ^q(ℤ, ℝ),
    (∀ x : ℤ, BddAbove (Set.range (fun i => ‖T i f x‖))) ∧
    (∀ x : ℤ, g x = ⨆ i : ι, ‖T i f x‖) ∧ ‖g‖ ≤ C * ‖f‖

theorem familySupremum_reflect {ι : Type*} (F : ι → ℤ → ℂ) (x : ℤ) :
    (⨆ i : ι, ‖reflectSequence (F i) x‖) =
      reflectSequence (fun y => ⨆ i : ι, ‖F i y‖) x := rfl

theorem lpFamilyMaximalBound_reflect {ι : Type*} {p q : ENNReal}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] {T : ι → ℓ^p(ℤ, ℂ) → ℓ^q(ℤ, ℂ)} {C : ℝ}
    (h : LpFamilyMaximalBound T C) :
    LpFamilyMaximalBound (fun i => reflectLpMap (T i)) C := by
  intro f
  obtain ⟨g, hb, hg, hn⟩ := h (reflectLp f)
  refine ⟨reflectLp g, ?_, ?_, ?_⟩
  · intro x
    simpa only [reflectLpMap_apply] using hb (-x)
  · intro x
    simpa only [reflectLp_apply, reflectLpMap_apply] using hg (-x)
  · simpa only [reflectLp_norm] using hn

theorem lpFamilyMaximalBound_reflect_iff {ι : Type*} {p q : ENNReal}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (T : ι → ℓ^p(ℤ, ℂ) → ℓ^q(ℤ, ℂ)) (C : ℝ) :
    LpFamilyMaximalBound (fun i => reflectLpMap (T i)) C ↔ LpFamilyMaximalBound T C := by
  constructor
  · intro h
    simpa only [reflectLpMap_involutive] using lpFamilyMaximalBound_reflect h
  · exact lpFamilyMaximalBound_reflect

theorem finiteTemporalMajorants_reflect {F : ℕ → ℓ²(ℤ, ℂ)} {B : ℝ}
    (h : FiniteTemporalMajorants F B) :
    FiniteTemporalMajorants (fun j => reflectLp (F j)) B := by
  intro n
  obtain ⟨g, hg, hF, hn⟩ := h n
  refine ⟨reflectLp g, ?_, ?_, ?_⟩
  · intro x
    exact hg (-x)
  · intro j hj x
    exact hF j hj (-x)
  · simpa only [reflectLp_norm] using hn

theorem finiteTemporalMajorants_reflect_iff (F : ℕ → ℓ²(ℤ, ℂ)) (B : ℝ) :
    FiniteTemporalMajorants (fun j => reflectLp (F j)) B ↔ FiniteTemporalMajorants F B := by
  constructor
  · intro h
    simpa only [reflectLp_involutive] using finiteTemporalMajorants_reflect h
  · exact finiteTemporalMajorants_reflect

theorem reflectedMap_difference_norm {p q : ENNReal} [Fact (1 ≤ q)]
    (T U : ℓ^p(ℤ, ℂ) → ℓ^q(ℤ, ℂ)) (f : ℓ^p(ℤ, ℂ)) :
    ‖reflectLpMap T f - reflectLpMap U f‖ =
      ‖T (reflectLp f) - U (reflectLp f)‖ := by
  have he : reflectLpMap T f - reflectLpMap U f =
      reflectLp (T (reflectLp f) - U (reflectLp f)) := by
    apply lp.ext
    rfl
  rw [he, reflectLp_norm]

end PrimeSquares
