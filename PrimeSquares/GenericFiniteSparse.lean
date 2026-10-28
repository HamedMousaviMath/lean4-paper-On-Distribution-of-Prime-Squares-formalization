import PrimeSquares.GenericSparseLinearization

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem genericPositiveSparseStep {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (hC : C ≤ (m:ℝ)) (F G : Finset ℤ) (b : SparseIntegerInterval → ℝ)
    (hlocal : GenericAdmissibleLocalBound T m F G b) (R I : SparseIntegerInterval)
    (hI : I ∈ integerSubintervals R) :
    IntegerSparseStep (integerSubintervals R) (fun I => genericLocalMaxPairing T m I F G) b I := by
  let U := primeStoppingChildren I (F ∩ (I.oddDilate m).points)
  refine ⟨U,?_,?_,primeStoppingChildren_disjoint _ _,?_,?_⟩
  · intro A hA
    exact integerSubintervals_trans hI ((mem_integerSubintervals I A).mpr
      (primeStoppingChildren_geometry hA).1)
  · exact fun A hA => primeStoppingChildren_geometry hA
  · rw [show U.biUnion SparseIntegerInterval.points=primeStoppingBadSet I (F ∩ (I.oddDilate m).points) from
      primeStoppingChildren_cover I (F ∩ (I.oddDilate m).points)]
    exact primeStoppingBadSet_packing _ _
  · exact (genericRemainingScale_pairing T m hC I F G).trans
      (add_le_add (genericRemainingScale_linearized T m F G b hlocal I) le_rfl)

theorem genericPositiveFiniteSparse {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (hC : C ≤ (m:ℝ)) (F G : Finset ℤ) (b : SparseIntegerInterval → ℝ)
    (hlocal : GenericAdmissibleLocalBound T m F G b) (R : SparseIntegerInterval) :
    ∃ S ⊆ integerSubintervals R,IntegerSparseFamily (3/4) S ∧
      genericLocalMaxPairing T m R F G ≤ ∑ I ∈ S,b I := by
  exact laminarSparseRecursion (integerSubintervals R) (fun I => genericLocalMaxPairing T m I F G) b
    (fun I hI => genericPositiveSparseStep T m hC F G b hlocal R I hI) R (integerSubintervals_self R)

noncomputable def genericDensitySparseCost (m : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (I : SparseIntegerInterval) (F G : Finset ℤ) : ℝ :=
  (I.length:ℝ)*Ψ (((F ∩ (I.oddDilate m).points).card:ℝ)/I.length)
    (((G ∩ I.points).card:ℝ)/I.length)

/-- The source local estimate, with its sufficiently large fixed admissibility
constant made explicit. Psi is arbitrary: positivity, monotonicity and
fixed-dilation comparisons are not hypotheses. -/
def GenericRestrictedLocalEstimate {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (Ψ : ℝ → ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ (I : SparseIntegerInterval) (F G : Finset ℤ) (τ : ℤ → ℕ),
    F ⊆ (I.oddDilate m).points → G ⊆ I.points →
    (∀ x ∈ G,(2:ℕ)^(τ x) ≤ I.length) →
    (∀ x ∈ G,linearSourceLocalMass C ((2:ℕ)^(τ x)) (finiteIndicatorLp F 1) x ≤
      (320*max 1 C)*((F.card:ℝ)/I.length)) →
    ‖∑ x ∈ G,positiveDyadicValue T (τ x) F x‖ ≤
      K*(I.length:ℝ)*Ψ ((F.card:ℝ)/I.length) ((G.card:ℝ)/I.length)

theorem genericFiniteSparse_from_local_profile {C K : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (hC : C ≤ (m:ℝ)) (Ψ : ℝ → ℝ → ℝ)
    (hlocal : GenericRestrictedLocalEstimate T m Ψ K)
    (R : SparseIntegerInterval) (F G : Finset ℤ) :
    ∃ S ⊆ integerSubintervals R,IntegerSparseFamily (3/4) S ∧
      genericLocalMaxPairing T m R F G ≤ K*∑ I ∈ S,genericDensitySparseCost m Ψ I F G := by
  have hbound : GenericAdmissibleLocalBound T m F G (fun I => K*genericDensitySparseCost m Ψ I F G) := by
    intro I τ hscale hadm
    have h := hlocal I (F ∩ (I.oddDilate m).points) (G ∩ I.points) τ
      Finset.inter_subset_right Finset.inter_subset_right hscale hadm
    simpa only [genericDensitySparseCost,mul_assoc] using h
  obtain ⟨S,hS,hsp,hval⟩ := genericPositiveFiniteSparse T m hC F G _ hbound R
  refine ⟨S,hS,hsp,?_⟩
  simpa only [Finset.mul_sum] using hval

end PrimeSquares
