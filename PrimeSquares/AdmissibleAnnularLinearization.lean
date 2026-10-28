import PrimeSquares.PrimeRemainingScaleRecursion
import PrimeSquares.LaminarSparseRecursion

/-!
# Exact remaining-scale linearization and sparse recursion

The local analytic estimate is an explicit hypothesis of this intermediate
theorem. It is not registered as an independent deep input. The final
prime-square application must supply it from Proposition 4.19 and the
independent ordinary-square stopping estimates.
-/

open Finset
open scoped NNReal
namespace PrimeSquares

theorem finite_positive_pairing_norm (G : Finset ℤ) (u : ℤ → ℂ)
    (hu : ∀ x ∈ G, (u x).im = 0 ∧ 0 ≤ (u x).re) :
    ‖∑ x ∈ G, u x‖ = ∑ x ∈ G, ‖u x‖ := by
  have hi : (∑ x ∈ G, u x).im = 0 := by
    rw [Complex.im_sum]
    exact sum_eq_zero (fun x hx => (hu x hx).1)
  have hr : 0 ≤ (∑ x ∈ G, u x).re := by
    rw [Complex.re_sum]
    exact sum_nonneg (fun x hx => (hu x hx).2)
  rw [complex_norm_eq_re hi hr, Complex.re_sum]
  exact sum_congr rfl (fun x hx => (complex_norm_eq_re (hu x hx).1 (hu x hx).2).symm)

theorem annularDyadicValue_positive (j : ℕ) (F : Finset ℤ) (x : ℤ) :
    (annularDyadicValue j F x).im = 0 ∧ 0 ≤ (annularDyadicValue j F x).re := by
  have hK := finiteSquareKernel_nonnegative (Ioc (((2 : ℕ)^j*2)/2) ((2 : ℕ)^j*2))
    (by positivity : 0 ≤ ((((2 : ℕ)^j*2 : ℕ) : ℝ)⁻¹)) ArithmeticFunction.vonMangoldt
    (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  exact ⟨indicatorConvolution_im_zero hK F x, indicatorConvolution_re_nonneg hK F x⟩

def AdmissibleAnnularLocalBound (F G : Finset ℤ) (b : SparseIntegerInterval → ℝ) : Prop :=
  ∀ (I : SparseIntegerInterval) (H : Finset ℤ), H ⊆ G ∩ I.points → ∀ τ : ℤ → ℕ,
    (∀ x ∈ H, ((2 : ℕ)^(τ x)*2)^2 ≤ I.length) →
    (∀ x ∈ H, sourceLocalMass ((2 : ℕ)^(τ x)*2) (finiteIndicatorLp (F ∩ I.five.points) 1) x ≤
      320 * (((F ∩ I.five.points).card : ℝ) / I.length)) →
    ‖∑ x ∈ H, annularDyadicValue (τ x) (F ∩ I.five.points) x‖ ≤ b I

theorem primeRemainingScale_linearized (F G : Finset ℤ) (b : SparseIntegerInterval → ℝ)
    (hlocal : AdmissibleAnnularLocalBound F G b) (I : SparseIntegerInterval) :
    (∑ x ∈ G ∩ I.points,
      (finiteAnnularMaximum (primeRemainingIndices I F x) (F ∩ I.five.points) x : ℝ)) ≤ b I := by
  classical
  let H := (G ∩ I.points).filter (fun x => (primeRemainingIndices I F x).Nonempty)
  let τ := fun x => if h : (primeRemainingIndices I F x).Nonempty then
    Classical.choose (finiteAnnularMaximum_attained h (F ∩ I.five.points) x) else 0
  have hH : H ⊆ G ∩ I.points := filter_subset _ _
  have hs : ∀ x ∈ H, τ x ∈ primeRemainingIndices I F x ∧
      finiteAnnularMaximum (primeRemainingIndices I F x) (F ∩ I.five.points) x =
        ‖annularDyadicValue (τ x) (F ∩ I.five.points) x‖₊ := by
    intro x hx
    have hne := (mem_filter.mp hx).2
    dsimp only [τ]
    rw [dite_eq_left hne]
    exact Classical.choose_spec (finiteAnnularMaximum_attained hne (F ∩ I.five.points) x)
  have hb := hlocal I H hH τ (fun x hx =>
    (mem_dyadicSpatialIndices I.length (τ x)).mp (primeRemainingIndices_subset I F x (hs x hx).1))
    (fun x hx => primeRemainingScale_admissible I F (mem_inter.mp (hH hx)).2 (hs x hx).1)
  calc
    _ = ∑ x ∈ H, (finiteAnnularMaximum (primeRemainingIndices I F x) (F ∩ I.five.points) x : ℝ) := by
      symm
      apply sum_subset hH
      intro x hx hxH
      have he : primeRemainingIndices I F x = ∅ := by
        apply not_nonempty_iff_eq_empty.mp
        intro hn
        exact hxH (mem_filter.mpr ⟨hx, hn⟩)
      simp only [he, finiteAnnularMaximum, sup_empty]
      rfl
    _ = ∑ x ∈ H, ‖annularDyadicValue (τ x) (F ∩ I.five.points) x‖ :=
      sum_congr rfl (fun x hx => congrArg (fun z : ℝ≥0 => (z : ℝ)) (hs x hx).2)
    _ = ‖∑ x ∈ H, annularDyadicValue (τ x) (F ∩ I.five.points) x‖ :=
      (finite_positive_pairing_norm H _ (fun x _ => annularDyadicValue_positive _ _ x)).symm
    _ ≤ _ := hb

theorem primeAnnularSparseStep (F G : Finset ℤ) (b : SparseIntegerInterval → ℝ)
    (hlocal : AdmissibleAnnularLocalBound F G b) (R I : SparseIntegerInterval)
    (hI : I ∈ integerSubintervals R) :
    IntegerSparseStep (integerSubintervals R) (fun I => annularLocalMaxPairing I F G) b I := by
  let U := primeStoppingChildren I (F ∩ I.five.points)
  refine ⟨U, ?_, ?_, primeStoppingChildren_disjoint _ _, ?_, ?_⟩
  · intro A hA
    exact integerSubintervals_trans hI ((mem_integerSubintervals I A).mpr
      (primeStoppingChildren_geometry hA).1)
  · exact fun A hA => primeStoppingChildren_geometry hA
  · rw [show U.biUnion SparseIntegerInterval.points = primeStoppingBadSet I (F ∩ I.five.points) from
      primeStoppingChildren_cover I (F ∩ I.five.points)]
    exact primeStoppingBadSet_packing _ _
  · exact (primeRemainingScale_pairing I F G).trans
      (add_le_add (primeRemainingScale_linearized F G b hlocal I) le_rfl)

theorem primeAnnularSparse_from_local (F G : Finset ℤ) (b : SparseIntegerInterval → ℝ)
    (hlocal : AdmissibleAnnularLocalBound F G b) (R : SparseIntegerInterval) :
    ∃ S ⊆ integerSubintervals R, IntegerSparseFamily (3/4) S ∧
      annularLocalMaxPairing R F G ≤ ∑ I ∈ S, b I := by
  exact laminarSparseRecursion (integerSubintervals R) (fun I => annularLocalMaxPairing I F G) b
    (fun I hI => primeAnnularSparseStep F G b hlocal R I hI) R (integerSubintervals_self R)

end PrimeSquares
