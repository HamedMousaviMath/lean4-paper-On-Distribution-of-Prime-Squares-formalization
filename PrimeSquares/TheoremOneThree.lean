import PrimeSquares.PrimeOpenSparse

/-!
# Source Theorem 1.3, with both sparse conclusions

This is a complete implication from explicitly recorded independent deep
analytic inputs. Neither the paper's local endpoint nor its stopping
recursion nor either final sparse conclusion is a theorem hypothesis.
-/

namespace PrimeSquares

/-- General collections, including infinite collections, with the same
actual finite major subsets used by the source definition. -/
def IntegerSparseCollection (η : ℝ) (S : Set SparseIntegerInterval) : Prop :=
  ∃ E : SparseIntegerInterval → Finset ℤ,
    (∀ I ∈ S, E I ⊆ I.points ∧ η*(I.length : ℝ) ≤ (E I).card) ∧
    S.PairwiseDisjoint E

theorem integerSparseFamily_iff_collection (η : ℝ) (S : Finset SparseIntegerInterval) :
    IntegerSparseFamily η S ↔ IntegerSparseCollection η (S : Set SparseIntegerInterval) := Iff.rfl

theorem theorem_1_3 (HP : PrimeAsymptoticInputs) {c C CS : ℝ}
    (D : PagePrimeSquareDistributionInputs c) (hc : 0 < c) (hC : 0 ≤ C)
    (HB : SmoothCircleBourgainInput C) (HPg : RawPageUniquenessInput c)
    (hCS : 1 ≤ CS) (HS : OrdinarySquareStoppingInput CS) (HM : IndependentPrimeMaximalInput) :
    (∀ cstar : ℝ, 4*Real.sqrt 3/9 < cstar → ∃ K : ℝ, 0 < K ∧
      ∀ F G : Finset ℤ, ∃ S : Finset SparseIntegerInterval, IntegerSparseFamily (1/10) S ∧
        |primeSquareMaximalPairing F G| ≤ K*integerEndpointSparseForm cstar S F G) ∧
    (∀ a b : ℝ, SourceSparseTriangle a b → ∃ K : ℝ, 0 < K ∧
      ∀ F G : Finset ℤ, ∃ S : Finset SparseIntegerInterval, IntegerSparseFamily (1/10) S ∧
        |primeSquareMaximalPairing F G| ≤ K*integerPowerSparseForm a b S F G) := by
  obtain ⟨δ, hδ, H419⟩ := proposition419 HP D hc hC HB HPg
  exact ⟨fun cstar hstar => primeEndpointSparse D H419 hδ hCS HS hstar,
    fun a b htri => primeOpenSparse D H419 hδ hCS HS HM htri⟩

/-- The endpoint does not require the independent complementary-exponent
maximal Lp input used only for the open triangle. -/
theorem theorem_1_3_endpoint (HP : PrimeAsymptoticInputs) {c C CS cstar : ℝ}
    (D : PagePrimeSquareDistributionInputs c) (hc : 0 < c) (hC : 0 ≤ C)
    (HB : SmoothCircleBourgainInput C) (HPg : RawPageUniquenessInput c)
    (hCS : 1 ≤ CS) (HS : OrdinarySquareStoppingInput CS) (hstar : 4*Real.sqrt 3/9 < cstar) :
    ∃ K : ℝ, 0 < K ∧ ∀ F G : Finset ℤ, ∃ S : Finset SparseIntegerInterval,
      IntegerSparseFamily (1/10) S ∧
      |primeSquareMaximalPairing F G| ≤ K*integerEndpointSparseForm cstar S F G := by
  obtain ⟨δ, hδ, H419⟩ := proposition419 HP D hc hC HB HPg
  exact primeEndpointSparse D H419 hδ hCS HS hstar

/-- Literal reciprocal-exponent coordinates of the printed open triangle.
The strictly positive barycentric criterion is proved equivalent to the
three edge inequalities in sourceSparseTriangle_iff_barycentric. -/
theorem theorem_1_3_open_pq (HP : PrimeAsymptoticInputs) {c C CS p q : ℝ}
    (D : PagePrimeSquareDistributionInputs c) (hc : 0 < c) (hC : 0 ≤ C)
    (HB : SmoothCircleBourgainInput C) (HPg : RawPageUniquenessInput c)
    (hCS : 1 ≤ CS) (HS : OrdinarySquareStoppingInput CS) (HM : IndependentPrimeMaximalInput)
    (htri : ∃ u v w : ℝ, 0 < u ∧ 0 < v ∧ 0 < w ∧ u+v+w=1 ∧
      1/p=(2/3 : ℝ)*u+v ∧ 1/q=(2/3 : ℝ)*u+w) :
    ∃ K : ℝ, 0 < K ∧ ∀ F G : Finset ℤ, ∃ S : Finset SparseIntegerInterval,
      IntegerSparseFamily (1/10) S ∧
      |primeSquareMaximalPairing F G| ≤ K*integerPowerSparseForm (1/p) (1/q) S F G := by
  exact (theorem_1_3 HP D hc hC HB HPg hCS HS HM).2 (1/p) (1/q)
    ((sourceSparseTriangle_iff_barycentric (1/p) (1/q)).mpr htri)

end PrimeSquares
