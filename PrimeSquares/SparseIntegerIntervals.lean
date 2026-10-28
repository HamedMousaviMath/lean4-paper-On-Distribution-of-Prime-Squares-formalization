import PrimeSquares.PrimeSquareSourceInterval

/-!
# Finite integer intervals and the paper's sparse forms

Intervals are nonempty half-open integer intervals. The parameter eta is
explicit: the preliminary definition uses 1/4, whereas Theorem 1.3 states
1/10. All major subsets below are actual finite sets of integers.
-/

open Finset
namespace PrimeSquares

structure SparseIntegerInterval where
  left : ℤ
  length : ℕ
  length_pos : 0 < length
  deriving DecidableEq

def SparseIntegerInterval.points (I : SparseIntegerInterval) : Finset ℤ :=
  Ico I.left (I.left + I.length)

@[simp]
theorem integerInterval_card_points (I : SparseIntegerInterval) : I.points.card = I.length := by
  simp [SparseIntegerInterval.points, Int.card_Ico]

theorem integerInterval_mem_points (I : SparseIntegerInterval) (x : ℤ) :
    x ∈ I.points ↔ I.left ≤ x ∧ x < I.left + I.length := by
  simp [SparseIntegerInterval.points]

theorem integerInterval_nonempty_points (I : SparseIntegerInterval) : I.points.Nonempty := by
  exact card_pos.mp (by simpa using I.length_pos)

def SparseIntegerInterval.five (I : SparseIntegerInterval) : SparseIntegerInterval where
  left := I.left - 2 * (I.length : ℤ)
  length := 5 * I.length
  length_pos := Nat.mul_pos (by decide) I.length_pos

theorem integerInterval_points_subset_five (I : SparseIntegerInterval) : I.points ⊆ I.five.points := by
  intro x hx
  rw [integerInterval_mem_points] at hx ⊢
  simp only [SparseIntegerInterval.five, Nat.cast_mul, Nat.cast_ofNat]
  have h := I.length_pos
  constructor <;> omega

theorem integerInterval_five_injective : Function.Injective SparseIntegerInterval.five := by
  intro I J h
  have hl := congrArg SparseIntegerInterval.length h
  have ha := congrArg SparseIntegerInterval.left h
  simp only [SparseIntegerInterval.five] at hl ha
  have hn : I.length = J.length := by omega
  have hx : I.left = J.left := by rw [hn] at ha; omega
  cases I
  cases J
  simp_all

theorem integerInterval_local_ball_subset_five (I : SparseIntegerInterval) {x y : ℤ}
    (hx : x ∈ I.points) (hy : |x-y| ≤ (I.length : ℤ)) : y ∈ I.five.points := by
  rw [integerInterval_mem_points] at hx ⊢
  rw [abs_le] at hy
  simp only [SparseIntegerInterval.five, Nat.cast_mul, Nat.cast_ofNat]
  constructor <;> omega

/-- The major subsets, their quantitative sizes and their disjointness
are witnesses of sparsity, rather than an abstract Carleson inequality. -/
def IntegerSparseFamily (η : ℝ) (S : Finset SparseIntegerInterval) : Prop :=
  ∃ E : SparseIntegerInterval → Finset ℤ,
    (∀ I ∈ S, E I ⊆ I.points ∧ η * (I.length : ℝ) ≤ (E I).card) ∧
    (S : Set SparseIntegerInterval).PairwiseDisjoint E

theorem integerSparseFamily_mono {η θ : ℝ} {S : Finset SparseIntegerInterval}
    (hS : IntegerSparseFamily η S) (hθη : θ ≤ η) : IntegerSparseFamily θ S := by
  obtain ⟨E, hE, hd⟩ := hS
  refine ⟨E, ?_, hd⟩
  intro I hI
  exact ⟨(hE I hI).1, (mul_le_mul_of_nonneg_right hθη (Nat.cast_nonneg _)).trans
    (hE I hI).2⟩

theorem integerSparseFamily_empty (η : ℝ) : IntegerSparseFamily η ∅ := by
  refine ⟨fun _ => ∅, ?_, ?_⟩ <;> simp

theorem integerSparseFamily_singleton (I : SparseIntegerInterval) {η : ℝ} (hη : η ≤ 1) :
    IntegerSparseFamily η {I} := by
  refine ⟨fun J => J.points, ?_, ?_⟩
  · intro J hJ
    have he : J = I := mem_singleton.mp hJ
    subst J
    exact ⟨Subset.rfl, by simpa using (mul_le_mul_of_nonneg_right hη
      (Nat.cast_nonneg I.length : (0 : ℝ) ≤ I.length))⟩
  · intro J hJ K hK hne
    have hJI : J = I := mem_singleton.mp hJ
    have hKI : K = I := mem_singleton.mp hK
    exact (hne (hJI.trans hKI.symm)).elim

noncomputable def integerEndpointSparseForm (cstar : ℝ)
    (S : Finset SparseIntegerInterval) (F G : Finset ℤ) : ℝ :=
  ∑ I ∈ S, (I.length : ℝ) *
    (finiteSetDensity I.length (F ∩ I.points) (G ∩ I.points))^(2/3 : ℝ) *
    paperPhi cstar (1/2) (finiteSetDensity I.length (F ∩ I.points) (G ∩ I.points))

noncomputable def integerPowerSparseForm (a b : ℝ)
    (S : Finset SparseIntegerInterval) (F G : Finset ℤ) : ℝ :=
  ∑ I ∈ S, (I.length : ℝ) *
    (((F ∩ I.points).card : ℝ) / I.length)^a *
    (((G ∩ I.points).card : ℝ) / I.length)^b

theorem integerEndpointSparseForm_nonneg (cstar : ℝ)
    (S : Finset SparseIntegerInterval) (F G : Finset ℤ) :
    0 ≤ integerEndpointSparseForm cstar S F G := by
  apply sum_nonneg
  intro I _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)) _))
    (paperPhi_pos _ _ _).le

theorem integerPowerSparseForm_nonneg (a b : ℝ)
    (S : Finset SparseIntegerInterval) (F G : Finset ℤ) :
    0 ≤ integerPowerSparseForm a b S F G := by
  apply sum_nonneg
  intro I _
  positivity

end PrimeSquares
