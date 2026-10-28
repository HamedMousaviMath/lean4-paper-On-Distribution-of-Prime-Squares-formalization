import PrimeSquares.GenericDyadicStopping

set_option autoImplicit false
open Finset
open scoped NNReal
namespace PrimeSquares

theorem genericDefaultIndex_bounds (I : SparseIntegerInterval) :
    (2:ℕ)^(Nat.log2 I.length) ≤ I.length ∧ I.length < 2*((2:ℕ)^(Nat.log2 I.length)) := by
  have h := (Nat.log2_eq_iff I.length_pos.ne').mp rfl
  simpa only [pow_succ,mul_comm] using h

theorem genericDefaultIndex_admissible (I : SparseIntegerInterval) (F : Finset ℤ)
    (C : ℝ) (x : ℤ) :
    linearSourceLocalMass C ((2:ℕ)^(Nat.log2 I.length)) (finiteIndicatorLp F 1) x ≤
      (320*max 1 C)*((F.card:ℝ)/I.length) := by
  let N := (2:ℕ)^(Nat.log2 I.length)
  have hN : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hNr : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hI : (0:ℝ)<I.length := by exact_mod_cast I.length_pos
  have hlen : (I.length:ℝ)≤2*(N:ℝ) := by exact_mod_cast (genericDefaultIndex_bounds I).2.le
  have hfrac : (1:ℝ)/(N:ℝ) ≤ 2/(I.length:ℝ) := by
    apply (div_le_div_iff₀ hNr hI).mpr
    simpa only [one_mul] using hlen
  have hD : (2:ℝ)≤320*max 1 C := by have h:=le_max_left (1:ℝ) C; linarith
  have hb := linearSourceLocalMass_uniform hN C (finiteIndicatorLp F 1) x
  rw [finiteIndicatorLp_one_norm] at hb
  calc
    _ ≤ (N:ℝ)⁻¹*(F.card:ℝ) := hb
    _ ≤ (2/(I.length:ℝ))*(F.card:ℝ) :=
      mul_le_mul_of_nonneg_right (by simpa only [one_div] using hfrac) (Nat.cast_nonneg _)
    _ = 2*((F.card:ℝ)/I.length) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hD (div_nonneg (Nat.cast_nonneg _) hI.le)

/-- The local hypothesis from the source, restricted to the exact recursive
indicator and the whole testing set. It does not assert any maximal or sparse
bound and does not impose monotonicity on a future density profile. -/
def GenericAdmissibleLocalBound {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (F G : Finset ℤ) (b : SparseIntegerInterval → ℝ) : Prop :=
  ∀ (I : SparseIntegerInterval) (τ : ℤ → ℕ),
    (∀ x ∈ G ∩ I.points,(2:ℕ)^(τ x) ≤ I.length) →
    (∀ x ∈ G ∩ I.points,
      linearSourceLocalMass C ((2:ℕ)^(τ x)) (finiteIndicatorLp (F ∩ (I.oddDilate m).points) 1) x ≤
        (320*max 1 C)*(((F ∩ (I.oddDilate m).points).card:ℝ)/I.length)) →
    ‖∑ x ∈ G ∩ I.points,positiveDyadicValue T (τ x) (F ∩ (I.oddDilate m).points) x‖ ≤ b I

theorem genericRemainingScale_linearized {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (F G : Finset ℤ) (b : SparseIntegerInterval → ℝ)
    (hlocal : GenericAdmissibleLocalBound T m F G b) (I : SparseIntegerInterval) :
    (∑ x ∈ G ∩ I.points,(genericDyadicMaximum T (genericRemainingIndices I m F x)
      (F ∩ (I.oddDilate m).points) x:ℝ)) ≤ b I := by
  classical
  let τ := fun x : ℤ => if h : (genericRemainingIndices I m F x).Nonempty then
    Classical.choose (genericDyadicMaximum_attained T h (F ∩ (I.oddDilate m).points) x)
      else Nat.log2 I.length
  have hs (x : ℤ) (h : (genericRemainingIndices I m F x).Nonempty) :
      τ x ∈ genericRemainingIndices I m F x ∧
      genericDyadicMaximum T (genericRemainingIndices I m F x) (F ∩ (I.oddDilate m).points) x=
        ‖positiveDyadicValue T (τ x) (F ∩ (I.oddDilate m).points) x‖₊ := by
    dsimp only [τ]
    rw [dite_eq_left h]
    exact Classical.choose_spec (genericDyadicMaximum_attained T h (F ∩ (I.oddDilate m).points) x)
  have hscale (x : ℤ) (_hx : x ∈ G ∩ I.points) : (2:ℕ)^(τ x) ≤ I.length := by
    by_cases h : (genericRemainingIndices I m F x).Nonempty
    · exact (mem_linearDyadicIndices I.length (τ x)).mp
        (genericRemainingIndices_subset I m F x (hs x h).1)
    · simpa only [τ,dite_eq_right h] using (genericDefaultIndex_bounds I).1
  have hadm (x : ℤ) (hx : x ∈ G ∩ I.points) :
      linearSourceLocalMass C ((2:ℕ)^(τ x)) (finiteIndicatorLp (F ∩ (I.oddDilate m).points) 1) x ≤
        (320*max 1 C)*(((F ∩ (I.oddDilate m).points).card:ℝ)/I.length) := by
    by_cases h : (genericRemainingIndices I m F x).Nonempty
    · exact genericRemainingScale_admissible I m F C (Finset.mem_inter.mp hx).2 (hs x h).1
    · simpa only [τ,dite_eq_right h] using genericDefaultIndex_admissible I
        (F ∩ (I.oddDilate m).points) C x
  have hpoint (x : ℤ) :
      (genericDyadicMaximum T (genericRemainingIndices I m F x) (F ∩ (I.oddDilate m).points) x:ℝ) ≤
        ‖positiveDyadicValue T (τ x) (F ∩ (I.oddDilate m).points) x‖ := by
    by_cases h : (genericRemainingIndices I m F x).Nonempty
    · exact le_of_eq (congrArg (fun z : ℝ≥0 => (z:ℝ)) (hs x h).2)
    · have he : genericRemainingIndices I m F x=∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp only [he,genericDyadicMaximum,Finset.sup_empty]
      exact norm_nonneg _
  calc
    _ ≤ ∑ x ∈ G ∩ I.points,‖positiveDyadicValue T (τ x) (F ∩ (I.oddDilate m).points) x‖ :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = ‖∑ x ∈ G ∩ I.points,positiveDyadicValue T (τ x) (F ∩ (I.oddDilate m).points) x‖ :=
      (finite_positive_pairing_norm _ _ (fun x _ => positiveDyadicValue_positive T _ _ x)).symm
    _ ≤ _ := hlocal I τ hscale hadm

end PrimeSquares
