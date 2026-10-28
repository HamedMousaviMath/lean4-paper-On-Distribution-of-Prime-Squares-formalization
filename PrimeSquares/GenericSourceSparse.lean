import PrimeSquares.GenericFullSparse

set_option autoImplicit false
open Finset
namespace PrimeSquares

/-- The source local hypothesis is tested only on stopping maps admissible
on the entire parent interval. The fixed admissibility constant A is explicit. -/
def SourceDyadicLocalEstimate {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (Ψ : ℝ → ℝ → ℝ) (K A : ℝ) : Prop :=
  ∀ (I : SparseIntegerInterval) (F G : Finset ℤ) (τ : ℤ → ℕ),
    F ⊆ (I.oddDilate m).points → G ⊆ I.points →
    (∀ x ∈ I.points,(2:ℕ)^(τ x) ≤ I.length) →
    (∀ x ∈ I.points,linearSourceLocalMass C ((2:ℕ)^(τ x)) (finiteIndicatorLp F 1) x ≤
      A*((F.card:ℝ)/I.length)) →
    ‖∑ x ∈ G,positiveDyadicValue T (τ x) F x‖ ≤
      K*(I.length:ℝ)*Ψ ((F.card:ℝ)/I.length) ((G.card:ℝ)/I.length)

theorem sourceFullLocal_implies_generic {C K A : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (Ψ : ℝ → ℝ → ℝ) (hA : 320*max 1 C ≤ A)
    (hlocal : SourceDyadicLocalEstimate T m Ψ K A) : GenericRestrictedLocalEstimate T m Ψ K := by
  intro I F G τ hF hG hscale hadm
  classical
  let σ := fun x : ℤ => if x ∈ G then τ x else Nat.log2 I.length
  have hI : (0:ℝ)<I.length := by exact_mod_cast I.length_pos
  have hdens : 0 ≤ (F.card:ℝ)/I.length := div_nonneg (Nat.cast_nonneg _) hI.le
  have hscale' (x : ℤ) (_hx : x ∈ I.points) : (2:ℕ)^(σ x) ≤ I.length := by
    dsimp [σ]
    split_ifs with hxG
    · exact hscale x hxG
    · exact (genericDefaultIndex_bounds I).1
  have hadm' (x : ℤ) (_hx : x ∈ I.points) :
      linearSourceLocalMass C ((2:ℕ)^(σ x)) (finiteIndicatorLp F 1) x ≤ A*((F.card:ℝ)/I.length) := by
    have hb : linearSourceLocalMass C ((2:ℕ)^(σ x)) (finiteIndicatorLp F 1) x ≤
        (320*max 1 C)*((F.card:ℝ)/I.length) := by
      dsimp [σ]
      split_ifs with hxG
      · exact hadm x hxG
      · exact genericDefaultIndex_admissible I F C x
    exact hb.trans (mul_le_mul_of_nonneg_right hA hdens)
  have hb := hlocal I F G σ hF hG hscale' hadm'
  have heq : (∑ x ∈ G,positiveDyadicValue T (σ x) F x)=
      ∑ x ∈ G,positiveDyadicValue T (τ x) F x := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [σ,ite_eq_left hx]
  rw [heq] at hb
  exact hb

theorem source_dyadic_sparse_recursion_full_domain {C K A : ℝ}
    (T : PositiveDyadicConvolutionFamily C) (m : ℕ) (hC : C ≤ (m:ℝ))
    (Ψ : ℝ → ℝ → ℝ) (hK : 0 < K) (hA : 320*max 1 C ≤ A)
    (hlocal : SourceDyadicLocalEstimate T m Ψ K A) :
    ∃ Kout : ℝ,0 < Kout ∧ ∀ F G : Finset ℤ,∃ S : Finset SparseIntegerInterval,
      IntegerSparseFamily (1/4) S ∧
      |genericFullDyadicPairing T F G| ≤ Kout*∑ I ∈ S,genericDensitySparseCost m Ψ I F G := by
  exact source_dyadic_sparse_recursion T m hC Ψ hK
    (sourceFullLocal_implies_generic T m Ψ hA hlocal)

end PrimeSquares
