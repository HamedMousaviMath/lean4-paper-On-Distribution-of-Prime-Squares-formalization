import PrimeSquares.PrimeEndpointSparse
import PrimeSquares.PrimeStoppingOpenEndpoint

/-! # The open-region sparse conclusion of source Theorem 1.3 -/

open Finset
namespace PrimeSquares

theorem primeOpenSparse {c δ CS a b : ℝ}
    (D : PagePrimeSquareDistributionInputs c) (H419 : Proposition419Bounds D δ) (hδ : 0 < δ)
    (hCS : 1 ≤ CS) (HS : OrdinarySquareStoppingInput CS) (HM : IndependentPrimeMaximalInput)
    (htri : SourceSparseTriangle a b) :
    ∃ C : ℝ, 0 < C ∧ ∀ F G : Finset ℤ, ∃ S : Finset SparseIntegerInterval,
      IntegerSparseFamily (1/10) S ∧
      |primeSquareMaximalPairing F G| ≤ C*integerPowerSparseForm a b S F G := by
  obtain ⟨C, hC, hOpen⟩ := primeStopping_open_endpoint D H419 hδ hCS HS HM htri
  let term := fun (I : SparseIntegerInterval) (F G : Finset ℤ) => (I.length : ℝ)*
    (((F ∩ I.points).card : ℝ)/I.length)^a * (((G ∩ I.points).card : ℝ)/I.length)^b
  have hterm : ∀ (I : SparseIntegerInterval) (F G : Finset ℤ), 0 ≤ term I F G := by
    intro I F G
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _))
      (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)
  have hlocal : ∀ F G : Finset ℤ, AdmissibleAnnularLocalBound F G (fun I => C*term I.five F G) := by
    intro F G I H hHG τ hscale hadm
    let F' := F ∩ I.five.points
    let H' := G ∩ I.five.points
    have hHH' : H ⊆ H' := by
      intro x hx
      have hh := mem_inter.mp (hHG hx)
      exact mem_inter.mpr ⟨hh.1, integerInterval_points_subset_five I hh.2⟩
    have hb0 : 0 ≤ C*term I.five F G := mul_nonneg hC.le (hterm I.five F G)
    by_cases hFn : F'.Nonempty
    · by_cases hHn : H'.Nonempty
      · have hb := hOpen I F' H H' τ inter_subset_right inter_subset_right
          (fun x hx => (mem_inter.mp (hHG hx)).2) hHH' hFn hHn hscale hadm
        have hI : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
        have hL : (0 : ℝ) < 5*(I.length : ℝ) := by positivity
        have hh := (div_le_iff₀ hL).mp hb
        have hl : (I.five.length : ℝ) = 5*(I.length : ℝ) := by
          simp only [SparseIntegerInterval.five, Nat.cast_mul, Nat.cast_ofNat]
        dsimp only [term]
        rw [hl]
        convert hh using 1; ring
      · have heH : H' = ∅ := not_nonempty_iff_eq_empty.mp hHn
        have he : H = ∅ := subset_empty.mp (heH ▸ hHH')
        subst H
        simpa only [sum_empty, norm_zero] using hb0
    · have heF : F' = ∅ := not_nonempty_iff_eq_empty.mp hFn
      have he : (∑ x ∈ H, annularDyadicValue (τ x) (F ∩ I.five.points) x) = 0 := by
        apply sum_eq_zero
        intro x _
        change indicatorConvolution _ F' x = 0
        rw [heF, indicatorConvolution_empty]
      rw [he, norm_zero]
      exact hb0
  obtain ⟨K, hK, hSparse⟩ := primeSparse_from_admissible_local term hC hlocal
  refine ⟨K, hK, ?_⟩
  intro F G
  obtain ⟨S, hS, hb⟩ := hSparse F G
  exact ⟨S, hS, by simpa only [integerPowerSparseForm, term] using hb⟩

end PrimeSquares
