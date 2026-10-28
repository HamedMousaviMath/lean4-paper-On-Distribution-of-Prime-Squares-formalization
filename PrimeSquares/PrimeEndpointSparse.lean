import PrimeSquares.PrimeFullMaximalComparison
import PrimeSquares.PrimeStoppingLocalEndpoint

/-!
# The endpoint conclusion of source Theorem 1.3

The resulting family consists of actual integer intervals and actual
pairwise disjoint major subsets of at least one tenth their size.
The maximum includes every original integer cutoff N>=2.
-/

open Finset
namespace PrimeSquares

theorem primeSparse_from_admissible_local
    (term : SparseIntegerInterval → Finset ℤ → Finset ℤ → ℝ) {C : ℝ} (hC : 0 < C)
    (hlocal : ∀ F G : Finset ℤ, AdmissibleAnnularLocalBound F G (fun I => C*term I.five F G)) :
    ∃ K : ℝ, 0 < K ∧ ∀ F G : Finset ℤ, ∃ S : Finset SparseIntegerInterval,
      IntegerSparseFamily (1/10) S ∧
      |primeSquareMaximalPairing F G| ≤ K*∑ I ∈ S, term I F G := by
  refine ⟨4*C, by positivity, ?_⟩
  intro F G
  obtain ⟨S, _, hS, hc⟩ := primeAnnularSparse_from_local F G _ (hlocal F G) (primeSparseRoot F G)
  refine ⟨S.image SparseIntegerInterval.five, integerSparseFamily_five_source hS, ?_⟩
  rw [abs_of_nonneg (primeSquareMaximalPairing_nonneg F G)]
  have hs : (∑ I ∈ S, C*term I.five F G) = C*∑ I ∈ S.image SparseIntegerInterval.five, term I F G := by
    rw [sum_image (fun A _ B _ h => integerInterval_five_injective h), mul_sum]
  calc
    _ ≤ 4*annularLocalMaxPairing (primeSparseRoot F G) F G := primeSquareMaximalPairing_le_root F G
    _ ≤ 4*∑ I ∈ S, C*term I.five F G := mul_le_mul_of_nonneg_left hc (by norm_num)
    _ = _ := by rw [hs]; ring

theorem primeEndpointSparse {c δ CS cstar : ℝ}
    (D : PagePrimeSquareDistributionInputs c) (H419 : Proposition419Bounds D δ) (hδ : 0 < δ)
    (hCS : 1 ≤ CS) (HS : OrdinarySquareStoppingInput CS) (hstar : 4*Real.sqrt 3/9 < cstar) :
    ∃ C : ℝ, 0 < C ∧ ∀ F G : Finset ℤ, ∃ S : Finset SparseIntegerInterval,
      IntegerSparseFamily (1/10) S ∧
      |primeSquareMaximalPairing F G| ≤ C*integerEndpointSparseForm cstar S F G := by
  obtain ⟨K, hK, hEndpoint⟩ := primeStopping_local_endpoint D H419 hδ hCS HS hstar
  refine ⟨4*K, by positivity, ?_⟩
  intro F G
  let term := fun I : SparseIntegerInterval => (I.length : ℝ)*
    (finiteSetDensity I.length (F ∩ I.points) (G ∩ I.points))^(2/3 : ℝ)*
    paperPhi cstar (1/2) (finiteSetDensity I.length (F ∩ I.points) (G ∩ I.points))
  let b := fun I : SparseIntegerInterval => K*term I.five
  have ht0 : ∀ I, 0 ≤ term I := by
    intro I
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)) _))
      (paperPhi_pos _ _ _).le
  have hlocal : AdmissibleAnnularLocalBound F G b := by
    intro I H hHG τ hscale hadm
    let F' := F ∩ I.five.points
    let H' := G ∩ I.five.points
    have hHH' : H ⊆ H' := by
      intro x hx
      have hh := mem_inter.mp (hHG hx)
      exact mem_inter.mpr ⟨hh.1, integerInterval_points_subset_five I hh.2⟩
    have hb0 : 0 ≤ b I := mul_nonneg hK.le (ht0 I.five)
    by_cases hFn : F'.Nonempty
    · by_cases hHn : H'.Nonempty
      · have hb := hEndpoint I F' H H' τ inter_subset_right inter_subset_right
          (fun x hx => (mem_inter.mp (hHG hx)).2) hHH' hFn hHn hscale hadm
        have hI : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
        have hL : (0 : ℝ) < 5*(I.length : ℝ) := by positivity
        have hh := (div_le_iff₀ hL).mp hb
        have hl : (I.five.length : ℝ) = 5*(I.length : ℝ) := by
          simp only [SparseIntegerInterval.five, Nat.cast_mul, Nat.cast_ofNat]
        dsimp only [b, term]
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
  obtain ⟨S, _, hSparse, hCost⟩ := primeAnnularSparse_from_local F G b hlocal (primeSparseRoot F G)
  have hsum : (∑ I ∈ S, b I) = K*integerEndpointSparseForm cstar
      (S.image SparseIntegerInterval.five) F G := by
    change (∑ I ∈ S, K*term I.five) = K*∑ I ∈ S.image SparseIntegerInterval.five, term I
    rw [sum_image (fun A _ B _ h => integerInterval_five_injective h), mul_sum]
  refine ⟨S.image SparseIntegerInterval.five, integerSparseFamily_five_source hSparse, ?_⟩
  rw [abs_of_nonneg (primeSquareMaximalPairing_nonneg F G)]
  calc
    _ ≤ 4*annularLocalMaxPairing (primeSparseRoot F G) F G := primeSquareMaximalPairing_le_root F G
    _ ≤ 4*∑ I ∈ S, b I := mul_le_mul_of_nonneg_left hCost (by norm_num)
    _ = _ := by rw [hsum]; ring

end PrimeSquares
