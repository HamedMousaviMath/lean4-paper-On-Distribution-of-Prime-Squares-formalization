import PrimeSquares.DyadicRankMass
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.List.Sort

/-!
# Actual decreasing-magnitude blocks for finite complex inputs

The order is constructed by merge sort and retains every input index.
Ties do not require distinct magnitudes. Rank magnitudes are extended by
zero past the list length; this also handles empty and incomplete blocks.
-/

open Finset

namespace PrimeSquares

noncomputable def decreasingMagnitudeList (F : Finset ℤ) (f : ℤ → ℂ) : List ℤ := by
  classical
  exact F.toList.mergeSort (fun x y => decide (‖f y‖ ≤ ‖f x‖))

theorem decreasingMagnitudeList_perm (F : Finset ℤ) (f : ℤ → ℂ) :
    (decreasingMagnitudeList F f).Perm F.toList := by
  classical
  exact List.mergeSort_perm _ _

theorem decreasingMagnitudeList_nodup (F : Finset ℤ) (f : ℤ → ℂ) :
    (decreasingMagnitudeList F f).Nodup :=
  (decreasingMagnitudeList_perm F f).nodup_iff.mpr F.nodup_toList

theorem decreasingMagnitudeList_length (F : Finset ℤ) (f : ℤ → ℂ) :
    (decreasingMagnitudeList F f).length = F.card :=
  (decreasingMagnitudeList_perm F f).length_eq.trans F.length_toList

theorem decreasingMagnitudeList_mem (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    x ∈ decreasingMagnitudeList F f ↔ x ∈ F := by
  simpa only [mem_toList] using (decreasingMagnitudeList_perm F f).mem_iff (a := x)

theorem decreasingMagnitudeList_toFinset (F : Finset ℤ) (f : ℤ → ℂ) :
    (decreasingMagnitudeList F f).toFinset = F := by
  ext x
  rw [List.mem_toFinset, decreasingMagnitudeList_mem]

theorem decreasingMagnitudeList_sorted (F : Finset ℤ) (f : ℤ → ℂ) :
    (decreasingMagnitudeList F f).Pairwise (fun x y => ‖f y‖ ≤ ‖f x‖) := by
  classical
  have h := List.pairwise_mergeSort
    (le := fun x y : ℤ => decide (‖f y‖ ≤ ‖f x‖))
    (fun x y z hxy hyz => by
      simp only [decide_eq_true_eq] at hxy hyz ⊢
      exact hyz.trans hxy)
    (fun x y => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total _ _) F.toList
  simpa only [decreasingMagnitudeList, decide_eq_true_eq] using h

noncomputable def rankMagnitude (l : List ℤ) (f : ℤ → ℂ) (n : ℕ) : ℝ :=
  if h : n < l.length then ‖f (l.get ⟨n,h⟩)‖ else 0

theorem rankMagnitude_nonneg (l : List ℤ) (f : ℤ → ℂ) (n : ℕ) : 0 ≤ rankMagnitude l f n := by
  unfold rankMagnitude
  split_ifs
  · exact norm_nonneg _
  · exact le_rfl

theorem rankMagnitude_get (l : List ℤ) (f : ℤ → ℂ) (i : Fin l.length) :
    rankMagnitude l f i = ‖f (l.get i)‖ := by
  simp only [rankMagnitude, dite_eq_left i.isLt]

theorem rankMagnitude_tail (l : List ℤ) (f : ℤ → ℂ) (n : ℕ) (hn : l.length ≤ n) :
    rankMagnitude l f n = 0 := by
  simp only [rankMagnitude, dite_eq_right (not_lt.mpr hn)]

theorem rankMagnitude_antitone (l : List ℤ) (f : ℤ → ℂ)
    (hsorted : l.Pairwise (fun x y => ‖f y‖ ≤ ‖f x‖)) : Antitone (rankMagnitude l f) := by
  intro i j hij
  by_cases hj : j < l.length
  · have hi : i < l.length := hij.trans_lt hj
    simp only [rankMagnitude, dite_eq_left hi, dite_eq_left hj]
    rcases lt_or_eq_of_le hij with hlt | heq
    · exact hsorted.rel_get_of_lt (a := ⟨i,hi⟩) (b := ⟨j,hj⟩) hlt
    · subst j
      exact le_rfl
  · rw [rankMagnitude_tail l f j (le_of_not_gt hj)]
    exact rankMagnitude_nonneg l f i

def rankIndexBlock (L j : ℕ) : Finset (Fin L) :=
  univ.filter (fun i => i.val ∈ dyadicRankInterval j)

def listRankBlock (l : List ℤ) (j : ℕ) : Finset ℤ :=
  (rankIndexBlock l.length j).image l.get

theorem rankIndexBlock_card_le (L j : ℕ) : (rankIndexBlock L j).card ≤ 2^j := by
  calc
    _ = ((rankIndexBlock L j).image Fin.val).card := (card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (dyadicRankInterval j).card := by
      apply card_le_card
      intro n hn
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hn
      exact (mem_filter.mp hi).2
    _ = _ := dyadicRankInterval_card j

theorem listRankBlock_card_le (l : List ℤ) (j : ℕ) : (listRankBlock l j).card ≤ 2^j :=
  card_image_le.trans (rankIndexBlock_card_le l.length j)

theorem listRankBlock_mem (l : List ℤ) (j : ℕ) {x : ℤ} (hx : x ∈ listRankBlock l j) : x ∈ l := by
  obtain ⟨i,_,rfl⟩ := mem_image.mp hx
  exact l.get_mem i

theorem listRankBlock_disjoint (l : List ℤ) (hnodup : l.Nodup) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (listRankBlock l i) (listRankBlock l j) := by
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨a,ha,hax⟩ := mem_image.mp hx
  obtain ⟨b,hb,hbx⟩ := mem_image.mp hy
  have hab : a = b := hnodup.get_inj_iff.mp (hax.trans hbx.symm)
  subst b
  exact disjoint_left.mp (dyadicRankInterval_disjoint hij)
    (mem_filter.mp ha).2 (mem_filter.mp hb).2

theorem listRankBlock_cover (l : List ℤ) :
    (range (l.length+1)).biUnion (listRankBlock l) = l.toFinset := by
  ext x
  constructor
  · intro hx
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hx
    exact List.mem_toFinset.mpr (listRankBlock_mem l j hj)
  · intro hx
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hx)
    apply mem_biUnion.mpr
    refine ⟨Nat.log2 (i.val+1), mem_range.mpr ?_, ?_⟩
    · exact Nat.lt_succ_of_le (dyadicRankInterval_index_le i.isLt)
    · apply mem_image.mpr
      refine ⟨i, mem_filter.mpr ⟨mem_univ _, dyadicRankInterval_cover i.val⟩, hi⟩

theorem listRankBlock_norm_le (l : List ℤ) (f : ℤ → ℂ)
    (hsorted : l.Pairwise (fun x y => ‖f y‖ ≤ ‖f x‖)) (j : ℕ)
    {x : ℤ} (hx : x ∈ listRankBlock l j) : ‖f x‖ ≤ rankMagnitude l f (dyadicRankStart j) := by
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
  have hstart := (mem_Ico.mp (mem_filter.mp hi).2).1
  have h := rankMagnitude_antitone l f hsorted hstart
  rwa [rankMagnitude_get] at h

theorem listRankBlock_sum {M : Type*} [AddCommMonoid M] (l : List ℤ) (hnodup : l.Nodup)
    (h : ℤ → M) :
    (∑ j ∈ range (l.length+1), ∑ x ∈ listRankBlock l j, h x) = ∑ x ∈ l.toFinset, h x := by
  rw [← listRankBlock_cover l]
  symm
  apply sum_biUnion
  intro i _ j _ hij
  exact listRankBlock_disjoint l hnodup hij

theorem rankMagnitude_sum (l : List ℤ) (hnodup : l.Nodup) (f : ℤ → ℂ) (p : ℝ) :
    (∑ n ∈ range l.length, (rankMagnitude l f n)^p) = ∑ x ∈ l.toFinset, ‖f x‖^p := by
  apply sum_bij (fun n hn => l.get ⟨n,mem_range.mp hn⟩)
  · intro n hn
    exact List.mem_toFinset.mpr (l.get_mem _)
  · intro i hi j hj hij
    exact congrArg Fin.val (hnodup.get_inj_iff.mp hij)
  · intro x hx
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hx)
    exact ⟨i.val, mem_range.mpr i.isLt, hi⟩
  · intro n hn
    simp only [rankMagnitude, dite_eq_left (mem_range.mp hn)]

noncomputable def magnitudeBlock (F : Finset ℤ) (f : ℤ → ℂ) (j : ℕ) : Finset ℤ :=
  listRankBlock (decreasingMagnitudeList F f) j

noncomputable def magnitudeAmplitude (F : Finset ℤ) (f : ℤ → ℂ) (j : ℕ) : ℝ :=
  rankMagnitude (decreasingMagnitudeList F f) f (dyadicRankStart j)

theorem magnitudeBlock_card_le (F : Finset ℤ) (f : ℤ → ℂ) (j : ℕ) :
    (magnitudeBlock F f j).card ≤ 2^j := listRankBlock_card_le _ j

theorem magnitudeBlock_disjoint (F : Finset ℤ) (f : ℤ → ℂ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (magnitudeBlock F f i) (magnitudeBlock F f j) :=
  listRankBlock_disjoint _ (decreasingMagnitudeList_nodup F f) hij

theorem magnitudeBlock_cover (F : Finset ℤ) (f : ℤ → ℂ) :
    (range (F.card+1)).biUnion (magnitudeBlock F f) = F := by
  change (range (F.card+1)).biUnion (listRankBlock (decreasingMagnitudeList F f)) = F
  simpa only [decreasingMagnitudeList_length, decreasingMagnitudeList_toFinset] using
    listRankBlock_cover (decreasingMagnitudeList F f)

theorem magnitudeAmplitude_nonneg (F : Finset ℤ) (f : ℤ → ℂ) (j : ℕ) :
    0 ≤ magnitudeAmplitude F f j := rankMagnitude_nonneg _ f _

theorem magnitudeBlock_norm_le (F : Finset ℤ) (f : ℤ → ℂ) (j : ℕ) :
    ∀ x ∈ magnitudeBlock F f j, ‖f x‖ ≤ magnitudeAmplitude F f j := by
  intro x hx
  exact listRankBlock_norm_le _ f (decreasingMagnitudeList_sorted F f) j hx

theorem magnitudeBlock_sum {M : Type*} [AddCommMonoid M] (F : Finset ℤ) (f : ℤ → ℂ)
    (h : ℤ → M) :
    (∑ j ∈ range (F.card+1), ∑ x ∈ magnitudeBlock F f j, h x) = ∑ x ∈ F, h x := by
  simpa only [magnitudeBlock, decreasingMagnitudeList_length, decreasingMagnitudeList_toFinset] using
    listRankBlock_sum (decreasingMagnitudeList F f) (decreasingMagnitudeList_nodup F f) h

/-- Actual blocks, not assumed block data: the coefficient mass is at most
three times the original finite input mass for every positive exponent. -/
theorem magnitudeBlock_coefficient_mass (F : Finset ℤ) (f : ℤ → ℂ) {p : ℝ} (hp : 0 < p) :
    (∑ j ∈ range (F.card+1), (((2 : ℝ)^j)^(1/p) * magnitudeAmplitude F f j)^p) ≤
      3 * ∑ x ∈ F, ‖f x‖^p := by
  have h := dyadic_rank_coefficient_mass
    (rankMagnitude_nonneg (decreasingMagnitudeList F f) f)
    (rankMagnitude_antitone _ f (decreasingMagnitudeList_sorted F f)) hp
    (decreasingMagnitudeList F f).length (rankMagnitude_tail _ f)
    (decreasingMagnitudeList F f).length
  rw [rankMagnitude_sum _ (decreasingMagnitudeList_nodup F f), decreasingMagnitudeList_toFinset,
    decreasingMagnitudeList_length] at h
  exact h

end PrimeSquares
