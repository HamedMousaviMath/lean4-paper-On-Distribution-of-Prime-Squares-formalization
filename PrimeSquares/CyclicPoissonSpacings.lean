import PrimeSquares.LaVictoireArithmetic
import Mathlib.Data.Nat.Squarefree

set_option autoImplicit false
open Finset Filter
open scoped Topology
namespace PrimeSquares

noncomputable def cyclicNextPoint (q : ℕ) (S : Finset (ZMod q)) (a : ZMod q) : ZMod q :=
  a+(cyclicForwardGap q S a:ZMod q)

theorem cyclicNextPoint_mem (q : ℕ) [NeZero q] (S : Finset (ZMod q))
    (a : ZMod q) (ha : a ∈ S) : cyclicNextPoint q S a ∈ S := by
  classical
  have hmem : cyclicForwardGap q S a ∈
      ((S.erase a).image (fun b => (b-a).val)) ∪ {q} := Finset.min'_mem _ _
  rcases Finset.mem_union.mp hmem with h|h
  · obtain ⟨b,hb,he⟩ := Finset.mem_image.mp h
    unfold cyclicNextPoint
    rw [←he,ZMod.natCast_zmod_val,add_sub_cancel]
    exact (Finset.mem_erase.mp hb).2
  · have he : cyclicForwardGap q S a=q := Finset.mem_singleton.mp h
    simpa only [cyclicNextPoint,he,ZMod.natCast_self,add_zero] using ha

noncomputable def normalizedCyclicGap (q : ℕ) (S : Finset (ZMod q)) (a : ZMod q) : ℝ :=
  (cyclicForwardGap q S a:ℝ)*S.card/q

noncomputable def cyclicGapTail (q : ℕ) (S : Finset (ZMod q)) (θ : ℝ) : ℝ := by
  classical
  exact ((S.filter (fun a => θ < normalizedCyclicGap q S a)).card:ℝ)/S.card

noncomputable def cyclicJointGapTail (q : ℕ) (S : Finset (ZMod q)) (k : ℕ)
    (θ : Fin k → ℝ) : ℝ := by
  classical
  exact ((S.filter (fun a => ∀ i : Fin k,
    θ i < normalizedCyclicGap q S ((cyclicNextPoint q S)^[i.val] a))).card:ℝ)/S.card

def CyclicPoissonSpacings (Λ : CyclicResidueFamily) (q : ℕ → ℕ+) : Prop :=
  ∀ (k : ℕ) (θ : Fin k → ℝ), (∀ i, 0 ≤ θ i) →
    Tendsto (fun j => cyclicJointGapTail (q j:ℕ) (Λ (q j)) k θ) atTop
      (𝓝 (Real.exp (-∑ i, θ i)))

theorem cyclicJointGapTail_one (q : ℕ) (S : Finset (ZMod q)) (θ : ℝ) :
    cyclicJointGapTail q S 1 (fun _ => θ)=cyclicGapTail q S θ := by
  classical
  simp [cyclicJointGapTail,cyclicGapTail]

theorem poisson_single_gap_tail (Λ : CyclicResidueFamily) (q : ℕ → ℕ+)
    (HP : CyclicPoissonSpacings Λ q) (θ : ℝ) (hθ : 0 ≤ θ) :
    Tendsto (fun j => cyclicGapTail (q j:ℕ) (Λ (q j)) θ) atTop (𝓝 (Real.exp (-θ))) := by
  simpa only [cyclicJointGapTail_one, Fin.sum_univ_one] using HP 1 (fun _ => θ) (fun _ => hθ)

end PrimeSquares
