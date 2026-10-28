import PrimeSquares.UniformUnitSquareFibers
import Mathlib.Topology.Order.LiminfLimsup

set_option autoImplicit false
open Finset Filter
open scoped Topology
namespace PrimeSquares

noncomputable def primeSquareSequence (k : ℕ) : ℕ := (Nat.nth Nat.Prime k)^2

noncomputable def sequenceResidueFrequency (n : ℕ → ℕ) (q : ℕ) [NeZero q]
    (a : ZMod q) (N : ℕ) : ℝ :=
  (∑ k ∈ Finset.range N, if (n k : ZMod q)=a then (1:ℝ) else 0)/(N:ℝ)

def RawFixedPrimeProgressionFrequencyInput : Prop :=
  ∀ (q : ℕ) [NeZero q] (u : (ZMod q)ˣ),
    Tendsto (sequenceResidueFrequency (Nat.nth Nat.Prime) q (u:ZMod q)) atTop
      (𝓝 (1/(q.totient:ℝ)))

theorem sequenceResidueFrequency_card (n : ℕ → ℕ) (q : ℕ) [NeZero q]
    (a : ZMod q) (N : ℕ) :
    sequenceResidueFrequency n q a N=
      (((Finset.range N).filter (fun k => (n k : ZMod q)=a)).card:ℝ)/(N:ℝ) := by
  classical
  simp [sequenceResidueFrequency, Finset.sum_boole]

theorem square_indicator_unit_fibers (q : ℕ) [NeZero q] (a : ZMod q)
    (ha : a ∈ unitSquareResidues q) (z : ZMod q) :
    (if z^2=a then (1:ℝ) else 0)=
      ∑ u ∈ unitSquareRoots q a, if z=(u:ZMod q) then (1:ℝ) else 0 := by
  classical
  by_cases hz : z^2=a
  · have hza : IsUnit (z*z) := by
      rw [←pow_two,hz]
      exact ((isUnitSquare_iff a).mp ((mem_unitSquareResidues a).mp ha)).1
    let u : (ZMod q)ˣ := (isUnit_of_mul_isUnit_left hza).unit
    have hu : (u:ZMod q)=z := (isUnit_of_mul_isUnit_left hza).unit_spec
    have hmem : u ∈ unitSquareRoots q a := (mem_unitSquareRoots q a u).mpr (hu ▸ hz)
    rw [ite_eq_left hz, Finset.sum_eq_single u]
    · simp [hu]
    · intro v _ hv
      have hneq : z ≠ (v:ZMod q) := by
        intro he
        exact hv (Units.ext (he.symm.trans hu.symm))
      simp [hneq]
    · exact fun h => False.elim (h hmem)
  · rw [ite_eq_right hz]
    symm
    apply Finset.sum_eq_zero
    intro u hu
    have hneq : z ≠ (u:ZMod q) := by
      intro he
      exact hz (he ▸ (mem_unitSquareRoots q a u).mp hu)
    simp [hneq]

theorem primeSquareFrequency_partition (q : ℕ) [NeZero q] (a : ZMod q)
    (ha : a ∈ unitSquareResidues q) (N : ℕ) :
    sequenceResidueFrequency primeSquareSequence q a N=
      ∑ u ∈ unitSquareRoots q a,
        sequenceResidueFrequency (Nat.nth Nat.Prime) q (u:ZMod q) N := by
  classical
  unfold sequenceResidueFrequency primeSquareSequence
  simp only [Nat.cast_pow]
  have he : (∑ k ∈ Finset.range N,
      if (Nat.nth Nat.Prime k:ZMod q)^2=a then (1:ℝ) else 0)=
      ∑ k ∈ Finset.range N, ∑ u ∈ unitSquareRoots q a,
        if (Nat.nth Nat.Prime k:ZMod q)=(u:ZMod q) then (1:ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    exact square_indicator_unit_fibers q a ha _
  rw [he, Finset.sum_comm, Finset.sum_div]

theorem primeSquareFrequency_limit (HP : RawFixedPrimeProgressionFrequencyInput)
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : a ∈ unitSquareResidues q) :
    Tendsto (sequenceResidueFrequency primeSquareSequence q a) atTop
      (𝓝 (1/((unitSquareResidues q).card:ℝ))) := by
  classical
  have hs := tendsto_finsetSum (unitSquareRoots q a) (fun u _ => HP q u)
  have heq : (fun N => ∑ u ∈ unitSquareRoots q a,
      sequenceResidueFrequency (Nat.nth Nat.Prime) q (u:ZMod q) N)=
      sequenceResidueFrequency primeSquareSequence q a := by
    funext N
    exact (primeSquareFrequency_partition q a ha N).symm
  rw [heq] at hs
  have hsum : (∑ _u ∈ unitSquareRoots q a, (1/(q.totient:ℝ)))=
      1/((unitSquareResidues q).card:ℝ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one_div] using
      unitSquareRoots_normalized q a ha
  rwa [hsum] at hs

theorem primeSquareFrequency_strict_liminf (HP : RawFixedPrimeProgressionFrequencyInput)
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : a ∈ unitSquareResidues q) :
    (1/2:ℝ)/((unitSquareResidues q).card:ℝ)<
      Filter.liminf (sequenceResidueFrequency primeSquareSequence q a) atTop := by
  rw [(primeSquareFrequency_limit HP q a ha).liminf_eq]
  have hm : (0:ℝ)<((unitSquareResidues q).card:ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (unitSquareResidues_nonempty q))
  exact (div_lt_div_iff_of_pos_right hm).mpr (by norm_num)

theorem primeSquareSequence_strictMono : StrictMono primeSquareSequence := by
  intro i j hij
  exact Nat.pow_lt_pow_left (Nat.nth_strictMono Nat.infinite_setOfPred_prime hij)
    (by decide : 2 ≠ 0)

end PrimeSquares
