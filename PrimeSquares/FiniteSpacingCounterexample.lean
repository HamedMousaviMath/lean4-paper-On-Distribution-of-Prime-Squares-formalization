import PrimeSquares.UnitSquareResidues

set_option autoImplicit false
open Finset
namespace PrimeSquares

def cyclicDistanceNat (q : ℕ) (a b : ZMod q) : ℕ :=
  min (a-b).val (b-a).val

def cyclicForwardGap (q : ℕ) (S : Finset (ZMod q)) (a : ZMod q) : ℕ :=
  (((S.erase a).image (fun b => (b-a).val)) ∪ {q}).min'
    (by exact ⟨q, Finset.mem_union_right _ (Finset.mem_singleton_self q)⟩)

def rationalGapTail (q : ℕ) (S : Finset (ZMod q)) (θ : ℚ) : ℚ :=
  ((S.filter (fun a => θ < (cyclicForwardGap q S a : ℚ)*S.card/q)).card : ℚ)/S.card

def rationalFarProportion (q : ℕ) [NeZero q] (S : Finset (ZMod q)) (θ : ℚ)
    (l : ZMod q) : ℚ :=
  ((S.filter (fun a => ∀ w ∈ S,
    θ < (cyclicDistanceNat q (a-l) w : ℚ)*S.card/q)).card : ℚ)/S.card

def spacingCounterexampleSet : Finset (ZMod 6) := {0,1,2,4}

theorem spacing_counterexample_gap_tails :
    rationalGapTail 6 spacingCounterexampleSet (12*(1/10))=1/2 ∧
    rationalGapTail 6 spacingCounterexampleSet (2*(1/10))=1 ∧
    rationalGapTail 6 spacingCounterexampleSet ((12-2)*(1/10))=1/2 := by
  decide +kernel

theorem spacing_counterexample_far_values :
    rationalFarProportion 6 spacingCounterexampleSet (1/10) 0=0 ∧
    rationalFarProportion 6 spacingCounterexampleSet (1/10) 1=1/2 ∧
    rationalFarProportion 6 spacingCounterexampleSet (1/10) 2=1/4 ∧
    rationalFarProportion 6 spacingCounterexampleSet (1/10) 4=1/4 := by
  decide +kernel

theorem spacing_counterexample_strict_fraction :
    (((spacingCounterexampleSet.filter (fun l =>
      (rationalGapTail 6 spacingCounterexampleSet (12*(1/10))+
        rationalGapTail 6 spacingCounterexampleSet (2*(1/10))-1)/2 <
          rationalFarProportion 6 spacingCounterexampleSet (1/10) l)).card : ℚ)/
            spacingCounterexampleSet.card) = 1/4 := by
  decide +kernel

theorem quoted_strict_spacing_bound_fails :
    (((spacingCounterexampleSet.filter (fun l =>
      (rationalGapTail 6 spacingCounterexampleSet (12*(1/10))+
        rationalGapTail 6 spacingCounterexampleSet (2*(1/10))-1)/2 <
          rationalFarProportion 6 spacingCounterexampleSet (1/10) l)).card : ℚ)/
            spacingCounterexampleSet.card) <
      rationalGapTail 6 spacingCounterexampleSet (2*(1/10))-
        rationalGapTail 6 spacingCounterexampleSet ((12-2)*(1/10)) := by
  decide +kernel

end PrimeSquares
