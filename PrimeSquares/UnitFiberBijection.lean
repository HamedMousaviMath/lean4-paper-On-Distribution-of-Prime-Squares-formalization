import PrimeSquares.CanonicalDenominatorFibers

namespace PrimeSquares

theorem unitRational_surjective_fiber (q : ℕ) [NeZero q] {r : ℚ}
    (hr : r ∈ canonicalDenominatorFiber q) : ∃ u : (ZMod q)ˣ,unitRational q u=r := by
  have hd := (mem_canonicalDenominatorFiber q r).mp hr
  have he : r.den=q := hd.2
  subst q
  exact ⟨rationalNumeratorUnit r,unitRational_numerator_recovery (Finset.mem_filter.mp hr).1⟩

noncomputable def unitFiberMap (q : ℕ) [NeZero q] (u : (ZMod q)ˣ) :
    {r : ℚ // r ∈ canonicalDenominatorFiber q} :=
  ⟨unitRational q u,unitRational_mem_fiber q u⟩

theorem unitFiberMap_bijective (q : ℕ) [NeZero q] : Function.Bijective (unitFiberMap q) := by
  constructor
  · intro u v h
    exact unitRational_injective q (congrArg Subtype.val h)
  · intro ⟨r,hr⟩
    obtain ⟨u,hu⟩ := unitRational_surjective_fiber q hr
    exact ⟨u,Subtype.ext hu⟩

end PrimeSquares
