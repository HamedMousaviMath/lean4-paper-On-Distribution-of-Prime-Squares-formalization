import PrimeSquares.UnitRationalReduction

namespace PrimeSquares

theorem unitRational_canonical (q : ℕ) [NeZero q] (u : (ZMod q)ˣ) :
    unitRational q u ∈ Set.Ico (0 : ℚ) 1 := by
  have hq : (0 : ℚ) < q := by exact_mod_cast NeZero.pos q
  refine ⟨div_nonneg (Nat.cast_nonneg _) hq.le,?_⟩
  apply (div_lt_one hq).mpr
  exact_mod_cast ZMod.val_lt (u : ZMod q)

theorem unitRational_mem_centers {q M : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) (h : q ≤ M) : unitRational q u ∈ canonicalRationalCenters M := by
  rw [mem_canonicalRationalCenters]
  exact ⟨unitRational_canonical q u,by rw [unitRational_den];exact h⟩

end PrimeSquares
