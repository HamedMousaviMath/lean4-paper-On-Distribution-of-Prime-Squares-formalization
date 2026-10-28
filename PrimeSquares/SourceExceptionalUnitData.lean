import PrimeSquares.SourceInducedCharacters

namespace PrimeSquares

theorem sourceExceptionalSelector_unitRational (q₀ q : ℕ) [NeZero q]
    (active : Bool) (u : (ZMod q)ˣ) :
    sourceExceptionalSelector q₀ active (unitRational q u)=if active=true ∧ q₀ ∣ q then 1 else 0 := by
  simp only [sourceExceptionalSelector,unitRational_den]

theorem sourceInducedCharacter_gauss_coordinates (q₀ : ℕ) (χ₀ : DirichletCharacter ℂ q₀)
    (r : ℚ) (q : ℕ) [NeZero q] (u : (ZMod q)ˣ)
    (hd : r.den=q) (hn : r.num=((u : ZMod q).val : ℤ)) :
    letI : NeZero r.den := ⟨r.den_pos.ne'⟩
    twistedSquareSum r.den (sourceInducedCharacter q₀ χ₀ r) (r.num : ZMod r.den)=
    if h : q₀ ∣ q then twistedSquareSum q (DirichletCharacter.changeLevel h χ₀) u
    else twistedSquareSum q 1 u := by
  subst q
  simp only [sourceInducedCharacter,hn,Int.cast_natCast,ZMod.natCast_zmod_val]
  split_ifs <;> rfl

theorem sourceInducedCharacter_unit_gauss (q₀ q : ℕ) [NeZero q]
    (χ₀ : DirichletCharacter ℂ q₀) (u : (ZMod q)ˣ) :
    letI : NeZero (unitRational q u).den := ⟨(unitRational q u).den_pos.ne'⟩
    twistedSquareSum (unitRational q u).den (sourceInducedCharacter q₀ χ₀ (unitRational q u))
      ((unitRational q u).num : ZMod (unitRational q u).den)=
    if h : q₀ ∣ q then twistedSquareSum q (DirichletCharacter.changeLevel h χ₀) u
    else twistedSquareSum q 1 u :=
  sourceInducedCharacter_gauss_coordinates q₀ χ₀ (unitRational q u) q u
    (unitRational_den q u) (unitRational_num q u)

end PrimeSquares
