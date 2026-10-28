import PrimeSquares.SourceLowCenteredIdentity

namespace PrimeSquares

theorem shiftedCompactLift_ite (p : Prop) [Decidable p] (f : C(ℝ, ℂ))
    (hf : ∀ x,1 ≤ |x| → f x=0) (hs : ∀ x,1 ≤ |x| → (if p then f else 0) x=0) (r : PrimeCircle) :
    circleFrequencyShift (compactCircleLift (if p then f else 0) hs) r=
      if p then circleFrequencyShift (compactCircleLift f hf) r else 0 := by
  by_cases hp : p
  · rw [compactCircleLift_congr _ _ hs hf (ite_eq_left hp),ite_eq_left hp]
  · rw [compactCircleLift_congr _ _ hs (fun _ _ => rfl) (ite_eq_right hp),ite_eq_right hp]
    erw [compactCircleLift_zero]
    exact circleFrequencyShift_zero _

theorem sourceCircleLowTerm_identity {N : ℕ} (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (active : Bool) (β : ℝ) (r : ℚ) {Q R : ℝ}
    (hQ : 0 < Q) (hQR : Q ≤ R) (hWR : Q*(q₀ : ℝ)/conductorMajorant q₀ ≤ R)
    (hr : (r.den : ℝ) ≤ R) (hb : 2*R^4 ≤ (N : ℝ)^2) (hw : 2*Q ≤ (N : ℝ)^2) :
    circleLowTerm N hN q₀ Q (conductorMajorant q₀) (sourceInducedCharacter q₀ χ₀)
      (sourceExceptionalSelector q₀ active) β r=
      (if (r.den : ℝ) ≤ Q then ordinaryRationalCircleLow N hN Q hQ hw r else 0)-
      (if active=true ∧ (r.den : ℝ)/(q₀ : ℝ) ≤ Q/conductorMajorant q₀
        then exceptionalRationalCircleLow N hN q₀ χ₀ Q hQ hw β r else 0) := by
  classical
  let f : C(ℝ, ℂ) := if (r.den : ℝ) ≤ Q then ordinaryCenteredLow N hN Q r else 0
  let g : C(ℝ, ℂ) := if active=true ∧ (r.den : ℝ)/(q₀ : ℝ) ≤ Q/conductorMajorant q₀
    then exceptionalCenteredLow N hN q₀ χ₀ Q β r else 0
  have hf : ∀ x,1 ≤ |x| → f x=0 := by
    intro x hx
    by_cases ho : (r.den : ℝ) ≤ Q
    · simpa only [f,ite_eq_left ho] using ordinaryCenteredLow_support N hN hQ hw r x hx
    · simp only [f,ite_eq_right ho,ContinuousMap.zero_apply]
  have hg : ∀ x,1 ≤ |x| → g x=0 := by
    intro x hx
    by_cases he : active=true ∧ (r.den : ℝ)/(q₀ : ℝ) ≤ Q/conductorMajorant q₀
    · simpa only [g,ite_eq_left he] using exceptionalCenteredLow_support N hN (NeZero.pos q₀) χ₀ hQ hw β r x hx
    · simp only [g,ite_eq_right he,ContinuousMap.zero_apply]
  have hfg : ∀ x,1 ≤ |x| → (f-g) x=0 := by
    intro x hx
    change f x-g x=0
    rw [hf x hx,hg x hx,sub_self]
  have hc := sourceCenteredLow_identity hN q₀ χ₀ active β r hQ hQR hWR hr hb
  change circleFrequencyShift (compactCircleLift _ _) (((r : ℝ) : PrimeCircle))=_
  rw [compactCircleLift_congr _ (f-g) _ hfg hc,compactCircleLift_sub f g hf hg hfg,circleFrequencyShift_sub]
  have ho : circleFrequencyShift (compactCircleLift f hf) (((r : ℝ) : PrimeCircle))=
      if (r.den : ℝ) ≤ Q then ordinaryRationalCircleLow N hN Q hQ hw r else 0 := by
    calc
      _ = if (r.den : ℝ) ≤ Q then circleFrequencyShift (compactCircleLift (ordinaryCenteredLow N hN Q r)
          (ordinaryCenteredLow_support N hN hQ hw r)) (((r : ℝ) : PrimeCircle)) else 0 :=
        shiftedCompactLift_ite _ _ _ hf _
      _ = _ := by
        split_ifs
        · exact ordinaryCenteredLow_circle N hN hQ hw r
        · rfl
  have he : circleFrequencyShift (compactCircleLift g hg) (((r : ℝ) : PrimeCircle))=
      if active=true ∧ (r.den : ℝ)/(q₀ : ℝ) ≤ Q/conductorMajorant q₀
        then exceptionalRationalCircleLow N hN q₀ χ₀ Q hQ hw β r else 0 := by
    calc
      _ = if active=true ∧ (r.den : ℝ)/(q₀ : ℝ) ≤ Q/conductorMajorant q₀ then
          circleFrequencyShift (compactCircleLift (exceptionalCenteredLow N hN q₀ χ₀ Q β r)
            (exceptionalCenteredLow_support N hN (NeZero.pos q₀) χ₀ hQ hw β r)) (((r : ℝ) : PrimeCircle)) else 0 :=
        shiftedCompactLift_ite _ _ _ hg _
      _ = _ := by split_ifs <;> rfl
  rw [ho,he]

end PrimeSquares
