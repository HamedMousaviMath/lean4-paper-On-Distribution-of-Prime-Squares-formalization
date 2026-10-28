import PrimeSquares.SourceLowCircleIdentity
import PrimeSquares.SourceExceptionalFiniteSum
import PrimeSquares.SourceOrdinaryLowIdentity

open Finset
namespace PrimeSquares

theorem canonicalOrdinarySum (N : ℕ) (hN : 1 ≤ N) {Q : ℝ} (hQ : 0 < Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (M : ℕ) (hM : ⌊Q⌋₊ ≤ M) :
    (∑ r ∈ canonicalRationalCenters M,if (r.den : ℝ) ≤ Q
      then ordinaryRationalCircleLow N hN Q hQ hb r else 0)=realOrdinaryLowModel N hN Q hQ hb := by
  classical
  rw [←sum_filter,canonicalCenters_real_filter hQ.le hM,canonicalCenters_sum_units]
  unfold realOrdinaryLowModel
  apply sum_congr rfl
  intro q _
  exact denominatorUnitSum_ordinary N hN hQ hb q

theorem truncatedSourceLow_identity {N : ℕ} (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (active : Bool) (β : ℝ) (M : ℕ) {Q R : ℝ}
    (hQ : 1 ≤ Q) (hQR : Q ≤ R) (hWR : Q*(q₀ : ℝ)/conductorMajorant q₀ ≤ R)
    (hM : (M : ℝ) ≤ R) (hQM : ⌊Q⌋₊ ≤ M) (hb : 2*R^4 ≤ (N : ℝ)^2) :
    circleLowModel (canonicalRationalCenters M) N hN q₀ Q (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β=
      realOrdinaryLowModel N hN Q (by linarith) (source_low_width_budget hQ hQR hb)-
      (if active=true then realExceptionalLowModel N hN q₀ χ₀ Q (by linarith)
        (source_low_width_budget hQ hQR hb) β M else 0) := by
  classical
  have hQp : 0 < Q := by linarith
  have hw := source_low_width_budget hQ hQR hb
  unfold circleLowModel
  calc
    _ = ∑ r ∈ canonicalRationalCenters M,
        ((if (r.den : ℝ) ≤ Q then ordinaryRationalCircleLow N hN Q hQp hw r else 0)-
        (if active=true ∧ (r.den : ℝ)/(q₀ : ℝ) ≤ Q/conductorMajorant q₀
          then exceptionalRationalCircleLow N hN q₀ χ₀ Q hQp hw β r else 0)) := by
      apply sum_congr rfl
      intro r hr
      have hd : (r.den : ℝ) ≤ R :=
        (by exact_mod_cast (mem_canonicalRationalCenters M r).mp hr |>.2 : (r.den : ℝ) ≤ M).trans hM
      exact sourceCircleLowTerm_identity hN q₀ χ₀ active β r hQp hQR hWR hd hb hw
    _ = _ := by
      rw [sum_sub_distrib,canonicalOrdinarySum N hN hQp hw M hQM,
        canonicalExceptionalSum_active N hN q₀ χ₀ hQp hw β M active]

theorem sourceFullLow_identity {N : ℕ} (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (active : Bool) (β : ℝ) {Q R : ℝ}
    (hQ : 1 ≤ Q) (hQR : Q ≤ R) (hWR : Q*(q₀ : ℝ)/conductorMajorant q₀ ≤ R)
    (hb : 2*R^4 ≤ (N : ℝ)^2) :
    circleLowModel (sourceRationalCenters R) N hN q₀ Q (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β=
      realOrdinaryLowModel N hN Q (by linarith) (source_low_width_budget hQ hQR hb)-
      (if active=true then realExceptionalLowModel N hN q₀ χ₀ Q (by linarith)
        (source_low_width_budget hQ hQR hb) β ⌊R⌋₊ else 0) :=
  truncatedSourceLow_identity hN q₀ χ₀ active β ⌊R⌋₊ hQ hQR hWR
    (Nat.floor_le (by linarith : 0 ≤ R)) (Nat.floor_mono hQR) hb

end PrimeSquares
