import PrimeSquares.CanonicalRationalCenters
import PrimeSquares.MajorArcGeometry

namespace PrimeSquares

theorem primeCircle_coe_integer_shift (ξ : ℝ) (k : ℤ) :
    ((ξ+(k : ℝ) : ℝ) : PrimeCircle) = (ξ : PrimeCircle) := by
  have hz : ((k : ℝ) : PrimeCircle) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨k,by simp⟩
  rw [AddCircle.coe_add,hz,add_zero]

theorem canonicalLift_den_separation {r s : ℚ} {k l : ℤ} {D : ℝ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (hs : s ∈ Set.Ico (0 : ℚ) 1)
    (hrD : (r.den : ℝ) ≤ D) (hsD : (s.den : ℝ) ≤ D)
    (hne : r ≠ s ∨ k ≠ l) :
    1/D^2 ≤ |(r : ℝ)-(s : ℝ)-((k : ℝ)-(l : ℝ))| := by
  have hrd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hsd : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  have hD : 0 < D := hrd.trans_le hrD
  by_cases hrs : r = s
  · have hkl : k ≠ l := by
      rcases hne with h | h
      · exact (h hrs).elim
      · exact h
    have hi := integer_cast_abs_one_le (sub_ne_zero.mpr hkl)
    have hDone : (1 : ℝ) ≤ D := (by exact_mod_cast r.den_pos : (1 : ℝ) ≤ r.den).trans hrD
    have hDsq : (1 : ℝ) ≤ D^2 := one_le_pow₀ hDone
    have hb : 1/D^2 ≤ 1 := (div_le_one (sq_pos_of_pos hD)).mpr hDsq
    subst s
    simp only [sub_self,zero_sub,abs_neg]
    exact hb.trans (by simpa only [Int.cast_sub] using hi)
  · have hp : (r.den : ℝ)*s.den ≤ D^2 := by nlinarith
    have hb := one_div_le_one_div_of_le (mul_pos hrd hsd) hp
    exact hb.trans (by
      simpa only [Int.cast_sub] using rational_canonical_lifts_separation r s hr hs hrs (k-l))

theorem canonicalLift_small_arc_unique {r s : ℚ} {k l : ℤ} {D δ ξ : ℝ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (hs : s ∈ Set.Ico (0 : ℚ) 1)
    (hrD : (r.den : ℝ) ≤ D) (hsD : (s.den : ℝ) ≤ D)
    (hwidth : 2*δ < 1/D^2)
    (hξr : |ξ+(k : ℝ)-(r : ℝ)| ≤ δ)
    (hξs : |ξ+(l : ℝ)-(s : ℝ)| ≤ δ) : r = s ∧ k = l := by
  by_contra h
  have hn : r ≠ s ∨ k ≠ l := by tauto
  have hsep := canonicalLift_den_separation hr hs hrD hsD hn
  have hb : |(r : ℝ)-(s : ℝ)-((k : ℝ)-(l : ℝ))| ≤ 2*δ := by
    calc
      _ = |(ξ+(l : ℝ)-(s : ℝ))-(ξ+(k : ℝ)-(r : ℝ))| := by congr 1;ring
      _ ≤ |ξ+(l : ℝ)-(s : ℝ)|+|ξ+(k : ℝ)-(r : ℝ)| := by
        simpa only [sub_zero,zero_sub,abs_neg] using
          abs_sub_le (ξ+(l : ℝ)-(s : ℝ)) 0 (ξ+(k : ℝ)-(r : ℝ))
      _ ≤ δ+δ := add_le_add hξs hξr
      _ = _ := by ring
  linarith

theorem canonicalLift_major_arc_unique {r s : ℚ} {k l : ℤ} {N R ξ : ℝ}
    (hN : 0 < N) (hR : 1 ≤ R) (hsep : 2*R^3 < N^2)
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (hs : s ∈ Set.Ico (0 : ℚ) 1)
    (hrR : (r.den : ℝ) ≤ R) (hsR : (s.den : ℝ) ≤ R)
    (hξr : |ξ+(k : ℝ)-(r : ℝ)| ≤ R/((r.den : ℝ)*N^2))
    (hξs : |ξ+(l : ℝ)-(s : ℝ)| ≤ R/((s.den : ℝ)*N^2)) : r = s ∧ k = l := by
  have hRp : 0 < R := by linarith
  have hw : 2*(R/N^2) < 1/R^2 := by
    rw [←mul_div_assoc,div_lt_div_iff₀ (sq_pos_of_pos hN) (sq_pos_of_pos hRp)]
    nlinarith only [hsep]
  have hrd : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
  have hsd : (1 : ℝ) ≤ s.den := by exact_mod_cast s.den_pos
  have hradius : R/((r.den : ℝ)*N^2) ≤ R/N^2 :=
    div_le_div_of_nonneg_left hRp.le (sq_pos_of_pos hN) (by nlinarith [sq_nonneg N])
  have sradius : R/((s.den : ℝ)*N^2) ≤ R/N^2 :=
    div_le_div_of_nonneg_left hRp.le (sq_pos_of_pos hN) (by nlinarith [sq_nonneg N])
  exact canonicalLift_small_arc_unique hr hs hrR hsR hw (hξr.trans hradius) (hξs.trans sradius)

theorem canonicalLift_other_outside {r₀ r : ℚ} {k : ℤ} {N R ξ : ℝ}
    (hN : 0 < N) (hR : 1 ≤ R) (hsep : 2*R^3 < N^2)
    (hr₀ : r₀ ∈ Set.Ico (0 : ℚ) 1) (hr : r ∈ Set.Ico (0 : ℚ) 1)
    (hr₀R : (r₀.den : ℝ) ≤ R) (hrR : (r.den : ℝ) ≤ R)
    (hξ : |ξ-(r₀ : ℝ)| ≤ R/((r₀.den : ℝ)*N^2))
    (hne : r ≠ r₀ ∨ k ≠ 0) :
    R/((r.den : ℝ)*N^2) < |ξ+(k : ℝ)-(r : ℝ)| := by
  by_contra h
  have hu := canonicalLift_major_arc_unique (k := (0 : ℤ)) (l := k) hN hR hsep
    hr₀ hr hr₀R hrR (by simpa only [Int.cast_zero,add_zero] using hξ) (le_of_not_gt h)
  rcases hne with hn | hn
  · exact hn hu.1.symm
  · exact hn hu.2.symm

theorem cutoffScale_wrapped_unique {r t : ℚ} {k l : ℤ} {ξ : ℝ} {s : ℕ}
    (hs : 2 ≤ s) (hr : r ∈ Set.Ico (0 : ℚ) 1) (ht : t ∈ Set.Ico (0 : ℚ) 1)
    (hrd : (r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (htd : (t.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (har : sourceArcCutoffScale s (ξ+(k : ℝ)-(r : ℝ)) ≠ 0)
    (hat : sourceArcCutoffScale s (ξ+(l : ℝ)-(t : ℝ)) ≠ 0) : r = t ∧ k = l :=
  canonicalLift_small_arc_unique hr ht hrd htd (dyadic_cutoff_width hs)
    (sourceArcCutoffScale_radius s har).le (sourceArcCutoffScale_radius s hat).le

end PrimeSquares
