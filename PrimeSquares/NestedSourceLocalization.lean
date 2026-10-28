import PrimeSquares.WeightedAnnularBlockBounds
import PrimeSquares.CircleSourceCutoffWitness
import PrimeSquares.CanonicalLiftArcUniqueness

namespace PrimeSquares

theorem circleSourceCutoff_one_on_inner {s t : ℕ} (ht : 1 ≤ t)
    (hst : 2*(16 : ℝ)^t ≤ (16 : ℝ)^s) (r : ℚ) (θ : PrimeCircle)
    (hz : circleSourceCutoff s r θ ≠ 0) : circleSourceCutoff t r θ=1 := by
  let ξ := (AddCircle.equivIco 1 (-(1/2) : ℝ) θ : ℝ)
  have he : (ξ : PrimeCircle)=θ := AddCircle.coe_equivIco
  rw [←he] at hz ⊢
  obtain ⟨k,hk⟩ := circleSourceCutoff_nonzero_lift ξ hz
  have hb : sourceArcCutoffScale t (ξ-(r : ℝ)+(k : ℝ))=1 := by
    apply sourceArcCutoffScale_core
    exact (sourceArcCutoffScale_radius s hk).le.trans
      (one_div_le_one_div_of_le (by positivity) hst)
  rw [circleSourceCutoff_eq_lift ht r ξ k (by rw [hb];norm_num),hb,Complex.ofReal_one]

theorem circleAnnularSource_localized {s t N : ℕ} (hN : 1 ≤ N) (hs : 1 ≤ s)
    (ht : 1 ≤ t) (hst : 2*(16 : ℝ)^t ≤ (16 : ℝ)^s) (β : ℝ) (r : ℚ) :
    circleAnnularSource N hN β s r=
      circleAnnularSource N hN β s r*circleSourceCutoff t r := by
  ext θ
  change circleAnnularSource N hN β s r θ=
    circleAnnularSource N hN β s r θ*circleSourceCutoff t r θ
  by_cases hz : circleSourceCutoff s r θ=0
  · rw [circleAnnularSource_zero_of_cutoff N hN β hs r θ hz,zero_mul]
  · rw [circleSourceCutoff_one_on_inner ht hst r θ hz,mul_one]

theorem circleSourceCutoff_general_disjoint {t : ℕ} {D : ℝ}
    {r u : ℚ} (hr : r ∈ Set.Ico (0 : ℚ) 1) (hu : u ∈ Set.Ico (0 : ℚ) 1)
    (hne : r ≠ u) (hrD : (r.den : ℝ) ≤ D) (huD : (u.den : ℝ) ≤ D)
    (hw : 2*(1/(16 : ℝ)^t)<1/D^2) (θ : PrimeCircle) :
    circleSourceCutoff t r θ=0 ∨ circleSourceCutoff t u θ=0 := by
  let ξ := (AddCircle.equivIco 1 (-(1/2) : ℝ) θ : ℝ)
  have he : (ξ : PrimeCircle)=θ := AddCircle.coe_equivIco
  rw [←he]
  by_cases hz : circleSourceCutoff t r (ξ : PrimeCircle)=0
  · exact Or.inl hz
  right
  by_contra hz'
  obtain ⟨k,hk⟩ := circleSourceCutoff_nonzero_lift ξ hz
  obtain ⟨l,hl⟩ := circleSourceCutoff_nonzero_lift ξ hz'
  exact hne (canonical_lift_small_arc_unique hr hu hrD huD hw k l
    (sourceArcCutoffScale_radius t hk).le (sourceArcCutoffScale_radius t hl).le)

theorem predecessorSourceCutoff_geometry {s : ℕ} (hs : 4 ≤ s) :
    1 ≤ s-1 ∧ 2*(16 : ℝ)^(s-1) ≤ (16 : ℝ)^s ∧
      2*(1/(16 : ℝ)^(s-1))<1/((2 : ℝ)^(s+1))^2 := by
  have hs1 : s-1+1=s := by omega
  have hp : (16 : ℝ)^s=(16 : ℝ)^(s-1)*16 := by rw [←pow_succ,hs1]
  refine ⟨by omega,by rw [hp];nlinarith [show (0 : ℝ) ≤ (16 : ℝ)^(s-1) by positivity],?_⟩
  have ha : (16 : ℝ) ≤ (2 : ℝ)^s := by
    have h : (2 : ℕ)^4 ≤ (2 : ℕ)^s := Nat.pow_le_pow_right (by norm_num) hs
    exact_mod_cast h
  have hpos : (0 : ℝ)<(2 : ℝ)^s := by positivity
  have he : (16 : ℝ)^(s-1)*16=((2 : ℝ)^s)^4 := by
    rw [←hp,dyadic_sixteen_scale]
  rw [show (2 : ℝ)^(s+1)=(2 : ℝ)^s*2 from pow_succ _ _]
  rw [mul_one_div,div_lt_div_iff₀ (by positivity) (by positivity)]
  have hsq : (128 : ℝ)<((2 : ℝ)^s)^2 := by nlinarith only [ha]
  have h := mul_lt_mul_of_pos_right hsq (sq_pos_of_pos hpos)
  nlinarith only [h,he]

end PrimeSquares
