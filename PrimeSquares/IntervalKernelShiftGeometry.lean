import PrimeSquares.ContinuousAnnularKernelRegularity

set_option autoImplicit false
namespace PrimeSquares

theorem interval_shift_membership_boundary {a b x h : ℝ}
    (hc : (x-h∈Set.Icc a b ∧ x∉Set.Icc a b) ∨
      (x∈Set.Icc a b ∧ x-h∉Set.Icc a b)) :
    x∈Set.Icc (a-|h|) (a+|h|) ∨ x∈Set.Icc (b-|h|) (b+|h|) := by
  have h1 := neg_abs_le h
  have h2 := le_abs_self h
  have h0 := abs_nonneg h
  rcases hc with ⟨hy,hx⟩ | ⟨hx,hy⟩
  · by_cases hxa : a≤x
    · have hxb : b<x := lt_of_not_ge (fun hxb => hx ⟨hxa,hxb⟩)
      right
      constructor <;> linarith [hy.2]
    · have hxa' := lt_of_not_ge hxa
      left
      constructor <;> linarith [hy.1]
  · by_cases hya : a≤x-h
    · have hyb : b<x-h := lt_of_not_ge (fun hyb => hy ⟨hya,hyb⟩)
      right
      constructor <;> linarith [hx.2]
    · have hya' := lt_of_not_ge hya
      left
      constructor <;> linarith [hx.1]

noncomputable def intervalKernelShiftEnvelope (a b L B h x : ℝ) : ℝ :=
  L*|h| *(Set.Icc a b).indicator (fun _ => (1 : ℝ)) x +
  B*((Set.Icc (a-|h|) (a+|h|)).indicator (fun _ => (1 : ℝ)) x +
    (Set.Icc (b-|h|) (b+|h|)).indicator (fun _ => (1 : ℝ)) x)

theorem interval_kernel_shift_envelope {a b L B : ℝ} (f : ℝ→ℝ)
    (hL : 0≤L) (hB : 0≤B)
    (hb : ∀ x∈Set.Icc a b,|f x|≤B)
    (hl : ∀ x∈Set.Icc a b,∀ y∈Set.Icc a b,|f x-f y|≤L*|x-y|)
    (h x : ℝ) :
    |(Set.Icc a b).indicator f (x-h)-(Set.Icc a b).indicator f x|≤
      intervalKernelShiftEnvelope a b L B h x := by
  have hn (c d : ℝ) : 0≤(Set.Icc c d).indicator (fun _ => (1 : ℝ)) x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hnon : 0≤ intervalKernelShiftEnvelope a b L B h x := by
    unfold intervalKernelShiftEnvelope
    exact add_nonneg (mul_nonneg (mul_nonneg hL (abs_nonneg h)) (hn a b))
      (mul_nonneg hB (add_nonneg (hn (a-|h|) (a+|h|)) (hn (b-|h|) (b+|h|))))
  have hs (hc : (x-h∈Set.Icc a b ∧ x∉Set.Icc a b) ∨
      (x∈Set.Icc a b ∧ x-h∉Set.Icc a b)) :
      B≤ intervalKernelShiftEnvelope a b L B h x := by
    have hsum : 1≤(Set.Icc (a-|h|) (a+|h|)).indicator (fun _ => (1 : ℝ)) x +
        (Set.Icc (b-|h|) (b+|h|)).indicator (fun _ => (1 : ℝ)) x := by
      rcases interval_shift_membership_boundary hc with ha | hb'
      · rw [Set.indicator_of_mem ha]
        linarith [hn (b-|h|) (b+|h|)]
      · rw [Set.indicator_of_mem hb']
        linarith [hn (a-|h|) (a+|h|)]
    have hm := mul_le_mul_of_nonneg_left hsum hB
    unfold intervalKernelShiftEnvelope
    nlinarith [mul_nonneg (mul_nonneg hL (abs_nonneg h)) (hn a b)]
  by_cases hx : x∈Set.Icc a b <;> by_cases hy : x-h∈Set.Icc a b
  · rw [Set.indicator_of_mem hy,Set.indicator_of_mem hx]
    have ht := hl (x-h) hy x hx
    have hd : |x-h-x|=|h| := by rw [show x-h-x = -h by ring,abs_neg]
    rw [hd] at ht
    unfold intervalKernelShiftEnvelope
    rw [Set.indicator_of_mem hx]
    nlinarith [mul_nonneg hB (add_nonneg (hn (a-|h|) (a+|h|)) (hn (b-|h|) (b+|h|)))]
  · rw [Set.indicator_of_notMem hy,Set.indicator_of_mem hx,zero_sub,abs_neg]
    exact (hb x hx).trans (hs (Or.inr ⟨hx,hy⟩))
  · rw [Set.indicator_of_mem hy,Set.indicator_of_notMem hx,sub_zero]
    exact (hb (x-h) hy).trans (hs (Or.inl ⟨hy,hx⟩))
  · rw [Set.indicator_of_notMem hy,Set.indicator_of_notMem hx,sub_self,abs_zero]
    exact hnon

end PrimeSquares
