import PrimeSquares.GoldbachLogarithmicReduction

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem one_mod_four_prime_divisors_pos {u : ℕ}
    (h : ∀ p : ℕ,p.Prime → p∣u → p%4=1) : 0<u := by
  by_contra hh
  have hu : u=0 := by omega
  have hc := h 3 (by decide) (by rw [hu]; exact dvd_zero _)
  norm_num at hc

theorem goldbachClosedL_source_form {N ℓ : ℕ} {z : ℝ} :
    GoldbachClosedL N z ℓ ↔ ∃ u p : ℕ,ℓ=2*u*p ∧ (u:ℝ)<(N:ℝ)^2/(2*z^2) ∧
      p.Prime ∧ p%4=3 ∧ z≤(p:ℝ) ∧ (p:ℝ)<Real.sqrt ((N:ℝ)^2/(2*(u:ℝ))) ∧
      ∀ s : ℕ,s.Prime → s∣u → s%4=1 := by
  constructor
  · rintro ⟨u,p,_,h⟩
    exact ⟨u,p,h⟩
  · rintro ⟨u,p,h⟩
    exact ⟨u,p,one_mod_four_prime_divisors_pos h.2.2.2.2.2.2,h⟩

noncomputable def goldbachAdmissibleNumbers (N : ℕ) : Finset ℕ :=
  (range (N^2)).filter (fun n => n%24=12)

noncomputable def goldbachLargeNumbers (N : ℕ) (H : ℝ) : Finset ℕ := by
  classical
  exact (goldbachAdmissibleNumbers N).filter (fun n => H≤(n:ℝ))

noncomputable def goldbachSmallNumbers (N : ℕ) (H : ℝ) : Finset ℕ := by
  classical
  exact (range (N^2)).filter (fun n => (n:ℝ)<H)

theorem goldbachSmallNumbers_card_le_ceil (N : ℕ) (H : ℝ) :
    (goldbachSmallNumbers N H).card≤⌈H⌉₊ := by
  classical
  have hh : goldbachSmallNumbers N H⊆range ⌈H⌉₊ := by
    intro n hn
    exact mem_range.mpr (Nat.lt_ceil.mpr (mem_filter.mp hn).2)
  exact (card_le_card hh).trans_eq (card_range _)

theorem goldbachLargeNumbers_range {N : ℕ} {H : ℝ} (hH : 13≤H) :
    ∀ n∈goldbachLargeNumbers N H,12<n ∧ n%24=12 ∧ n<N^2 := by
  intro n hn
  obtain ⟨hna,hHn⟩ := mem_filter.mp hn
  obtain ⟨hnrange,hnres⟩ := mem_filter.mp hna
  have hn13 : (13:ℝ)≤n := hH.trans hHn
  exact ⟨by exact_mod_cast (show (12:ℝ)<n by linarith),hnres,mem_range.mp hnrange⟩

theorem goldbach_exceptional_split (N : ℕ) (H : ℝ) :
    goldbachExceptionalSet (goldbachAdmissibleNumbers N)⊆
      goldbachExceptionalSet (goldbachLargeNumbers N H)∪goldbachSmallNumbers N H := by
  classical
  intro n hn
  obtain ⟨hna,hzero⟩ := mem_filter.mp hn
  by_cases hHn : H≤(n:ℝ)
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hna,hHn⟩,hzero⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨(mem_filter.mp hna).1,lt_of_not_ge hHn⟩)

theorem goldbach_full_exceptional_count {N : ℕ} {H D : ℝ} (hH : 1≤H)
    (hlarge : ((goldbachExceptionalSet (goldbachLargeNumbers N H)).card:ℝ)≤D*H) :
    ((goldbachExceptionalSet (goldbachAdmissibleNumbers N)).card:ℝ)≤(D+2)*H := by
  have hcard := (card_le_card (goldbach_exceptional_split N H)).trans (card_union_le _ _)
  have hsmall := goldbachSmallNumbers_card_le_ceil N H
  have hceil := Nat.ceil_lt_add_one (by linarith : 0≤H)
  have hc : ((goldbachExceptionalSet (goldbachAdmissibleNumbers N)).card:ℝ)≤
      ((goldbachExceptionalSet (goldbachLargeNumbers N H)).card:ℝ)+(⌈H⌉₊:ℝ) := by
    exact_mod_cast hcard.trans (Nat.add_le_add (Nat.le_refl _) hsmall)
  nlinarith only [hc,hlarge,hceil,hH]

/-- The complete Section9 final-count deduction. The lower/upper sieve,
main-term gap and mean-square inputs are still internal paper obligations;
this reduction is not credited as a completed Goldbach headline theorem. -/
theorem goldbach_section9_count_reduction (H : PrimitiveTwoSquaresCriterion)
    {N : ℕ} (hN : 2≤N) {α : ℝ} (hα1 : 1<α) (hα2 : α<2)
    (M a b E₁ E₂ : ℕ→ℝ) {t κ A C B : ℝ}
    (hκ : 0<κ) (hB : 0≤B) (hlog : 1≤Real.log N)
    (hcut : 13≤(N:ℝ)^2*(Real.log N)^(-A))
    (ht : κ*(N:ℝ)*(Real.log N)^(-C)≤t)
    (hlower : ∀ n∈goldbachLargeNumbers N ((N:ℝ)^2*(Real.log N)^(-A)),
      a n*M n+E₁ n≤((goldbachSiftedValues n ((N:ℝ)^(1/α))).card:ℝ))
    (hupper : ∀ n∈goldbachLargeNumbers N ((N:ℝ)^2*(Real.log N)^(-A)),
      (goldbachUpperSieveSum n N ((N:ℝ)^(1/α)):ℝ)≤b n*M n+E₂ n)
    (hgap : ∀ n∈goldbachLargeNumbers N ((N:ℝ)^2*(Real.log N)^(-A)),2*t≤(a n-b n)*M n)
    (hsmall : ∀ n∈goldbachLargeNumbers N ((N:ℝ)^2*(Real.log N)^(-A)),2*((n-1).primeFactors.card:ℝ)≤t)
    (hsum : (∑ n∈goldbachLargeNumbers N ((N:ℝ)^2*(Real.log N)^(-A)),(E₁ n)^2)+
      (∑ n∈goldbachLargeNumbers N ((N:ℝ)^2*(Real.log N)^(-A)),(E₂ n)^2)≤
        B*(N:ℝ)^4*(Real.log N)^(-(A+2*C+10))) :
    ((goldbachExceptionalSet (goldbachAdmissibleNumbers N)).card:ℝ)≤
      (2*B/κ^2+2)*(N:ℝ)^2*(Real.log N)^(-A) := by
  have hlarge := goldbach_logarithmic_exceptional_bound H hN hα1 hα2
    (goldbachLargeNumbers N ((N:ℝ)^2*(Real.log N)^(-A)))
    (goldbachLargeNumbers_range hcut) M a b E₁ E₂ hκ hB hlog
    (show A+2*C≤A+2*C+10 by linarith) ht hlower hupper hgap hsmall hsum
  have hh := goldbach_full_exceptional_count (by linarith : 1≤(N:ℝ)^2*(Real.log N)^(-A))
    (D:=2*B/κ^2) (by simpa only [mul_assoc] using hlarge)
  exact hh.trans_eq (by ring)

end PrimeSquares
