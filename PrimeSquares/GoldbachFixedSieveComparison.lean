import PrimeSquares.GoldbachCircleSourceSeed
import PrimeSquares.GoldbachMasterSieveReduction

set_option autoImplicit false
open Finset
namespace PrimeSquares

def GoldbachFixedLowerSievePrime (p : ℕ) : Prop := p.Prime ∧ 3<p ∧ p%4=3

noncomputable def goldbachFixedLowerSifted (n : ℕ) (z : ℝ) : Finset ℕ := by
  classical
  exact (goldbachAdmissibleRepresentations n).filter (fun r=>∀ p : ℕ,
    GoldbachFixedLowerSievePrime p →(p:ℝ)<z →¬p∣r-1)

noncomputable def goldbachFixedLowerSiftedValues (n : ℕ) (z : ℝ) : Finset ℕ :=
  (goldbachFixedLowerSifted n z).image (fun r=>r-1)

def GoldbachFixedUpperSievePrime (ℓ p : ℕ) : Prop := p.Prime ∧ ¬p∣12*ℓ

noncomputable def goldbachFixedUpperSifted (n N ℓ : ℕ) : Finset ℕ := by
  classical
  exact (goldbachUpperM n N ℓ).filter (fun r=>∀ p : ℕ,
    GoldbachFixedUpperSievePrime ℓ p →(p:ℝ)<goldbachUpperSieveLevel N ℓ →¬p∣r)

noncomputable def goldbachFixedUpperSieveSum (n N : ℕ) (z : ℝ) : ℕ :=
  ∑ ℓ∈goldbachClosedLSet N z,(goldbachFixedUpperSifted n N ℓ).card

noncomputable def goldbachFixedSieveExceptions (n : ℕ) : Finset (ℕ×ℕ) :=
  n.primeFactors.biUnion (fun p=>(n-p^2-1).divisors.image (fun ℓ=>(ℓ,n-p^2)))

noncomputable def goldbachSievePairs (I : Finset ℕ) (F : ℕ→Finset ℕ) : Finset (ℕ×ℕ) :=
  I.biUnion (fun ℓ=>(F ℓ).image (fun r=>(ℓ,r)))

theorem mem_goldbachSievePairs (I : Finset ℕ) (F : ℕ→Finset ℕ) (ℓ r : ℕ) :
    (ℓ,r)∈goldbachSievePairs I F ↔ℓ∈I ∧ r∈F ℓ := by
  classical
  simp [goldbachSievePairs]

theorem goldbachSievePairs_card (I : Finset ℕ) (F : ℕ→Finset ℕ) :
    (goldbachSievePairs I F).card=∑ ℓ∈I,(F ℓ).card := by
  classical
  rw [goldbachSievePairs,card_biUnion]
  · apply sum_congr rfl
    intro ℓ _
    exact card_image_iff.mpr (fun r _ s _ h=>Prod.mk.inj h |>.2)
  · intro a _ b _ hab
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨r,_,hr⟩ := mem_image.mp hx
    obtain ⟨s,_,hs⟩ := mem_image.mp hy
    exact hab (congrArg Prod.fst (hr.trans hs.symm))

theorem goldbach_fixed_lower_subset (n : ℕ) (z : ℝ) :
    goldbachFixedLowerSifted n z⊆goldbachSifted n z := by
  classical
  intro r hr
  obtain ⟨hra,hs⟩ := mem_filter.mp hr
  apply mem_filter.mpr
  refine ⟨hra,?_⟩
  intro p hp hpz
  by_cases hp3 : 3<p
  · exact hs p ⟨hp.1,hp3,hp.2.1⟩ hpz
  · have he : p=3 := by have := hp.2.1;omega
    subst p
    have hres := (mem_filter.mp hra).2
    intro hd
    obtain ⟨k,hk⟩ := hd
    omega

theorem goldbach_fixed_lower_values_subset (n : ℕ) (z : ℝ) :
    goldbachFixedLowerSiftedValues n z⊆goldbachSiftedValues n z :=
  image_subset_image (goldbach_fixed_lower_subset n z)

theorem goldbach_fixed_lower_count (n : ℕ) (z : ℝ) :
    (goldbachFixedLowerSiftedValues n z).card≤(goldbachSiftedValues n z).card :=
  card_le_card (goldbach_fixed_lower_values_subset n z)

theorem goldbach_fixed_upper_subset (n N ℓ : ℕ) :
    goldbachFixedUpperSifted n N ℓ⊆goldbachUpperSifted n N ℓ := by
  classical
  intro r hr
  obtain ⟨hrM,hs⟩ := mem_filter.mp hr
  refine mem_filter.mpr ⟨hrM,?_⟩
  intro p hp hpz
  exact hs p ⟨hp.1,fun hd=>hp.2 (dvd_mul_of_dvd_left hd n)⟩ hpz

theorem goldbach_fixed_upper_exception {n N ℓ r : ℕ} (hn : 0<n) (hℓ : 0<ℓ)
    (hr : r∈goldbachUpperSifted n N ℓ) (hne : r∉goldbachFixedUpperSifted n N ℓ) :
    (ℓ,r)∈goldbachFixedSieveExceptions n := by
  classical
  obtain ⟨hrM,hs⟩ := mem_filter.mp hr
  have hnot : ¬∀ p : ℕ,GoldbachFixedUpperSievePrime ℓ p →
      (p:ℝ)<goldbachUpperSieveLevel N ℓ →¬p∣r :=
    fun h=>hne (mem_filter.mpr ⟨hrM,h⟩)
  push Not at hnot
  obtain ⟨p,hp,hpz,hpr⟩ := hnot
  have hpn : p∣n := by
    by_contra hh
    have hpDep : GoldbachUpperSievePrime n ℓ p := ⟨hp.1,fun h=>by
      rcases hp.1.dvd_mul.mp h with h₀|h₁
      · exact hp.2 h₀
      · exact hh h₁⟩
    exact hs p hpDep hpz hpr
  obtain ⟨_,t,q,ht,_,hq,_,hrEq,hEq⟩ := mem_filter.mp hrM
  have hpq : p=q := by
    have hd : p∣q^2 := (Nat.dvd_add_iff_right hpr).mpr (by rw [hEq];exact hpn)
    exact (Nat.prime_dvd_prime_iff_eq hp.1 hq).mp (hp.1.dvd_of_dvd_pow hd)
  have hprN : p∈n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp.1,hpn,hn.ne'⟩
  have hrVal : r=n-p^2 := by rw [hpq];omega
  have hdiv : ℓ∣n-p^2-1 := ⟨t,by omega⟩
  have hpos : 0<n-p^2-1 := by
    have := ht.pos
    have hh := Nat.mul_pos hℓ ht.pos
    omega
  apply mem_biUnion.mpr
  refine ⟨p,hprN,mem_image.mpr ⟨ℓ,Nat.mem_divisors.mpr ⟨hdiv,hpos.ne'⟩,?_⟩⟩
  exact Prod.ext rfl hrVal.symm

theorem goldbach_fixed_sieve_exceptions_card (n : ℕ) :
    (goldbachFixedSieveExceptions n).card≤∑ p∈n.primeFactors,(n-p^2-1).divisors.card := by
  classical
  apply card_biUnion_le.trans
  exact sum_le_sum (fun p _=>card_image_le)

theorem goldbach_fixed_upper_count_finite {n N : ℕ} (hn : 0<n)
    (I J : Finset ℕ) (hIJ : I⊆J) (hI : ∀ ℓ∈I,0<ℓ) :
    (∑ ℓ∈I,(goldbachUpperSifted n N ℓ).card)≤
      (∑ ℓ∈J,(goldbachFixedUpperSifted n N ℓ).card)+∑ p∈n.primeFactors,(n-p^2-1).divisors.card := by
  classical
  have hsub : goldbachSievePairs I (goldbachUpperSifted n N)⊆
      goldbachSievePairs J (goldbachFixedUpperSifted n N)∪goldbachFixedSieveExceptions n := by
    rintro ⟨ℓ,r⟩ hx
    obtain ⟨hℓ,hr⟩ := (mem_goldbachSievePairs I _ ℓ r).mp hx
    by_cases hf : r∈goldbachFixedUpperSifted n N ℓ
    · exact mem_union_left _ ((mem_goldbachSievePairs J _ ℓ r).mpr ⟨hIJ hℓ,hf⟩)
    · exact mem_union_right _ (goldbach_fixed_upper_exception hn (hI ℓ hℓ) hr hf)
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  rw [goldbachSievePairs_card,goldbachSievePairs_card] at hh
  exact hh.trans (Nat.add_le_add_left (goldbach_fixed_sieve_exceptions_card n) _)

theorem goldbach_closed_multiplier_positive {N ℓ : ℕ} {z : ℝ}
    (hℓ : ℓ∈goldbachClosedLSet N z) : 0<ℓ := by
  obtain ⟨u,p,hu,he,_,hp,_⟩ := mem_goldbachClosedLSet.mp hℓ
  rw [he]
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) hu) hp.pos

theorem goldbach_fixed_upper_source_count_finite {n N : ℕ} (hn : 0<n) (z : ℝ) :
    goldbachUpperSieveSum n N z≤goldbachFixedUpperSieveSum n N z+
      ∑ p∈n.primeFactors,(n-p^2-1).divisors.card := by
  apply goldbach_fixed_upper_count_finite hn (goldbachClosedLn n N z) (goldbachClosedLSet N z)
  · exact filter_subset _ _
  · intro ℓ hℓ
    exact goldbach_closed_multiplier_positive (mem_filter.mp hℓ).1

end PrimeSquares
