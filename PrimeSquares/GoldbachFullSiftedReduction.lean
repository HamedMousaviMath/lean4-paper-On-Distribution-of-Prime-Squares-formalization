import PrimeSquares.GoldbachFiniteRepresentations

set_option autoImplicit false
open Finset
namespace PrimeSquares

/-- Classical primitive two-square criterion, isolated independently of any
prime, prime-square, sieve or manuscript conclusion. Its proof is not supplied
by this declaration. -/
def PrimitiveTwoSquaresCriterion : Prop :=
  ∀ m : ℕ,m%4=2 →
    (PrimitiveTwoSquares m ↔ ∀ p : ℕ,p.Prime → p%4=3 → ¬p∣m)

noncomputable def goldbachSiftedValues (n : ℕ) (z : ℝ) : Finset ℕ :=
  (goldbachSifted n z).image (fun r => r-1)

theorem goldbachSiftedValues_card (n : ℕ) (z : ℝ) :
    (goldbachSiftedValues n z).card=(goldbachSifted n z).card := by
  classical
  apply card_image_iff.mpr
  intro r hr t ht he
  change r-1=t-1 at he
  have hr' := (mem_goldbachRepresentations.mp (mem_filter.mp (mem_filter.mp hr).1).1).1.two_le
  have ht' := (mem_goldbachRepresentations.mp (mem_filter.mp (mem_filter.mp ht).1).1).1.two_le
  omega

theorem goldbach_full_sifted_inclusion (H : PrimitiveTwoSquaresCriterion)
    {N n : ℕ} (hn : 2≤n) (hsize : n≤N^2) :
    goldbachSifted n ((N:ℝ)^2)⊆goldbachGoodRepresentations n∪goldbachDivisorExceptions n := by
  classical
  intro r hr
  obtain ⟨hra,hsift⟩ := mem_filter.mp hr
  obtain ⟨hrr,hres⟩ := mem_filter.mp hra
  obtain ⟨hrp,q,hq,he⟩ := mem_goldbachRepresentations.mp hrr
  by_cases hex : r∈goldbachDivisorExceptions n
  · exact mem_union_right _ hex
  · apply mem_union_left
    apply mem_filter.mpr
    refine ⟨hrr,(H (r-1) (by omega)).mpr ?_⟩
    intro p hp hp4 hpr
    by_cases hpn : p∣n-1
    · exact hex (goldbach_shared_divisor_exception hn hrp.one_le hq hp he hpr hpn)
    · have hple : p≤r-1 := Nat.le_of_dvd (by have hh := hrp.two_le; omega) hpr
      have hq2 : 0<q^2 := pow_pos hq.pos _
      have hpN : (p:ℝ)<(N:ℝ)^2 := by exact_mod_cast (show p<N^2 by omega)
      exact hsift p ⟨hp,hp4,hpn⟩ hpN hpr

theorem goldbach_full_sifted_count (H : PrimitiveTwoSquaresCriterion)
    {N n : ℕ} (hn : 2≤n) (hsize : n≤N^2) :
    (goldbachSiftedValues n ((N:ℝ)^2)).card≤
      (goldbachGoodRepresentations n).card+(n-1).primeFactors.card := by
  rw [goldbachSiftedValues_card]
  exact (card_le_card (goldbach_full_sifted_inclusion H hn hsize)).trans
    ((card_union_le _ _).trans (Nat.add_le_add_left (goldbachDivisorExceptions_card n) _))

/-- The complete finite-to-asymptotic implication of the first Section9 lemma. -/
theorem goldbach_from_full_sifted (H : PrimitiveTwoSquaresCriterion) {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ N n : ℕ,1≤N → 2≤n → n≤N^2 →
      ((goldbachSiftedValues n ((N:ℝ)^2)).card:ℝ)-K*(N:ℝ)^ε≤
        ((goldbachGoodRepresentations n).card:ℝ) := by
  obtain ⟨K,hK,herr⟩ := goldbach_prime_divisor_power_error hε
  refine ⟨K,hK,?_⟩
  intro N n hN hn hsize
  have hf := goldbach_full_sifted_count H hn hsize
  have hf' : ((goldbachSiftedValues n ((N:ℝ)^2)).card:ℝ)≤
      ((goldbachGoodRepresentations n).card:ℝ)+((n-1).primeFactors.card:ℝ) := by exact_mod_cast hf
  have he := herr N n hN hn (by omega : n-1≤N^2)
  linarith

end PrimeSquares
