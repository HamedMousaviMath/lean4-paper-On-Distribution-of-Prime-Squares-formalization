import PrimeSquares.GoldbachFactorParity

set_option autoImplicit false
namespace PrimeSquares

theorem primeFactorsList_odd_mod_four {m : ℕ} (hm : m%4=1)
    {p : ℕ} (hp : p∈m.primeFactorsList) : p%4=1 ∨ p%4=3 := by
  have hpp := Nat.prime_of_mem_primeFactorsList hp
  have hd := Nat.dvd_of_mem_primeFactorsList hp
  have hp2 : p≠2 := by
    intro he
    rw [he] at hd
    have hh := Nat.mod_eq_zero_of_dvd hd
    omega
  have ho := hpp.mod_two_eq_one_iff_ne_two.mpr hp2
  omega

/-- The exact multiplicity-sensitive factorization used by the truncated sieve. -/
theorem primitive_obstruction_two_large_primes {m : ℕ} (hm : m%4=1)
    {z : ℝ} (hz : 1≤z) (hsize : (m:ℝ)<z^4)
    (hlarge : ∀ p : ℕ,p.Prime → p%4=3 → p∣m → z≤(p:ℝ))
    (hbad : ∃ p : ℕ,p.Prime ∧ p%4=3 ∧ p∣m) :
    ∃ u p₁ p₂ : ℕ,0<u ∧ m=u*p₁*p₂ ∧ p₂≤p₁ ∧
      p₁.Prime ∧ p₁%4=3 ∧ z≤(p₁:ℝ) ∧
      p₂.Prime ∧ p₂%4=3 ∧ z≤(p₂:ℝ) ∧
      ∀ p : ℕ,p.Prime → p∣u → p%4=1 := by
  let L := m.primeFactorsList
  have hm0 : 0<m := by omega
  have hprod : L.prod=m := Nat.prod_primeFactorsList hm0.ne'
  have hL : ∀ p∈L,p%4=1 ∨ p%4=3 := fun _ hp => primeFactorsList_odd_mod_four hm hp
  have hbne : badModFourFactors L≠[] := by
    obtain ⟨p,hp,hp4,hpd⟩ := hbad
    have hmem : p∈badModFourFactors L := mem_badModFourFactors.mpr
      ⟨(Nat.mem_primeFactorsList hm0.ne').mpr ⟨hp,hpd⟩,hp4⟩
    intro he
    simp only [he,List.not_mem_nil] at hmem
  have hlargelist : ∀ p∈badModFourFactors L,z≤(p:ℝ) := by
    intro p hp
    obtain ⟨hpL,hp4⟩ := mem_badModFourFactors.mp hp
    exact hlarge p (Nat.prime_of_mem_primeFactorsList hpL) hp4 (Nat.dvd_of_mem_primeFactorsList hpL)
  obtain ⟨a,b,hab⟩ := exactly_two_badModFourFactors L hL (by omega) (by omega) hz hlargelist
    (by simpa only [hprod] using hsize) hbne
  let u := (goodModFourFactors L).prod
  have ha : a∈badModFourFactors L := by rw [hab]; simp
  have hb : b∈badModFourFactors L := by rw [hab]; simp
  have haL := (mem_badModFourFactors.mp ha).1
  have hbL := (mem_badModFourFactors.mp hb).1
  have ha4 := (mem_badModFourFactors.mp ha).2
  have hb4 := (mem_badModFourFactors.mp hb).2
  have hap := Nat.prime_of_mem_primeFactorsList haL
  have hbp := Nat.prime_of_mem_primeFactorsList hbL
  have haz := hlargelist a ha
  have hbz := hlargelist b hb
  have he : m=u*a*b := by
    have hh := modFourFactors_product L
    rw [hprod,hab] at hh
    simp only [List.prod_cons,List.prod_nil,mul_one] at hh
    dsimp [u]
    nlinarith only [hh]
  have hu : 0<u := by
    by_contra hh
    have hu0 : u=0 := by omega
    simp only [hu0,zero_mul] at he
    omega
  have hugood : ∀ p : ℕ,p.Prime → p∣u → p%4=1 := by
    intro p hp hpd
    have hprime : ∀ t∈goodModFourFactors L,Prime t := by
      intro t ht
      exact (Nat.prime_of_mem_primeFactorsList (mem_goodModFourFactors.mp ht).1).prime
    have hmem : p∈goodModFourFactors L := mem_list_primes_of_dvd_prod hp.prime hprime hpd
    obtain ⟨hpL,hp4⟩ := mem_goodModFourFactors.mp hmem
    exact (hL p hpL).resolve_right hp4
  by_cases hba : b≤a
  · exact ⟨u,a,b,hu,he,hba,hap,ha4,haz,hbp,hb4,hbz,hugood⟩
  · exact ⟨u,b,a,hu,by nlinarith only [he],by omega,hbp,hb4,hbz,hap,ha4,haz,hugood⟩

end PrimeSquares
