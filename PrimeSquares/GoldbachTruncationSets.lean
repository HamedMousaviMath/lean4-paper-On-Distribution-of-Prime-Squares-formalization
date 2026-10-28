import PrimeSquares.GoldbachFullSiftedReduction
import PrimeSquares.GoldbachTwoLargePrimeFactors

set_option autoImplicit false
open Finset
namespace PrimeSquares

def GoldbachTwoLargeFactorization (n : ℕ) (z : ℝ) (r : ℕ) : Prop :=
  ∃ u p₁ p₂ : ℕ,0<u ∧ r-1=2*u*p₁*p₂ ∧
    z≤(p₂:ℝ) ∧ p₂≤p₁ ∧ GoldbachSievePrime n p₁ ∧ GoldbachSievePrime n p₂ ∧
    ∀ p : ℕ,p.Prime → p∣u → p%4=1

noncomputable def goldbachTruncatedBad (n : ℕ) (z : ℝ) : Finset ℕ := by
  classical
  exact (goldbachAdmissibleRepresentations n).filter (GoldbachTwoLargeFactorization n z)

theorem prime_three_mod_four_dvd_half {p m r : ℕ} (hp : p.Prime) (hp4 : p%4=3)
    (he : r-1=2*m) (hd : p∣r-1) : p∣m := by
  rw [he] at hd
  rcases hp.dvd_mul.mp hd with hd|hd
  · have hh := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hd
    norm_num [hh] at hp4
  · exact hd

theorem goldbach_sifted_bad_factorization (H : PrimitiveTwoSquaresCriterion)
    {N n : ℕ} (hn : 2≤n) (hsize : n≤N^2) {z : ℝ} (hz : 1≤z)
    (hlarge : (N:ℝ)^2<z^4) {r : ℕ} (hr : r∈goldbachSifted n z)
    (hgood : r∉goldbachGoodRepresentations n) (hexc : r∉goldbachDivisorExceptions n) :
    r∈goldbachTruncatedBad n z := by
  classical
  obtain ⟨hra,hsift⟩ := mem_filter.mp hr
  obtain ⟨hrr,hres⟩ := mem_filter.mp hra
  obtain ⟨hrp,q,hq,heq⟩ := mem_goldbachRepresentations.mp hrr
  let m := (r-1)/2
  have hm : m%4=1 := by dsimp [m]; omega
  have hrm : r-1=2*m := by dsimp [m]; omega
  have hbad : ∃ p : ℕ,p.Prime ∧ p%4=3 ∧ p∣r-1 := by
    by_contra hh
    push Not at hh
    exact hgood (mem_filter.mpr ⟨hrr,(H (r-1) (by omega)).mpr hh⟩)
  have hmp : ∀ p : ℕ,p.Prime → p%4=3 → p∣m → z≤(p:ℝ) := by
    intro p hp hp4 hpm
    have hpr : p∣r-1 := by rw [hrm]; exact dvd_mul_of_dvd_right hpm 2
    have hpn : ¬p∣n-1 := fun h => hexc (goldbach_shared_divisor_exception hn hrp.one_le hq hp heq hpr h)
    exact le_of_not_gt (fun h => hsift p ⟨hp,hp4,hpn⟩ h hpr)
  have hmN : m≤N^2 := by dsimp [m]; omega
  obtain ⟨u,p₁,p₂,hu,hmfac,horder,hp₁,hp₁4,hp₁z,hp₂,hp₂4,hp₂z,hugood⟩ :=
    primitive_obstruction_two_large_primes hm hz
      ((show (m:ℝ)≤(N:ℝ)^2 by exact_mod_cast hmN).trans_lt hlarge) hmp
      (by obtain ⟨p,hp,hp4,hpd⟩ := hbad
          exact ⟨p,hp,hp4,prime_three_mod_four_dvd_half hp hp4 hrm hpd⟩)
  have hfac : r-1=2*u*p₁*p₂ := by rw [hrm,hmfac]; ring
  have hp₁r : p₁∣r-1 := ⟨2*u*p₂,by rw [hfac]; ring⟩
  have hp₂r : p₂∣r-1 := ⟨2*u*p₁,by rw [hfac]; ring⟩
  have hp₁n : ¬p₁∣n-1 := fun h => hexc (goldbach_shared_divisor_exception hn hrp.one_le hq hp₁ heq hp₁r h)
  have hp₂n : ¬p₂∣n-1 := fun h => hexc (goldbach_shared_divisor_exception hn hrp.one_le hq hp₂ heq hp₂r h)
  exact mem_filter.mpr ⟨hra,u,p₁,p₂,hu,hfac,hp₂z,horder,⟨hp₁,hp₁4,hp₁n⟩,⟨hp₂,hp₂4,hp₂n⟩,hugood⟩

theorem goldbachTruncatedBad_subset_sifted {n : ℕ} {z : ℝ} :
    goldbachTruncatedBad n z⊆goldbachSifted n z := by
  classical
  intro r hr
  obtain ⟨hra,u,p₁,p₂,_,hfac,hp₂z,horder,hp₁,hp₂,hugood⟩ := mem_filter.mp hr
  apply mem_filter.mpr
  refine ⟨hra,?_⟩
  intro p hp hpz hpd
  rw [hfac] at hpd
  simp only [hp.1.dvd_mul] at hpd
  rcases hpd with ((h2|hu)|h1)|h2p
  · have he := (Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 2)).mp h2
    norm_num [GoldbachSievePrime,he] at hp
  · have hh := hugood p hp.1 hu
    have hh4 := hp.2.1
    omega
  · have he := (Nat.prime_dvd_prime_iff_eq hp.1 hp₁.1).mp h1
    have ho : (p₂:ℝ)≤p₁ := by exact_mod_cast horder
    rw [he] at hpz
    linarith
  · have he := (Nat.prime_dvd_prime_iff_eq hp.1 hp₂.1).mp h2p
    rw [he] at hpz
    linarith

theorem goldbachTruncatedBad_not_good (H : PrimitiveTwoSquaresCriterion)
    {n : ℕ} {z : ℝ} {r : ℕ} (hr : r∈goldbachTruncatedBad n z) :
    r∉goldbachGoodRepresentations n := by
  classical
  obtain ⟨hra,u,p₁,p₂,_,hfac,_,_,hp₁,_,_⟩ := mem_filter.mp hr
  have hres := (mem_filter.mp hra).2
  intro hg
  have hprim := (mem_filter.mp hg).2
  have hnp := (H (r-1) (by omega)).mp hprim p₁ hp₁.1 hp₁.2.1
  exact hnp ⟨2*u*p₂,by rw [hfac]; ring⟩

theorem goldbach_good_subset_sifted (H : PrimitiveTwoSquaresCriterion)
    {n : ℕ} (hn : 12<n) (hres : n%24=12) (z : ℝ) :
    goldbachGoodRepresentations n⊆goldbachSifted n z := by
  classical
  intro r hr
  obtain ⟨hrr,hprim⟩ := mem_filter.mp hr
  have hrep := mem_goldbachRepresentations.mp hrr
  have hrres := goldbach_representation_admissible hn hres hrep
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨hrr,hrres⟩,?_⟩
  intro p hp _
  exact (H (r-1) (by omega)).mp hprim p hp.1 hp.2.1

end PrimeSquares
