import PrimeSquares.PrimeFactorPower
import PrimeSquares.LocalArithmetic

set_option autoImplicit false
open Finset
namespace PrimeSquares

/-- The primitive sum of two squares used by the manuscript. -/
def PrimitiveTwoSquares (m : ℕ) : Prop :=
  ∃ x y : ℕ,m=x^2+y^2 ∧ x.Coprime y

def GoldbachRepresentation (n r : ℕ) : Prop :=
  r.Prime ∧ ∃ q : ℕ,q.Prime ∧ r+q^2=n

noncomputable def goldbachRepresentations (n : ℕ) : Finset ℕ := by
  classical
  exact (range (n+1)).filter (GoldbachRepresentation n)

noncomputable def goldbachGoodRepresentations (n : ℕ) : Finset ℕ := by
  classical
  exact (goldbachRepresentations n).filter (fun r => PrimitiveTwoSquares (r-1))

noncomputable def goldbachAdmissibleRepresentations (n : ℕ) : Finset ℕ := by
  classical
  exact (goldbachRepresentations n).filter (fun r => r%24=11)

def GoldbachSievePrime (n p : ℕ) : Prop :=
  p.Prime ∧ p%4=3 ∧ ¬p∣n-1

noncomputable def goldbachSifted (n : ℕ) (z : ℝ) : Finset ℕ := by
  classical
  exact (goldbachAdmissibleRepresentations n).filter
    (fun r => ∀ p : ℕ,GoldbachSievePrime n p → (p:ℝ)<z → ¬p∣r-1)

/-- An explicit finite exceptional envelope, indexed by prime divisors of n-1. -/
noncomputable def goldbachDivisorExceptions (n : ℕ) : Finset ℕ :=
  (n-1).primeFactors.image (fun q => n-q^2)

theorem mem_goldbachRepresentations {n r : ℕ} :
    r∈goldbachRepresentations n ↔ GoldbachRepresentation n r := by
  classical
  simp only [goldbachRepresentations,mem_filter,mem_range]
  constructor
  · exact And.right
  · intro h
    obtain ⟨hp,q,hq,he⟩ := h
    exact ⟨by omega,hp,q,hq,he⟩

theorem goldbach_representation_unique_prime {n r q : ℕ} (he : r+q^2=n) : r=n-q^2 := by omega

theorem goldbach_shared_prime_eq {n r q p : ℕ} (hr : 1≤r) (hq : q.Prime)
    (hp : p.Prime) (he : r+q^2=n) (hdr : p∣r-1) (hdn : p∣n-1) : p=q := by
  have hd : p∣q^2 := by
    have hh : p∣(r-1)+q^2 := by rwa [show (r-1)+q^2=n-1 by omega]
    exact (Nat.dvd_add_iff_right hdr).mpr hh
  exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hd)

theorem goldbach_shared_divisor_exception {n r q p : ℕ} (hn : 2≤n) (hr : 1≤r)
    (hq : q.Prime) (hp : p.Prime) (he : r+q^2=n) (hdr : p∣r-1) (hdn : p∣n-1) :
    r∈goldbachDivisorExceptions n := by
  have hpq := goldbach_shared_prime_eq hr hq hp he hdr hdn
  apply mem_image.mpr
  refine ⟨q,Nat.mem_primeFactors.mpr ⟨hq,?_,by omega⟩,?_⟩
  · simpa only [hpq] using hdn
  · exact (goldbach_representation_unique_prime he).symm

theorem goldbachDivisorExceptions_card (n : ℕ) :
    (goldbachDivisorExceptions n).card≤(n-1).primeFactors.card := card_image_le

theorem goldbach_factor_coprime_of_not_exception {n r q ℓ : ℕ} (hn : 2≤n)
    (hr : 1≤r) (hq : q.Prime) (he : r+q^2=n) (hℓ : ℓ∣r-1)
    (hne : r∉goldbachDivisorExceptions n) : ℓ.Coprime (n-1) := by
  apply Nat.coprime_of_dvd
  intro p hp hpl hpn
  exact hne (goldbach_shared_divisor_exception hn hr hq hp he (hpl.trans hℓ) hpn)

theorem goldbachSifted_antitone {n : ℕ} {z w : ℝ} (hzw : z≤w) :
    goldbachSifted n w⊆goldbachSifted n z := by
  classical
  intro r hr
  obtain ⟨hr,hs⟩ := mem_filter.mp hr
  exact mem_filter.mpr ⟨hr,fun p hp hpz => hs p hp (hpz.trans_le hzw)⟩

theorem goldbach_prime_divisor_power_error {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ N n : ℕ,1≤N → 2≤n → n-1≤N^2 →
      ((n-1).primeFactors.card:ℝ)≤K*(N:ℝ)^ε := by
  obtain ⟨K,hK,h⟩ := primeFactor_pow_le_rpow 2 (by norm_num) (ε/2) (by positivity)
  refine ⟨K,hK,?_⟩
  intro N n hN hn hsize
  have hm : 0<n-1 := by omega
  have hNR : (0:ℝ)≤N := Nat.cast_nonneg N
  have hbase : (((n-1).primeFactors.card:ℕ):ℝ)≤(2:ℝ)^(n-1).primeFactors.card := by
    exact_mod_cast (show (n-1).primeFactors.card<2^(n-1).primeFactors.card from Nat.lt_two_pow_self).le
  calc
    _≤(2:ℝ)^(n-1).primeFactors.card := hbase
    _≤K*((n-1:ℕ):ℝ)^(ε/2) := h (n-1) hm
    _≤K*((N:ℝ)^2)^(ε/2) := by
      apply mul_le_mul_of_nonneg_left ?_ hK.le
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hsize) (by positivity)
    _=K*(N:ℝ)^ε := by
      congr 1
      rw [←Real.rpow_natCast,←Real.rpow_mul hNR]
      congr 1
      ring

theorem goldbachDivisorExceptions_power_error {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ N n : ℕ,1≤N → 2≤n → n-1≤N^2 →
      ((goldbachDivisorExceptions n).card:ℝ)≤K*(N:ℝ)^ε := by
  obtain ⟨K,hK,h⟩ := goldbach_prime_divisor_power_error hε
  exact ⟨K,hK,fun N n hN hn hsize =>
    (show ((goldbachDivisorExceptions n).card:ℝ)≤((n-1).primeFactors.card:ℝ) by
      exact_mod_cast goldbachDivisorExceptions_card n).trans (h N n hN hn hsize)⟩

theorem goldbach_square_prime_large {n r q : ℕ} (hn : 12<n) (hres : n%24=12)
    (hr : r.Prime) (hq : q.Prime) (he : r+q^2=n) : 3<q := by
  by_contra hh
  have hq2 := hq.two_le
  have hc : q=2 ∨ q=3 := by omega
  rcases hc with hqeq|hqeq
  · have he' : r+4=n := by simpa only [hqeq,show (2:ℕ)^2=4 by norm_num] using he
    have hd : 2∣r := Nat.dvd_of_mod_eq_zero (by omega)
    rcases (Nat.dvd_prime hr).mp hd with hh|hh <;> omega
  · have he' : r+9=n := by simpa only [hqeq,show (3:ℕ)^2=9 by norm_num] using he
    have hd : 3∣r := Nat.dvd_of_mod_eq_zero (by omega)
    rcases (Nat.dvd_prime hr).mp hd with hh|hh <;> omega

theorem goldbach_representation_admissible {n r : ℕ} (hn : 12<n) (hres : n%24=12)
    (h : GoldbachRepresentation n r) : r%24=11 := by
  obtain ⟨hr,q,hq,he⟩ := h
  have hh := prime_square_mod24 q hq (goldbach_square_prime_large hn hres hr hq he)
  omega

end PrimeSquares
