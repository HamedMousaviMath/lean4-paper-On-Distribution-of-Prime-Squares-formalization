import PrimeSquares.GoldbachFixedSieveSets
import PrimeSquares.GoldbachSieveResidues

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachLowerDivisibilitySequence (n d : ℕ) : Finset ℕ := by
  classical
  exact (goldbachAdmissibleRepresentations n).filter (fun r=>d∣r-1)

noncomputable def goldbachLowerDivisibilityValues (n d : ℕ) : Finset ℕ :=
  (goldbachLowerDivisibilitySequence n d).image (fun r=>r-1)

theorem goldbach_lower_divisibility_values_card (n d : ℕ) :
    (goldbachLowerDivisibilityValues n d).card=(goldbachLowerDivisibilitySequence n d).card := by
  classical
  apply card_image_iff.mpr
  intro r hr t ht he
  have hrp := (mem_goldbachRepresentations.mp (mem_filter.mp (mem_filter.mp hr).1).1).1.two_le
  have htp := (mem_goldbachRepresentations.mp (mem_filter.mp (mem_filter.mp ht).1).1).1.two_le
  change r-1=t-1 at he
  omega

theorem goldbach_sieve_coprime_twentyfour {d : ℕ} (h : d.Coprime 6) : (24:ℕ).Coprime d := by
  have h2 : (2:ℕ).Coprime d := Nat.Coprime.of_dvd_left (by decide : 2∣6) h.symm
  rw [show (24:ℕ)=2^2*6 by decide]
  exact (h2.pow_left 2).mul_left h.symm

theorem goldbach_lower_sieve_residue_iff {d a r : ℕ} (hd6 : d.Coprime 6)
    (ha24 : Nat.ModEq 24 a 11) (had : Nat.ModEq d a 1) (hr : 1≤r) :
    r%(24*d)=a%(24*d) ↔r%24=11 ∧ d∣r-1 := by
  have hcop := goldbach_sieve_coprime_twentyfour hd6
  constructor
  · intro h
    have hmod : Nat.ModEq (24*d) r a := h
    have h24 := (hmod.of_dvd (dvd_mul_right 24 d)).trans ha24
    have hd := (hmod.of_dvd (dvd_mul_left d 24)).trans had
    refine ⟨by simpa only [Nat.ModEq,show 11%24=11 by decide] using h24,?_⟩
    exact (Nat.modEq_iff_dvd' hr).mp hd.symm
  · rintro ⟨h24,hd⟩
    have h24' : Nat.ModEq 24 r a := (show Nat.ModEq 24 r 11 from h24).trans ha24.symm
    have hd' : Nat.ModEq d r a := ((Nat.modEq_iff_dvd' hr).mpr hd).symm.trans had.symm
    have hh := Nat.mod_lcm h24' hd'
    change Nat.ModEq (24*d) r a
    simpa only [hcop.lcm_eq_mul] using hh

theorem mem_goldbach_progression_pairs (ℓ k a n m t : ℕ) :
    (m,t)∈goldbachProgressionPairs ℓ k a n ↔
      m≤n ∧ t≤n ∧ m.Prime ∧ t.Prime ∧ t%k=a%k ∧ m^2+ℓ*t=n := by
  classical
  simp only [goldbachProgressionPairs,mem_filter,mem_product,mem_range,Nat.lt_succ_iff]
  tauto

theorem goldbach_lower_sieve_sequence_count (n d a : ℕ) (hd6 : d.Coprime 6)
    (ha24 : Nat.ModEq 24 a 11) (had : Nat.ModEq d a 1) :
    (goldbachLowerDivisibilityValues n d).card=(goldbachProgressionPairs 1 (24*d) a n).card := by
  classical
  rw [goldbach_lower_divisibility_values_card]
  symm
  apply card_bij (fun x _=>x.2)
  · rintro ⟨m,t⟩ hx
    obtain ⟨_,_,hm,ht,hres,he⟩ := (mem_goldbach_progression_pairs 1 (24*d) a n m t).mp hx
    obtain ⟨h24,hd⟩ := (goldbach_lower_sieve_residue_iff hd6 ha24 had ht.one_le).mp hres
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_goldbachRepresentations.mpr ⟨ht,m,hm,by nlinarith⟩,h24⟩,hd⟩
  · rintro ⟨m,t⟩ hx ⟨q,r⟩ hy he
    change t=r at he
    obtain ⟨_,_,_,_,_,hxEq⟩ := (mem_goldbach_progression_pairs 1 (24*d) a n m t).mp hx
    obtain ⟨_,_,_,_,_,hyEq⟩ := (mem_goldbach_progression_pairs 1 (24*d) a n q r).mp hy
    have hsq : m^2=q^2 := by omega
    exact Prod.ext ((Nat.pow_left_inj (by decide : 2≠0)).mp hsq) he
  · intro r hr
    obtain ⟨hra,hd⟩ := mem_filter.mp hr
    obtain ⟨hrep,h24⟩ := mem_filter.mp hra
    obtain ⟨hrp,m,hm,he⟩ := mem_goldbachRepresentations.mp hrep
    have hmN : m≤n := by have := hm.two_le;nlinarith
    have hrN : r≤n := by omega
    have hres := (goldbach_lower_sieve_residue_iff hd6 ha24 had hrp.one_le).mpr ⟨h24,hd⟩
    refine ⟨(m,r),(mem_goldbach_progression_pairs 1 (24*d) a n m r).mpr ⟨hmN,hrN,hm,hrp,hres,by nlinarith⟩,rfl⟩

theorem goldbach_sieve_support_coprime_six (d : ℕ)
    (hS : ∀ p : ℕ,p.Prime →p∣d →3<p) : d.Coprime 6 := by
  apply Nat.coprime_of_dvd
  intro p hp hpd hp6
  have hlarge := hS p hp hpd
  rcases hp.dvd_mul.mp (show p∣2*3 from hp6) with hp2|hp3
  · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hp2
    omega
  · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp hp3
    omega

theorem goldbach_lower_sequence_fixed_residue (d : ℕ)
    (hS : ∀ p : ℕ,p.Prime →p∣d →3<p) :
    ∃ a : ℕ,a<24*d ∧ a.Coprime (24*d) ∧ ∀ n : ℕ,
      (goldbachLowerDivisibilityValues n d).card=(goldbachProgressionPairs 1 (24*d) a n).card := by
  obtain ⟨a,haBound,ha24,had,hac⟩ := goldbach_lower_sieve_residue_from_support d hS
  exact ⟨a,haBound,hac,fun n=>goldbach_lower_sieve_sequence_count n d a (goldbach_sieve_support_coprime_six d hS) ha24 had⟩

theorem goldbach_lower_sequence_circle_identity (ψ : SchwartzMap ℝ ℝ) (N n d a : ℕ)
    (hd6 : d.Coprime 6) (ha24 : Nat.ModEq 24 a 11) (had : Nat.ModEq d a 1) (R : ℝ) :
    ((goldbachLowerDivisibilityValues n d).card:ℂ)=
      goldbachArithmeticFactor R (24*d) (1:ℤ) (a:ℤ) n/((24*d).totient:ℂ)*
        goldbachSingularIntegral ψ N 1 R (n:ℝ) (N:ℝ) ((N:ℝ)^2)+
      goldbachFullRemainder ψ N 1 (24*d) a R n := by
  rw [goldbach_lower_sieve_sequence_count n d a hd6 ha24 had]
  unfold goldbachFullRemainder
  simp only [Nat.cast_one,one_mul]
  ring

end PrimeSquares
