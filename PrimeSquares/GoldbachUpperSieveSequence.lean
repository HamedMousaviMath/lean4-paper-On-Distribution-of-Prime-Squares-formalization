import PrimeSquares.GoldbachLowerSieveSequence

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachUpperDivisibilitySequence (n N ℓ d : ℕ) : Finset ℕ := by
  classical
  exact (goldbachUpperM n N ℓ).filter (fun r=>d∣r)

theorem goldbach_upper_sieve_residue_iff {v d a t : ℕ} (hv : v.Coprime 6)
    (hdℓ : d.Coprime (12*(2*v)))
    (ha12 : Nat.ModEq 12 (v*a) 5) (had : Nat.ModEq d ((2*v)*a+1) 0) :
    t%(12*d)=a%(12*d) ↔Nat.ModEq 12 (v*t) 5 ∧ d∣(2*v)*t+1 := by
  have hv12 : v.Coprime 12 := by
    rw [show (12:ℕ)=2*6 by decide]
    exact (Nat.Coprime.of_dvd_right (by decide : 2∣6) hv).mul_right hv
  have hd12 : d.Coprime 12 := Nat.Coprime.of_dvd_right (dvd_mul_right 12 (2*v)) hdℓ
  have hℓd : (2*v).Coprime d := (Nat.Coprime.of_dvd_right (dvd_mul_left (2*v) 12) hdℓ).symm
  constructor
  · intro h
    have hh : Nat.ModEq (12*d) t a := h
    have h12 := ((hh.of_dvd (dvd_mul_right 12 d)).mul_left v).trans ha12
    have hd := (((hh.of_dvd (dvd_mul_left d 12)).mul_left (2*v)).add_right 1).trans had
    exact ⟨h12,Nat.modEq_zero_iff_dvd.mp hd⟩
  · rintro ⟨h12,hd⟩
    have h12' : Nat.ModEq 12 t a := Nat.ModEq.cancel_left_of_coprime hv12.symm.gcd_eq_one (h12.trans ha12.symm)
    have hd' : Nat.ModEq d t a := by
      have hh : Nat.ModEq d ((2*v)*t+1) ((2*v)*a+1) := (Nat.modEq_zero_iff_dvd.mpr hd).trans had.symm
      exact Nat.ModEq.cancel_left_of_coprime hℓd.symm.gcd_eq_one (hh.add_right_cancel' 1)
    change Nat.ModEq (12*d) t a
    simpa only [hd12.symm.lcm_eq_mul] using Nat.mod_lcm h12' hd'

theorem goldbach_upper_prime_conditions {n v m t : ℕ} (hn : 0<n) (hn24 : n%24=12)
    (hv4 : v%4=3) (hm : m.Prime) (hvt : Nat.ModEq 12 (v*t) 5)
    (he : m^2+(2*v)*t=n-1) : 3<m ∧ t%4=3 := by
  have hvt12 : (v*t)%12=5 := hvt
  have he' : m^2+2*(v*t)+1=n := by
    calc
      _=(m^2+(2*v)*t)+1 := by ring
      _=n := by omega
  have hm3 : 3<m := by
    by_contra hh
    have := hm.two_le
    have hm23 : m=2 ∨ m=3 := by omega
    rcases hm23 with heq|heq <;> subst m <;> norm_num at he' <;> omega
  have hvt4 : (v*t)%4=1 := by omega
  rw [Nat.mul_mod,hv4] at hvt4
  exact ⟨hm3,by omega⟩

theorem goldbach_upper_sieve_sequence_count (n N v d a : ℕ)
    (hn : 0<n) (hnN : n<N^2) (hn24 : n%24=12) (hv : v.Coprime 6) (hv4 : v%4=3)
    (hdℓ : d.Coprime (12*(2*v)))
    (ha12 : Nat.ModEq 12 (v*a) 5) (had : Nat.ModEq d ((2*v)*a+1) 0) :
    (goldbachUpperDivisibilitySequence n N (2*v) d).card=
      (goldbachProgressionPairs (2*v) (12*d) a (n-1)).card := by
  classical
  have hvpos : 0<v := by omega
  have hℓpos : 0<2*v := by omega
  symm
  apply card_bij (fun x _=>(2*v)*x.2+1)
  · rintro ⟨m,t⟩ hx
    change (2*v)*t+1∈goldbachUpperDivisibilitySequence n N (2*v) d
    obtain ⟨_,_,hm,ht,hres,he⟩ := (mem_goldbach_progression_pairs (2*v) (12*d) a (n-1) m t).mp hx
    obtain ⟨hvt,hdiv⟩ := (goldbach_upper_sieve_residue_iff hv hdℓ ha12 had).mp hres
    obtain ⟨hm3,ht4⟩ := goldbach_upper_prime_conditions hn hn24 hv4 hm hvt he
    have hrN : (2*v)*t+1<N^2 := by omega
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_range.mpr hrN,t,m,ht,ht4,hm,hm3,rfl,by omega⟩,hdiv⟩
  · rintro ⟨m,t⟩ hx ⟨q,r⟩ hy he
    change (2*v)*t+1=(2*v)*r+1 at he
    have ht : t=r := by nlinarith
    obtain ⟨_,_,_,_,_,hmEq⟩ := (mem_goldbach_progression_pairs (2*v) (12*d) a (n-1) m t).mp hx
    obtain ⟨_,_,_,_,_,hqEq⟩ := (mem_goldbach_progression_pairs (2*v) (12*d) a (n-1) q r).mp hy
    have hsq : m^2=q^2 := by omega
    exact Prod.ext ((Nat.pow_left_inj (by decide : 2≠0)).mp hsq) ht
  · intro r hr
    obtain ⟨hrM,hdiv⟩ := mem_filter.mp hr
    obtain ⟨_,t,m,ht,_,hm,hm3,hrEq,hnEq⟩ := mem_filter.mp hrM
    have he : m^2+(2*v)*t=n-1 := by omega
    have hmN : m≤n-1 := by have := hm.two_le;nlinarith
    have htN : t≤n-1 := by nlinarith
    have hm24 := prime_square_mod24 m hm hm3
    have hvt : Nat.ModEq 12 (v*t) 5 := by
      change (v*t)%12=5
      have he' : m^2+2*(v*t)+1=n := by nlinarith
      omega
    have hres := (goldbach_upper_sieve_residue_iff hv hdℓ ha12 had).mpr ⟨hvt,by simpa only [hrEq] using hdiv⟩
    refine ⟨(m,t),(mem_goldbach_progression_pairs (2*v) (12*d) a (n-1) m t).mpr ⟨hmN,htN,hm,ht,hres,he⟩,hrEq.symm⟩

theorem goldbach_prime_support_one_mod_four {u : ℕ} (hu : 0<u)
    (hU : ∀ p : ℕ,p.Prime →p∣u →p%4=1) : u%4=1 := by
  have hprod (L : List ℕ) (hL : ∀ p∈L,p%4=1) : L.prod%4=1 := by
    induction L with
    | nil => norm_num
    | cons a L ih =>
      rw [List.prod_cons,Nat.mul_mod,hL a (by simp),ih (fun p hp=>hL p (by simp [hp]))]
  rw [←Nat.prod_primeFactorsList hu.ne']
  exact hprod _ (fun p hp=>hU p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp))

theorem goldbach_closed_multiplier_residue_data {N ℓ : ℕ} {z : ℝ} (hz : 3<z)
    (hℓ : ℓ∈goldbachClosedLSet N z) :
    ∃ v : ℕ,ℓ=2*v ∧ v%4=3 ∧ v.Coprime 6 := by
  obtain ⟨u,p,hu,he,_,hp,hp4,hpz,_,hU⟩ := mem_goldbachClosedLSet.mp hℓ
  have hp3 : 3<p := by exact_mod_cast hz.trans_le hpz
  have hu4 := goldbach_prime_support_one_mod_four hu hU
  have huc : u.Coprime 6 := goldbach_sieve_support_coprime_six u (fun q hq hqu=>by
    have hq4 := hU q hq hqu
    have hq2 := hq.two_le
    omega)
  have hpc : p.Coprime 6 := hp.coprime_iff_not_dvd.mpr (fun h=>by
    rcases hp.dvd_mul.mp (show p∣2*3 from h) with h2|h3
    · have hh := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp h2;omega
    · have hh := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp h3;omega)
  refine ⟨u*p,by rw [he];ring,?_,huc.mul_left hpc⟩
  simp only [Nat.mul_mod,hu4,hp4,one_mul]

theorem goldbach_upper_sequence_fixed_residue {N ℓ : ℕ} {z : ℝ} (hz : 3<z)
    (hℓ : ℓ∈goldbachClosedLSet N z) (d : ℕ) (hd : 0<d) (hdℓ : d.Coprime (12*ℓ)) :
    ∃ a : ℕ,a<12*d ∧ a.Coprime (12*d) ∧ ∀ n : ℕ,0<n →n<N^2 →n%24=12 →
      (goldbachUpperDivisibilitySequence n N ℓ d).card=(goldbachProgressionPairs ℓ (12*d) a (n-1)).card := by
  obtain ⟨v,he,hv4,hv⟩ := goldbach_closed_multiplier_residue_data hz hℓ
  rw [he] at hdℓ ⊢
  obtain ⟨a,haBound,ha12,had,hac⟩ := goldbach_upper_sieve_residue v d hv hd hdℓ
  exact ⟨a,haBound,hac,fun n hn hnN hn24=>goldbach_upper_sieve_sequence_count n N v d a hn hnN hn24 hv hv4 hdℓ ha12 had⟩

theorem goldbach_upper_sequence_circle_identity (ψ : SchwartzMap ℝ ℝ) (N n v d a : ℕ)
    (hn : 0<n) (hnN : n<N^2) (hn24 : n%24=12) (hv : v.Coprime 6) (hv4 : v%4=3)
    (hdℓ : d.Coprime (12*(2*v))) (ha12 : Nat.ModEq 12 (v*a) 5)
    (had : Nat.ModEq d ((2*v)*a+1) 0) (R : ℝ) :
    ((goldbachUpperDivisibilitySequence n N (2*v) d).card:ℂ)=
      goldbachArithmeticFactor R (12*d) ((2*v:ℕ):ℤ) (a:ℤ) ((n-1:ℕ):ℤ)/
        (((2*v:ℕ):ℂ)*((12*d).totient:ℂ))*goldbachSingularIntegral ψ N (2*v) R (n-1:ℕ) (N:ℝ) ((N:ℝ)^2)+
      goldbachFullRemainder ψ N (2*v) (12*d) a R (n-1) := by
  rw [goldbach_upper_sieve_sequence_count n N v d a hn hnN hn24 hv hv4 hdℓ ha12 had]
  unfold goldbachFullRemainder
  ring

end PrimeSquares
