import PrimeSquares.GoldbachWeightedEulerProducts
import PrimeSquares.GoldbachWeightedGeometry
import PrimeSquares.GoldbachWeightedMeanInputs

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachWeightedOuterPrimes (R z : ℝ) (a : ℕ) : Finset ℕ := by
  classical
  exact ((range (Nat.ceil z)).filter (fun p : ℕ=>p.Prime ∧ 3<p ∧ R<(p:ℝ))).filter
    (fun p : ℕ=>a=0 ∨ p%4=a)

noncomputable def goldbachWeightedOuterProduct (R z : ℝ) (a : ℕ) : ℝ :=
  ∏ p∈goldbachWeightedOuterPrimes R z a,(1-1/((p:ℝ)-1))

theorem mem_goldbach_weighted_outer_primes (R z : ℝ) (a p : ℕ) :
    p∈goldbachWeightedOuterPrimes R z a ↔
      p.Prime ∧ 3<p ∧ R<(p:ℝ) ∧ (p:ℝ)<z ∧ (a=0 ∨ p%4=a) := by
  classical
  simp only [goldbachWeightedOuterPrimes,mem_filter,mem_range,Nat.lt_ceil]
  tauto

theorem goldbach_weighted_outer_product_positive (R z : ℝ) (a : ℕ) :
    0<goldbachWeightedOuterProduct R z a := by
  classical
  apply prod_pos
  intro p hp
  have hs := (mem_goldbach_weighted_outer_primes R z a p).mp hp
  have hpR : (3:ℝ)<p := by exact_mod_cast hs.2.1
  apply sub_pos.mpr
  exact (div_lt_one (by linarith : 0<(p:ℝ)-1)).mpr (by linarith)

theorem goldbach_weighted_small_divisors {R : ℝ} (hR : 0≤R) {u p₂ : ℕ}
    (hp₂ : p₂.Prime) (hp₂R : R<(p₂:ℝ)) (p : ℕ) (hp : p∈goldbachLargeLocalPrimes R) :
    p∣2*u*p₂ ↔ p∣u := by
  have hs := (mem_goldbach_large_local_primes hR p).mp hp
  have hp2 : ¬p∣2 := by
    intro h
    have hh := (Nat.prime_dvd_prime_iff_eq hs.1 (by decide : Nat.Prime 2)).mp h
    omega
  have hpp : ¬p∣p₂ := by
    intro h
    have hh := (Nat.prime_dvd_prime_iff_eq hs.1 hp₂).mp h
    rw [hh] at hs
    linarith [hs.2.2]
  constructor
  · intro h
    rcases hs.1.dvd_mul.mp h with h|h
    · exact (hs.1.dvd_mul.mp h).resolve_left hp2
    · exact False.elim (hpp h)
  · intro h
    exact (h.mul_left 2).mul_right p₂

theorem goldbach_weighted_upper_small_product (R : ℝ) (hR : 3≤R) (u p₂ : ℕ)
    (hp₂ : p₂.Prime) (hp₂R : R<(p₂:ℝ))
    (hU : ∀ p : ℕ,p.Prime→p∣u→p%4=1) (n : ℤ) :
    (∏ p∈goldbachLargeLocalPrimes R,goldbachUpperArithmeticReal p (2*u*p₂) n)*
      (∏ p∈goldbachLargeLocalPrimes R,if p∣2*u*p₂ then 1 else 1-goldbachUpperDensity R n p)=
    goldbachWeightedB R n*
      ∏ p∈goldbachLargeLocalPrimes R,if p∣u then goldbachWeightedPrimeValue R n p else 1 := by
  classical
  unfold goldbachWeightedB
  rw [←prod_mul_distrib,←prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  obtain ⟨hprime,hlarge,hpR⟩ := (mem_goldbach_large_local_primes (by linarith) p).mp hp
  have hd := goldbach_weighted_small_divisors (u:=u) (by linarith : (0:ℝ)≤R) hp₂ hp₂R p hp
  by_cases hpu : p∣u
  · have hpℓ : p∣2*u*p₂ := hd.mpr hpu
    simp only [goldbachUpperArithmeticReal,ite_eq_left hpℓ,ite_eq_left hpu,mul_one]
    exact (goldbach_weighted_small_prime_cancel hprime hlarge R hpR n (hU p hprime hpu)).2.symm
  · have hpℓ : ¬p∣2*u*p₂ := fun h=>hpu (hd.mp h)
    simp only [goldbachUpperArithmeticReal,ite_eq_right hpℓ,ite_eq_right hpu,mul_one]
    exact goldbach_weighted_upper_local_cancel hprime hlarge R hpR n

theorem goldbach_weighted_lower_prime_partition (R z : ℝ) (hR : 3≤R) (hRz : R<z) :
    (goldbachLargeLocalPrimes R).filter (fun p : ℕ=>p%4=3)∪
      goldbachWeightedOuterPrimes R z 3=goldbachLowerSievePrimes z ∧
    Disjoint ((goldbachLargeLocalPrimes R).filter (fun p : ℕ=>p%4=3))
      (goldbachWeightedOuterPrimes R z 3) := by
  classical
  constructor
  · ext p
    simp only [mem_union,mem_filter,mem_goldbach_weighted_outer_primes,
      mem_goldbach_lower_sieve_primes,GoldbachFixedLowerSievePrime]
    rw [mem_goldbach_large_local_primes (by linarith : (0:ℝ)≤R)]
    constructor
    · rintro (⟨⟨hprime,hlarge,hpR⟩,h4⟩|⟨hprime,hlarge,_,hpz,h4⟩)
      · exact ⟨⟨hprime,hlarge,h4⟩,hpR.trans_lt hRz⟩
      · exact ⟨⟨hprime,hlarge,by simpa using h4⟩,hpz⟩
    · rintro ⟨⟨hprime,hlarge,h4⟩,hpz⟩
      by_cases hpR : (p:ℝ)≤R
      · exact Or.inl ⟨⟨hprime,hlarge,hpR⟩,h4⟩
      · exact Or.inr ⟨hprime,hlarge,lt_of_not_ge hpR,hpz,Or.inr h4⟩
  · apply disjoint_left.mpr
    intro p hp hq
    have hpR := ((mem_goldbach_large_local_primes (by linarith) p).mp (mem_filter.mp hp).1).2.2
    exact not_lt_of_ge hpR ((mem_goldbach_weighted_outer_primes R z 3 p).mp hq).2.2.1

theorem goldbach_weighted_lower_theta_partition (R z : ℝ) (hR : 3≤R) (hRz : R<z) (n : ℕ) :
    goldbachLowerTheta R z n=
      (∏ p∈goldbachLargeLocalPrimes R,if p%4=3 then 1-goldbachLowerDensity R n p else 1)*
        goldbachWeightedOuterProduct R z 3 := by
  classical
  obtain ⟨hunion,hdisj⟩ := goldbach_weighted_lower_prime_partition R z hR hRz
  unfold goldbachLowerTheta
  rw [←hunion,prod_union hdisj,prod_filter]
  congr 1
  apply prod_congr rfl
  intro p hp
  have hs := (mem_goldbach_weighted_outer_primes R z 3 p).mp hp
  simp only [goldbachLowerDensity,goldbachLocalDensity,ite_eq_right (not_le_of_gt hs.2.2.1)]

theorem goldbach_weighted_lower_normalization (ψ : SchwartzMap ℝ ℝ) (N n : ℕ)
    (R z : ℝ) (hR : 3≤R) (hRz : R<z) (hn : ((n:ℤ):ZMod 24)=12) :
    goldbachLowerMainTerm ψ N R n*goldbachLowerTheta R z n=
      3*goldbachWeightedC R n*
        (goldbachSingularIntegral ψ N 1 R n (N:ℝ) ((N:ℝ)^2)).re*
          goldbachWeightedOuterProduct R z 3 := by
  classical
  have hG : goldbachArithmeticFactor R 24 1 11 n=
      (((goldbachArithmeticFactor R 24 1 11 n).re:ℝ):ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im]
      exact (goldbach_lower_base_real_positive R hR n hn).2
  have hsmall := goldbach_weighted_lower_small_product R hR n hn
  rw [goldbach_weighted_lower_theta_partition R z hR hRz]
  unfold goldbachLowerMainTerm
  rw [hG,show Nat.totient 24=8 by decide]
  simp only [Nat.cast_ofNat,Complex.div_ofNat_re,Complex.mul_re,Complex.div_ofNat_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_div,zero_mul,sub_zero]
  nlinarith only [congrArg (fun t : ℝ=>t*
    (goldbachSingularIntegral ψ N 1 R n (N:ℝ) ((N:ℝ)^2)).re*
      goldbachWeightedOuterProduct R z 3) hsmall]

theorem goldbach_weighted_prime_coprime_twelve {p : ℕ} (hp : p.Prime) (hp3 : 3<p)
    (ℓ : ℕ) : GoldbachFixedUpperSievePrime ℓ p ↔ ¬p∣ℓ := by
  have hc : p.Coprime 12 := Nat.Coprime.of_dvd_right (by decide : 12∣24)
    (goldbach_large_prime_coprime_twentyfour p hp hp3)
  have hnot : ¬p∣12 := hp.coprime_iff_not_dvd.mp hc
  constructor
  · intro hh hd
    exact hh.2 (hd.mul_left 12)
  · intro hh
    exact ⟨hp,fun hd=>hh ((hp.dvd_mul.mp hd).resolve_left hnot)⟩

theorem goldbach_weighted_upper_prime_partition (R z : ℝ) (hR : 3≤R) (hRz : R<z) (ℓ : ℕ) :
    (goldbachLargeLocalPrimes R).filter (fun p : ℕ=>¬p∣ℓ)∪
      (goldbachWeightedOuterPrimes R z 0).filter (fun p : ℕ=>¬p∣ℓ)=
        goldbachUpperSievePrimes ℓ z ∧
    Disjoint ((goldbachLargeLocalPrimes R).filter (fun p : ℕ=>¬p∣ℓ))
      ((goldbachWeightedOuterPrimes R z 0).filter (fun p : ℕ=>¬p∣ℓ)) := by
  classical
  constructor
  · ext p
    simp only [mem_union,mem_filter,mem_goldbach_weighted_outer_primes,
      mem_goldbach_upper_sieve_primes]
    rw [mem_goldbach_large_local_primes (by linarith : (0:ℝ)≤R)]
    constructor
    · rintro (⟨⟨hp,hp3,hpR⟩,hnot⟩|⟨⟨hp,hp3,_,hpz,_⟩,hnot⟩)
      · exact ⟨(goldbach_weighted_prime_coprime_twelve hp hp3 ℓ).mpr hnot,hpR.trans_lt hRz⟩
      · exact ⟨(goldbach_weighted_prime_coprime_twelve hp hp3 ℓ).mpr hnot,hpz⟩
    · rintro ⟨hW,hpz⟩
      have hp3 : 3<p := by
        have := hW.1.two_le
        by_contra! hh
        have he : p=2 ∨ p=3 := by omega
        rcases he with he|he <;> apply hW.2 <;> rw [he] <;> omega
      have hnot := (goldbach_weighted_prime_coprime_twelve hW.1 hp3 ℓ).mp hW
      by_cases hpR : (p:ℝ)≤R
      · exact Or.inl ⟨⟨hW.1,hp3,hpR⟩,hnot⟩
      · exact Or.inr ⟨⟨hW.1,hp3,lt_of_not_ge hpR,hpz,Or.inl trivial⟩,hnot⟩
  · apply disjoint_left.mpr
    intro p hp hq
    have hpR := ((mem_goldbach_large_local_primes (by linarith) p).mp (mem_filter.mp hp).1).2.2
    exact not_lt_of_ge hpR
      ((mem_goldbach_weighted_outer_primes R z 0 p).mp (mem_filter.mp hq).1).2.2.1

theorem goldbach_weighted_upper_theta_partition (R z : ℝ) (hR : 3≤R) (hRz : R<z)
    (ℓ : ℕ) (n : ℤ) :
    goldbachUpperTheta R z ℓ n=
      (∏ p∈goldbachLargeLocalPrimes R,if p∣ℓ then 1 else 1-goldbachUpperDensity R n p)*
        ∏ p∈goldbachWeightedOuterPrimes R z 0,if p∣ℓ then 1 else 1-1/((p:ℝ)-1) := by
  classical
  obtain ⟨hunion,hdisj⟩ := goldbach_weighted_upper_prime_partition R z hR hRz ℓ
  unfold goldbachUpperTheta
  rw [←hunion,prod_union hdisj,prod_filter,prod_filter]
  have he (p : ℕ) (x : ℝ) : (if ¬p∣ℓ then x else 1)=(if p∣ℓ then 1 else x) := by
    by_cases h : p∣ℓ <;> simp only [h,not_true_eq_false,not_false_eq_true,ite_true,ite_false]
  simp_rw [he]
  congr 1
  apply prod_congr rfl
  intro p hp
  have hs := (mem_goldbach_weighted_outer_primes R z 0 p).mp hp
  simp only [goldbachUpperDensity,goldbachLocalDensity,ite_eq_right (not_le_of_gt hs.2.2.1)]

theorem goldbach_weighted_divisor_product (R z : ℝ) (hR : 3≤R) (u : ℕ) (hu : 0<u)
    (huz : (u:ℝ)<z) (hU : ∀ p : ℕ,p.Prime→p∣u→p%4=1) (n : ℤ) :
    (∏ p∈goldbachLargeLocalPrimes R,if p∣u then goldbachWeightedPrimeValue R n p else 1)*
      (∏ p∈goldbachWeightedOuterPrimes R z 0,if p∣u then goldbachWeightedPrimeValue R n p else 1)=
        goldbachWeightedMultiplicative R n u := by
  classical
  let P := (goldbachLargeLocalPrimes R).filter (fun p : ℕ=>p∣u)
  let Q := (goldbachWeightedOuterPrimes R z 0).filter (fun p : ℕ=>p∣u)
  have hd : Disjoint P Q := by
    apply disjoint_left.mpr
    intro p hp hq
    have hpR := ((mem_goldbach_large_local_primes (by linarith) p).mp (mem_filter.mp hp).1).2.2
    exact not_lt_of_ge hpR
      ((mem_goldbach_weighted_outer_primes R z 0 p).mp (mem_filter.mp hq).1).2.2.1
  have he : P∪Q=u.primeFactors := by
    ext p
    simp only [P,Q,mem_union,mem_filter]
    constructor
    · rintro (⟨hp,hpu⟩|⟨hp,hpu⟩)
      · exact (((mem_goldbach_large_local_primes (by linarith) p).mp hp).1).mem_primeFactors hpu hu.ne'
      · exact (((mem_goldbach_weighted_outer_primes R z 0 p).mp hp).1).mem_primeFactors hpu hu.ne'
    · intro hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hpu := Nat.dvd_of_mem_primeFactors hp
      have hp3 : 3<p := by have := hU p hprime hpu;have := hprime.two_le;omega
      have hpuR : (p:ℝ)≤u := by exact_mod_cast Nat.le_of_dvd hu hpu
      have hpz : (p:ℝ)<z := hpuR.trans_lt huz
      by_cases hpR : (p:ℝ)≤R
      · exact Or.inl ⟨(mem_goldbach_large_local_primes (by linarith) p).mpr ⟨hprime,hp3,hpR⟩,hpu⟩
      · exact Or.inr ⟨(mem_goldbach_weighted_outer_primes R z 0 p).mpr
          ⟨hprime,hp3,lt_of_not_ge hpR,hpz,Or.inl rfl⟩,hpu⟩
  rw [←prod_filter,←prod_filter]
  change (∏ p∈P,goldbachWeightedPrimeValue R n p)*(∏ p∈Q,goldbachWeightedPrimeValue R n p)=_
  rw [←prod_union hd,he]
  simp only [goldbachWeightedMultiplicative,ite_eq_right hu.ne']

theorem goldbach_weighted_upper_outer_product (R z : ℝ) (hR : 3≤R) (u p₂ : ℕ)
    (hp₂ : p₂.Prime) (hzp₂ : z≤(p₂:ℝ))
    (hU : ∀ p : ℕ,p.Prime→p∣u→p%4=1) (n : ℤ) :
    (∏ p∈goldbachWeightedOuterPrimes R z 0,if p∣2*u*p₂ then 1 else 1-1/((p:ℝ)-1))=
      goldbachWeightedOuterProduct R z 0*
        ∏ p∈goldbachWeightedOuterPrimes R z 0,if p∣u then goldbachWeightedPrimeValue R n p else 1 := by
  classical
  rw [goldbachWeightedOuterProduct,←prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  obtain ⟨hprime,hp3,hRp,hpz,_⟩ := (mem_goldbach_weighted_outer_primes R z 0 p).mp hp
  have hd : p∣2*u*p₂ ↔p∣u := goldbach_weighted_small_divisors (u:=u)
    (R:=(p:ℝ)) (by positivity) hp₂ (hpz.trans_le hzp₂) p
      ((mem_goldbach_large_local_primes (by positivity) p).mpr ⟨hprime,hp3,le_rfl⟩)
  by_cases hpu : p∣u
  · rw [ite_eq_left (hd.mpr hpu),ite_eq_left hpu,
      goldbach_weighted_prime_above R n p hRp,goldbachBaselinePrimeValue,ite_eq_left (hU p hprime hpu)]
    have hpR : (3:ℝ)<p := by exact_mod_cast hp3
    field_simp [show (p:ℝ)-1≠0 by linarith,show (p:ℝ)-2≠0 by linarith]
    ring
  · rw [ite_eq_right (show ¬p∣2*u*p₂ from fun h=>hpu (hd.mp h)),ite_eq_right hpu,mul_one]

theorem goldbach_weighted_upper_arithmetic_normalization (R z : ℝ) (hR : 3≤R) (hRz : R<z)
    (u p₂ : ℕ) (hu : 0<u) (huz : (u:ℝ)<z) (hp₂ : p₂.Prime) (hzp₂ : z≤(p₂:ℝ))
    (hU : ∀ p : ℕ,p.Prime→p∣u→p%4=1) (n : ℤ) (hn : (n:ZMod 24)=12) :
    goldbachArithmeticFactor R 12 ((2*u*p₂:ℕ):ℤ) (goldbachUpperBaseResidue (2*u*p₂):ℤ) (n-1)=
      ((24*∏ p∈goldbachLargeLocalPrimes R,goldbachUpperArithmeticReal p (2*u*p₂) n:ℝ):ℂ) ∧
    (goldbachArithmeticFactor R 12 ((2*u*p₂:ℕ):ℤ) (goldbachUpperBaseResidue (2*u*p₂):ℤ) (n-1)).re*
      goldbachUpperTheta R z (2*u*p₂) n=
        24*goldbachWeightedB R n*goldbachWeightedMultiplicative R n u*
          goldbachWeightedOuterProduct R z 0 := by
  classical
  have hu6 : u.Coprime 6 := goldbach_sieve_support_coprime_six u (by
    intro p hp hpu
    have := hU p hp hpu
    have := hp.two_le
    omega)
  have hp₃ : 3<p₂ := by exact_mod_cast hR.trans_lt (hRz.trans_le hzp₂)
  have hp6 : p₂.Coprime 6 := Nat.Coprime.of_dvd_right (by decide : 6∣24)
    (goldbach_large_prime_coprime_twentyfour p₂ hp₂ hp₃)
  have hv := hu6.mul_left hp6
  have he : 2*(u*p₂)=2*u*p₂ := by ring
  have hG := goldbach_upper_arithmetic_real_product R hR (u*p₂) hv n hn
  rw [he] at hG
  refine ⟨hG,?_⟩
  rw [hG,Complex.ofReal_re,goldbach_weighted_upper_theta_partition R z hR hRz,
    goldbach_weighted_upper_outer_product R z hR u p₂ hp₂ hzp₂ hU n]
  have hs := goldbach_weighted_upper_small_product R hR u p₂ hp₂ (hRz.trans_le hzp₂) hU n
  have hd := goldbach_weighted_divisor_product R z hR u hu huz hU n
  calc
    _=24*((∏ p∈goldbachLargeLocalPrimes R,goldbachUpperArithmeticReal p (2*u*p₂) n)*
        (∏ p∈goldbachLargeLocalPrimes R,if p∣2*u*p₂ then 1 else 1-goldbachUpperDensity R n p))*
        goldbachWeightedOuterProduct R z 0*
        (∏ p∈goldbachWeightedOuterPrimes R z 0,if p∣u then goldbachWeightedPrimeValue R n p else 1) := by ring
    _=24*(goldbachWeightedB R n*
        (∏ p∈goldbachLargeLocalPrimes R,if p∣u then goldbachWeightedPrimeValue R n p else 1))*
        goldbachWeightedOuterProduct R z 0*
        (∏ p∈goldbachWeightedOuterPrimes R z 0,if p∣u then goldbachWeightedPrimeValue R n p else 1) := by rw [hs]
    _=24*goldbachWeightedB R n*
        ((∏ p∈goldbachLargeLocalPrimes R,if p∣u then goldbachWeightedPrimeValue R n p else 1)*
          (∏ p∈goldbachWeightedOuterPrimes R z 0,if p∣u then goldbachWeightedPrimeValue R n p else 1))*
        goldbachWeightedOuterProduct R z 0 := by ring
    _=_ := by rw [hd]

theorem goldbach_weighted_upper_normalization (ψ : SchwartzMap ℝ ℝ) (N n : ℕ)
    (R z : ℝ) (hR : 3≤R) (hRz : R<z)
    (u p₂ : ℕ) (hu : 0<u) (huz : (u:ℝ)<z) (hp₂ : p₂.Prime) (hzp₂ : z≤(p₂:ℝ))
    (hU : ∀ p : ℕ,p.Prime→p∣u→p%4=1) (hn : ((n:ℤ):ZMod 24)=12) :
    goldbachUpperMainTerm ψ N R (2*u*p₂) n*goldbachUpperTheta R z (2*u*p₂) n=
      6*goldbachWeightedB R n*goldbachWeightedMultiplicative R n u/
        ((2*u*p₂:ℕ):ℝ)*
        (goldbachSingularIntegral ψ N (2*u*p₂) R ((n:ℝ)-1) (N:ℝ) ((N:ℝ)^2)).re*
          goldbachWeightedOuterProduct R z 0 := by
  classical
  obtain ⟨hG,hs⟩ := goldbach_weighted_upper_arithmetic_normalization R z hR hRz u p₂ hu huz hp₂ hzp₂ hU (n:ℤ) hn
  have hG' : goldbachArithmeticFactor R 12 ((2*u*p₂:ℕ):ℤ) (goldbachUpperBaseResidue (2*u*p₂):ℤ) ((n:ℤ)-1)=
      (((goldbachArithmeticFactor R 12 ((2*u*p₂:ℕ):ℤ)
        (goldbachUpperBaseResidue (2*u*p₂):ℤ) ((n:ℤ)-1)).re:ℝ):ℂ) := by
    rw [hG,Complex.ofReal_re]
  unfold goldbachUpperMainTerm
  rw [hG',show Nat.totient 12=4 by decide]
  have hc : ((2*u*p₂:ℕ):ℂ)*((4:ℕ):ℂ)=(((2*u*p₂:ℕ):ℝ)*4:ℝ) := by push_cast;ring
  rw [hc,←Complex.ofReal_div]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hℓ : ((2*u*p₂:ℕ):ℝ)≠0 := by exact_mod_cast mul_ne_zero (mul_ne_zero (by decide : (2:ℕ)≠0) hu.ne') hp₂.ne_zero
  apply (mul_right_cancel₀ hℓ)
  have hh := congrArg (fun t : ℝ=>t*
    (goldbachSingularIntegral ψ N (2*u*p₂) R ((n:ℝ)-1) (N:ℝ) ((N:ℝ)^2)).re) hs
  field_simp at hh ⊢
  nlinarith only [hh]

end PrimeSquares
