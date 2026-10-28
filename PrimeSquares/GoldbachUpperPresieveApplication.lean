import PrimeSquares.GoldbachUpperPresieveUniform
import PrimeSquares.GoldbachUpperSequenceBridge

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachUpperSingleRemainder (ψ : SchwartzMap ℝ ℝ) (N ℓ : ℕ)
    (B R : ℝ) (c : ℕ→ℝ) (n : ℕ) : ℝ :=
  ∑ d∈(range (Nat.ceil (goldbachUpperDivisorLevel B N ℓ))).filter (fun d=>0<d),
    c d*(goldbachFullRemainder ψ N ℓ (12*d) (goldbachUpperSieveResidue ℓ d) R (n-1)).re

noncomputable def goldbachUpperRemainderSum (ψ : SchwartzMap ℝ ℝ) (N : ℕ)
    (B R : ℝ) (c : ℕ→ℕ→ℝ) (n : ℕ) : ℝ :=
  ∑ ℓ∈goldbachClosedLSet N ((N:ℝ)^(8/9:ℝ)),goldbachUpperSingleRemainder ψ N ℓ B R (c ℓ) n

theorem goldbach_upper_remainder_zero_extension (ψ : SchwartzMap ℝ ℝ) (N ℓ n : ℕ)
    (B R : ℝ) (c : ℕ→ℝ) :
    (∑ d∈range (Nat.ceil (goldbachUpperDivisorLevel B N ℓ)),c d*
      (if d=0 then 0 else (goldbachFullRemainder ψ N ℓ (12*d)
        (goldbachUpperSieveResidue ℓ d) R (n-1)).re))=
      goldbachUpperSingleRemainder ψ N ℓ B R c n := by
  classical
  unfold goldbachUpperSingleRemainder
  rw [sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases hd : d=0
  · simp [hd]
  · simp [hd,Nat.pos_of_ne_zero hd]

theorem goldbach_upper_sifted_sequence (n N ℓ : ℕ) :
    goldbachSequenceSiftedCount (goldbachUpperM n N ℓ) id
      (goldbachUpperSievePrimes ℓ (goldbachUpperSieveLimit N ℓ))=
        ((goldbachFixedUpperSifted n N ℓ).card:ℝ) := by
  classical
  unfold goldbachSequenceSiftedCount
  congr 2
  ext r
  simp only [mem_filter,goldbachFixedUpperSifted,id_eq]
  constructor
  · rintro ⟨hr,hp⟩
    exact ⟨hr,fun p hs hz=>hp p ((mem_goldbach_upper_sieve_primes ℓ _ p).mpr ⟨hs,hz⟩)⟩
  · rintro ⟨hr,hp⟩
    exact ⟨hr,fun p hs=>hp p ((mem_goldbach_upper_sieve_primes ℓ _ p).mp hs).1
      ((mem_goldbach_upper_sieve_primes ℓ _ p).mp hs).2⟩

theorem goldbach_upper_presieve_application
    (ψ : SchwartzMap ℝ ℝ) (hψ : ψ≠0) (N : ℕ) (hN : 2≤N)
    (ℓ : ℕ) (hℓ : ℓ∈goldbachClosedLSet N ((N:ℝ)^(8/9:ℝ)))
    (hz3 : (3:ℝ)<(N:ℝ)^(8/9:ℝ))
    (B C K K₀ c K₁ δ ε : ℝ) (f F : ℝ→ℝ)
    (hR : 3≤(Real.log N)^C) (hM : GoldbachClassicalFullIntervalMertens K)
    (hAt : GoldbachCorrectedPresieveAt.{0} N C 2 2 1 K K₀ c K₁ δ
      (goldbachUpperSieveLimit N ℓ) (goldbachUpperOuterLevel B N ℓ)
      (goldbachUpperPreliminaryPrimes ℓ ((Real.log N)^C) (goldbachUpperSieveLimit N ℓ))
      (goldbachUpperOuterPrimes ℓ ((Real.log N)^C) (goldbachUpperSieveLimit N ℓ)) f F)
    (hcoef : F (Real.log (goldbachUpperOuterLevel B N ℓ)/Real.log (goldbachUpperSieveLimit N ℓ))+
      goldbachUpperSieveError B C K K₀ c K₁ δ N ℓ≤F 2+ε) :
    ∃ cp : ℕ→ℝ,(∀ d : ℕ,|cp d|≤1) ∧ ∀ n : ℕ,0<n→n<N^2→(n:ZMod 24)=12→
      ((goldbachFixedUpperSifted n N ℓ).card:ℝ)≤
        goldbachUpperMainTerm ψ N ((Real.log N)^C) ℓ n*
          goldbachUpperTheta ((Real.log N)^C) (goldbachUpperSieveLimit N ℓ) ℓ n*(F 2+ε)+
            goldbachUpperSingleRemainder ψ N ℓ B ((Real.log N)^C) cp n := by
  classical
  dsimp only [GoldbachCorrectedPresieveAt] at hAt
  obtain ⟨cm,cp,hcoeff,_,hbound⟩ := hAt
  refine ⟨cp,fun d=>(hcoeff d).2,?_⟩
  intro n hn hnN hn24
  let R := (Real.log (N:ℝ))^C
  let z := goldbachUpperSieveLimit N ℓ
  let P := goldbachUpperPreliminaryPrimes ℓ R z
  let Q := goldbachUpperOuterPrimes ℓ R z
  let g := goldbachPrimeDensityProduct (goldbachUpperDensity R (n:ℤ))
  let r := fun d : ℕ=>if d=0 then 0 else
    (goldbachFullRemainder ψ N ℓ (12*d) (goldbachUpperSieveResidue ℓ d) R (n-1)).re
  obtain ⟨v,he,hv4,hv⟩ := goldbach_closed_multiplier_residue_data hz3 hℓ
  have hsplit := goldbach_upper_prime_split ℓ R z
  have hg : GoldbachMultiplicativeDensityOn (P∪Q) g := by
    rw [show P∪Q=goldbachUpperSievePrimes ℓ z from hsplit.2]
    exact goldbach_upper_density_multiplicative ℓ R z n
  have hX : 0≤goldbachUpperMainTerm ψ N R ℓ n := by
    rw [he];exact goldbach_upper_main_term_nonneg ψ hψ N hN R hR v n hv hn24
  have hdata : ∀ d : ℕ,Squarefree d→d.primeFactors⊆P∪Q→
      (d:ℝ)<Real.exp ((Real.log (Real.log N))^3)*goldbachUpperOuterLevel B N ℓ→
      goldbachSequenceDivisorCount (goldbachUpperM n N ℓ) id d=
        goldbachUpperMainTerm ψ N R ℓ n*g d+r d := by
    intro d hd hs _
    have hdc : d.Coprime (12*ℓ) := by
      apply Nat.coprime_of_dvd
      intro p hp hpd hpℓ
      have hsp := hs (hp.mem_primeFactors hpd hd.ne_zero)
      rw [show P∪Q=goldbachUpperSievePrimes ℓ z from hsplit.2] at hsp
      exact ((mem_goldbach_upper_sieve_primes ℓ z p).mp hsp).1.2 hpℓ
    have hn24' : n%24=12 := by
      have hh := (ZMod.natCast_eq_natCast_iff n 12 24).mp (by simpa only [Nat.cast_ofNat] using hn24)
      change n%24=12%24 at hh
      norm_num at hh
      exact hh
    simpa only [he,g,r,ite_eq_right hd.ne_zero] using
      goldbach_upper_divisor_real_identity ψ N n v d hN hn hnN hn24' hv hv4 R hR hd (by rwa [←he])
  have hb := (hbound g hg (goldbach_upper_preliminary_dimension ℓ K R z _ hM n)
    (goldbach_upper_outer_dimension ℓ K R z hM n) ℕ (goldbachUpperM n N ℓ) id
      (goldbachUpperMainTerm ψ N R ℓ n) hX r hdata).2
  have htheta : goldbachSieveProduct P g*goldbachSieveProduct Q g=goldbachUpperTheta R z ℓ n := by
    dsimp only [goldbachSieveProduct]
    rw [←prod_union hsplit.1,hsplit.2]
    apply prod_congr rfl
    intro p hp
    have hprime := ((mem_goldbach_upper_sieve_primes ℓ z p).mp hp).1.1
    simp only [g,goldbachPrimeDensityProduct,hprime.primeFactors,prod_singleton]
  change goldbachSequenceSiftedCount (goldbachUpperM n N ℓ) id (P∪Q)≤
    goldbachUpperMainTerm ψ N R ℓ n*goldbachSieveProduct P g*goldbachSieveProduct Q g*
      (F (Real.log (goldbachUpperOuterLevel B N ℓ)/Real.log z)+goldbachUpperSieveError B C K K₀ c K₁ δ N ℓ)+
      ∑ d∈range (Nat.ceil (Real.exp ((Real.log (Real.log N))^3)*goldbachUpperOuterLevel B N ℓ)),cp d*r d at hb
  rw [mul_assoc (goldbachUpperMainTerm ψ N R ℓ n),htheta,goldbach_upper_product_level,
    show P∪Q=goldbachUpperSievePrimes ℓ z from hsplit.2,goldbach_upper_sifted_sequence] at hb
  dsimp only [r] at hb
  rw [goldbach_upper_remainder_zero_extension] at hb
  exact hb.trans (add_le_add (mul_le_mul_of_nonneg_left hcoef
    (mul_nonneg hX (goldbach_upper_theta_positive R z ℓ n).le)) le_rfl)

end PrimeSquares
