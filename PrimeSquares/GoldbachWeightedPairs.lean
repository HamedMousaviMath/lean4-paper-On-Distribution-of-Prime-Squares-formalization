import PrimeSquares.GoldbachWeightedHarmonic

set_option autoImplicit false
open Finset
namespace PrimeSquares

def GoldbachWeightedPair (N : ℕ) (z : ℝ) (i : ℕ×ℕ) : Prop :=
  0 < i.1 ∧ (i.1:ℝ) < (N:ℝ)^2/(2*z^2) ∧ i.2.Prime ∧ i.2%4=3 ∧
    z≤(i.2:ℝ) ∧ (i.2:ℝ) < Real.sqrt ((N:ℝ)^2/(2*(i.1:ℝ))) ∧
    ∀ p : ℕ,p.Prime→p∣i.1→p%4=1

noncomputable def goldbachWeightedPairs (N : ℕ) (z : ℝ) : Finset (ℕ×ℕ) := by
  classical
  exact ((range (N^2))×ˢ(range (N^2))).filter (GoldbachWeightedPair N z)

theorem goldbach_weighted_pair_multiplier (N : ℕ) (z : ℝ) (i : ℕ×ℕ)
    (hi : GoldbachWeightedPair N z i) : GoldbachClosedL N z (2*i.1*i.2) := by
  exact ⟨i.1,i.2,hi.1,rfl,hi.2⟩

theorem mem_goldbach_weighted_pairs (N : ℕ) (z : ℝ) (i : ℕ×ℕ) :
    i∈goldbachWeightedPairs N z ↔ GoldbachWeightedPair N z i := by
  classical
  constructor
  · intro hi;exact (mem_filter.mp hi).2
  · intro hi
    have hsize := goldbachClosedL_bound (goldbach_weighted_pair_multiplier N z i hi)
    have hu := hi.1
    have hp := hi.2.2.1.two_le
    have huB : i.1<N^2 := by nlinarith
    have hpB : i.2<N^2 := by nlinarith
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr huB,mem_range.mpr hpB⟩,hi⟩

theorem goldbach_weighted_pair_injective (N : ℕ) (z : ℝ) :
    Set.InjOn (fun i : ℕ×ℕ=>2*i.1*i.2) (goldbachWeightedPairs N z) := by
  intro i hi j hj he
  dsimp only at he
  have hI := (mem_goldbach_weighted_pairs N z i).mp hi
  have hJ := (mem_goldbach_weighted_pairs N z j).mp hj
  have hp := hI.2.2.1
  have hq := hJ.2.2.1
  have hp3 := hI.2.2.2.1
  have hp2 : ¬i.2∣2 := by
    intro h
    have hh := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp h
    omega
  have hpv : ¬i.2∣j.1 := by
    intro h
    have h4 := hJ.2.2.2.2.2.2 i.2 hp h
    omega
  have hpq : i.2∣j.2 := by
    have hdiv : i.2∣2*i.1*i.2 := dvd_mul_left i.2 (2*i.1)
    rw [he] at hdiv
    rcases hp.dvd_mul.mp hdiv with h|h
    · exact False.elim (hpv ((hp.dvd_mul.mp h).resolve_left hp2))
    · exact h
  have hpEq := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  have huEq : i.1=j.1 := by
    rw [hpEq] at he
    have hqp := hq.pos
    nlinarith only [he,hqp]
  exact Prod.ext huEq hpEq

theorem goldbach_weighted_pairs_image (N : ℕ) (z : ℝ) :
    (goldbachWeightedPairs N z).image (fun i=>2*i.1*i.2)=goldbachClosedLSet N z := by
  classical
  ext ℓ
  constructor
  · rintro h
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    exact mem_goldbachClosedLSet.mpr
      (goldbach_weighted_pair_multiplier N z i ((mem_goldbach_weighted_pairs N z i).mp hi))
  · intro h
    obtain ⟨u,p,hu,he,huB,hp,hp4,hpz,hpB,hU⟩ := mem_goldbachClosedLSet.mp h
    exact mem_image.mpr ⟨(u,p),(mem_goldbach_weighted_pairs N z (u,p)).mpr
      ⟨hu,huB,hp,hp4,hpz,hpB,hU⟩,he.symm⟩

theorem goldbach_weighted_pairs_sum (N : ℕ) (z : ℝ) (F : ℕ→ℝ) :
    (∑ ℓ∈goldbachClosedLSet N z,F ℓ)=∑ i∈goldbachWeightedPairs N z,F (2*i.1*i.2) := by
  classical
  rw [←goldbach_weighted_pairs_image N z]
  apply sum_image
  exact goldbach_weighted_pair_injective N z

theorem goldbach_weighted_pairs_harmonic (R z : ℝ) (N : ℕ) (n : ℤ)
    (K : ℝ) (hK : 0≤K) (hN : 2≤N) (hM : GoldbachClassicalIntervalMertens K) :
    (∑ i∈goldbachWeightedPairs N z,
      goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ))≤
      (3/2:ℝ)*((1+K/Real.log 2)*(Real.log ((N:ℝ)^2+1)/Real.log 2)^2)^3*
        (1+2*Real.log N) := by
  classical
  let I := Icc 1 (N^2)
  have hs : goldbachWeightedPairs N z⊆I×ˢI := by
    intro i hi
    have hvalid := (mem_goldbach_weighted_pairs N z i).mp hi
    have hrect := mem_product.mp (mem_filter.mp hi).1
    have hp := hvalid.2.2.1.pos
    have hu := hvalid.1
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,(mem_range.mp hrect.1).le⟩,
      mem_Icc.mpr ⟨by omega,(mem_range.mp hrect.2).le⟩⟩
  have hsum : (∑ i∈goldbachWeightedPairs N z,
      goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ))≤
      ∑ i∈I×ˢI,goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ) :=
    sum_le_sum_of_subset_of_nonneg hs (fun i _ _=>div_nonneg
      (goldbach_weighted_multiplicative_nonneg R n i.1) (Nat.cast_nonneg _))
  have he : (∑ i∈I×ˢI,goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ))=
      (1/2:ℝ)*(∑ u∈I,goldbachWeightedMultiplicative R n u/(u:ℝ))*(∑ p∈I,(p:ℝ)⁻¹) := by
    calc
      _=∑ u∈I,(1/2:ℝ)*(goldbachWeightedMultiplicative R n u/(u:ℝ))*(∑ p∈I,(p:ℝ)⁻¹) := by
        rw [sum_product]
        apply sum_congr rfl
        intro u hu
        rw [mul_sum]
        apply sum_congr rfl
        intro p hp
        push_cast
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      _=_ := by rw [←sum_mul,←mul_sum]
  have hH : (∑ p∈I,(p:ℝ)⁻¹)≤1+2*Real.log N := by
    have heq : (∑ p∈I,(p:ℝ)⁻¹)=(harmonic (N^2):ℝ) := by
      dsimp only [I]
      rw [harmonic_eq_sum_Icc,Rat.cast_sum]
      simp only [Rat.cast_inv,Rat.cast_natCast]
    rw [heq]
    have hh := harmonic_le_one_add_log (N^2)
    simpa only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] using hh
  have hNreal : (2:ℝ)≤(N:ℝ)^2 := by
    have hh : (2:ℝ)≤N := by exact_mod_cast hN
    nlinarith
  have hweight := goldbach_weighted_harmonic_uniform R n K ((N^2:ℕ):ℝ) hK (by exact_mod_cast hNreal) hM
  rw [Nat.floor_natCast] at hweight
  push_cast at hweight
  rw [he] at hsum
  apply hsum.trans
  have hsum0 : 0≤∑ u∈I,goldbachWeightedMultiplicative R n u/(u:ℝ) :=
    sum_nonneg (fun u _=>div_nonneg (goldbach_weighted_multiplicative_nonneg R n u) (Nat.cast_nonneg _))
  have hH0 : 0≤∑ p∈I,(p:ℝ)⁻¹ := sum_nonneg (fun p _=>inv_nonneg.mpr (Nat.cast_nonneg _))
  have hh := mul_le_mul hweight hH hH0
    (by have := Real.log_pos (by norm_num : (1:ℝ)<2);positivity)
  nlinarith only [hh]

end PrimeSquares
