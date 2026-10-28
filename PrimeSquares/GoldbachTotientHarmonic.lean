import PrimeSquares.GoldbachEuclideanDecay
import PrimeSquares.CorrelationWeightedHarmonic

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_reciprocal_totient_majorant (n : ℕ) (hn : 0<n) :
    (n.totient:ℝ)⁻¹≤conductorCorrelationProduct n/(n:ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hφ : (0:ℝ)<n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hpred : ((∏ p∈n.primeFactors,(p-1:ℕ)):ℝ)=∏ p∈n.primeFactors,((p:ℝ)-1) := by
    apply prod_congr rfl
    intro p hp
    simpa only [Nat.cast_one] using (Nat.cast_sub (R:=ℝ) (Nat.prime_of_mem_primeFactors hp).one_le)
  have hpos : 0<∏ p∈n.primeFactors,((p:ℝ)-1) := prod_pos (fun p hp => by
    have hh : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith)
  have he : (n:ℝ)/(n.totient:ℝ)=∏ p∈n.primeFactors,(p:ℝ)/((p:ℝ)-1) := by
    rw [prod_div_distrib]
    apply (div_eq_div_iff hφ.ne' hpos.ne').mpr
    have hh : (n.totient:ℝ)*(∏ p∈n.primeFactors,(p:ℝ))=
        (n:ℝ)*((∏ p∈n.primeFactors,(p-1:ℕ)):ℝ) := by
      have hh := congrArg (fun z : ℕ => (z:ℝ)) (Nat.totient_mul_prod_primeFactors n)
      simpa only [Nat.cast_mul,Nat.cast_prod] using hh
    rw [hpred] at hh
    nlinarith only [hh]
  have hb : (n:ℝ)/(n.totient:ℝ)≤conductorCorrelationProduct n := by
    rw [he,conductorCorrelationProduct]
    apply prod_le_prod₀
    · intro p hp
      have hh : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
    · intro p hp
      have hh : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  apply (le_div_iff₀ hnR).mpr
  simpa only [div_eq_mul_inv,mul_comm] using hb

theorem goldbach_reciprocal_totient_sum (D : ℕ) :
    (∑ n∈Icc 1 D,(n.totient:ℝ)⁻¹)≤Real.exp 2*(harmonic D:ℝ) := by
  apply (sum_le_sum (fun n hn => goldbach_reciprocal_totient_majorant n (mem_Icc.mp hn).1)).trans
  exact conductorCorrelationProduct_weighted_harmonic D

theorem goldbach_reciprocal_totient_multiples (d D : ℕ) (hd : 0<d) :
    (∑ n∈(Icc 1 D).filter (fun n => d∣n),(n.totient:ℝ)⁻¹)≤
      (d.totient:ℝ)⁻¹*(Real.exp 2*(harmonic D:ℝ)) := by
  classical
  have hφ : (0:ℝ)<d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hb : (∑ n∈(Icc 1 D).filter (fun n => d∣n),(n.totient:ℝ)⁻¹)≤
      (d.totient:ℝ)⁻¹*(∑ m∈Icc 1 D,(m.totient:ℝ)⁻¹) := by
    rw [mul_sum]
    apply sum_le_sum_of_injOn (fun n => n/d)
    · intro n hn m hm he
      dsimp only at he
      have hdn := (mem_filter.mp hn).2
      have hdm := (mem_filter.mp hm).2
      calc
        n=d*(n/d) := (Nat.mul_div_cancel' hdn).symm
        _=d*(m/d) := by rw [he]
        _=m := Nat.mul_div_cancel' hdm
    · intro m hm
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hm
      obtain ⟨hn,hdn⟩ := mem_filter.mp hn
      obtain ⟨hn0,hnD⟩ := mem_Icc.mp hn
      exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn0 hdn) hd,(Nat.div_le_self _ _).trans hnD⟩
    · intro n hn
      have hdn := (mem_filter.mp hn).2
      have hn0 := (mem_Icc.mp (mem_filter.mp hn).1).1
      have hm0 := Nat.div_pos (Nat.le_of_dvd hn0 hdn) hd
      have hmφ : (0:ℝ)<(n/d).totient := by exact_mod_cast Nat.totient_pos.mpr hm0
      have hh : (d.totient:ℝ)*((n/d).totient:ℝ)≤n.totient := by
        exact_mod_cast (Nat.totient_super_multiplicative d (n/d)).trans_eq
          (congrArg Nat.totient (Nat.mul_div_cancel' hdn))
      simpa only [one_div,mul_inv_rev,mul_comm] using one_div_le_one_div_of_le
        (mul_pos hφ hmφ) hh
    · intro m _ _;positivity
  exact hb.trans (mul_le_mul_of_nonneg_left (goldbach_reciprocal_totient_sum D) (by positivity))

theorem goldbach_gcd_totient_divisor_expansion (q n : ℕ) (hq : 0<q) :
    (q.gcd n:ℝ)=∑ d∈q.divisors,if d∣n then (d.totient:ℝ) else 0 := by
  classical
  have hg : q.gcd n≠0 := (Nat.gcd_pos_of_pos_left n hq).ne'
  have hset : (q.gcd n).divisors=q.divisors.filter (fun d => d∣n) := by
    ext d
    constructor
    · intro hd
      have hh := (Nat.mem_divisors.mp hd).1
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hh.trans (Nat.gcd_dvd_left q n),hq.ne'⟩,
        hh.trans (Nat.gcd_dvd_right q n)⟩
    · intro hd
      obtain ⟨hdq,hdn⟩ := mem_filter.mp hd
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd (Nat.mem_divisors.mp hdq).1 hdn,hg⟩
  rw [←sum_filter,←hset]
  exact_mod_cast (Nat.sum_totient (q.gcd n)).symm

end PrimeSquares
