import PrimeSquares.GoldbachWeightedRectangles
import PrimeSquares.GoldbachWeightedKernels

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachWeightedActivePrimes (N : ℕ) (z a : ℝ) : Finset ℕ := by
  classical
  exact (goldbachWeightedRectanglePrimes N z).filter
    (fun p : ℕ=>a≤(N:ℝ)^2/(2*(p:ℝ)^2))

theorem goldbach_weighted_pair_log_floor (N : ℕ) (z : ℝ) (hz : 2≤z) (i : ℕ×ℕ)
    (hi : i∈goldbachWeightedPairs N z) :
    Real.log z≤Real.log ((N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ)) := by
  obtain ⟨hu,_,hp,_,hpz,hpB,_⟩ := (mem_goldbach_weighted_pairs N z i).mp hi
  have hu0 : (0:ℝ)< i.1 := by exact_mod_cast hu
  have hp0 : (0:ℝ)< i.2 := by exact_mod_cast hp.pos
  have hsq := (Real.lt_sqrt hp0.le).mp hpB
  have hh := (lt_div_iff₀ (show 0<2*(i.1:ℝ) by positivity)).mp hsq
  have hℓ : (0:ℝ)<((2*i.1*i.2:ℕ):ℝ) := by
    push_cast
    positivity
  have hratio : (i.2:ℝ)<(N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ) := by
    apply (lt_div_iff₀ hℓ).mpr
    push_cast
    nlinarith only [hh]
  exact Real.log_le_log (by linarith : 0<z) (hpz.trans hratio.le)

theorem goldbach_weighted_kernel_small (R z a : ℝ) (N : ℕ) (n : ℤ)
    (hz : 2≤z) (ha : 2≤a) :
    (∑ i∈(goldbachWeightedPairs N z).filter (fun i : ℕ×ℕ=>(i.1:ℝ)≤a),
      goldbachWeightedMultiplicative R n i.1/
        (((2*i.1*i.2:ℕ):ℝ)*(Real.log ((N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ)))^2))≤
      (1/(2*(Real.log z)^2))*(∑ u∈Icc 1 ⌊a⌋₊,goldbachWeightedMultiplicative R n u/(u:ℝ))*
        (∑ p∈goldbachWeightedRectanglePrimes N z,1/(p:ℝ)) := by
  classical
  let S := (goldbachWeightedPairs N z).filter (fun i : ℕ×ℕ=>(i.1:ℝ)≤a)
  let G := fun i : ℕ×ℕ=>(goldbachWeightedMultiplicative R n i.1/(i.1:ℝ))*(1/(i.2:ℝ))
  let c := 1/(2*(Real.log z)^2)
  have hc : 0≤c := by dsimp only [c];positivity
  have hpoint : ∀ i∈S,
      goldbachWeightedMultiplicative R n i.1/
        (((2*i.1*i.2:ℕ):ℝ)*(Real.log ((N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ)))^2)≤c*G i := by
    intro i hi
    have hiI := (mem_filter.mp hi).1
    have hlog := goldbach_weighted_pair_log_floor N z hz i hiI
    have hlogz : 0<Real.log z := Real.log_pos (by linarith)
    have hrec := one_div_le_one_div_of_le (sq_pos_of_pos hlogz)
      (pow_le_pow_left₀ hlogz.le hlog 2)
    have hG : 0≤G i := by
      dsimp only [G]
      exact mul_nonneg (div_nonneg (goldbach_weighted_multiplicative_nonneg R n _) (Nat.cast_nonneg _)) (by positivity)
    have hh := mul_le_mul_of_nonneg_left hrec ((mul_nonneg (by norm_num : (0:ℝ)≤1/2) hG))
    convert hh using 1 <;> dsimp only [c,G] <;> push_cast <;>
      simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
  have hcover : ∀ i∈S,i.2∈goldbachWeightedRectanglePrimes N z ∧ i.1∈Icc 1 ⌊a⌋₊ := by
    intro i hi
    obtain ⟨hiI,hia⟩ := mem_filter.mp hi
    have hu := ((mem_goldbach_weighted_pairs N z i).mp hiI).1
    exact ⟨(goldbach_weighted_pair_rectangle N z i hiI).1,
      mem_Icc.mpr ⟨hu,(Nat.le_floor_iff (by linarith : (0:ℝ)≤a)).mpr hia⟩⟩
  have hsum := goldbach_finite_fiber_upper S (goldbachWeightedRectanglePrimes N z)
    (fun _=>Icc 1 ⌊a⌋₊) G hcover (fun p _ u _=>by
      dsimp only [G]
      exact mul_nonneg (div_nonneg (goldbach_weighted_multiplicative_nonneg R n u) (Nat.cast_nonneg _)) (by positivity))
  have hs0 : (∑ i∈S,goldbachWeightedMultiplicative R n i.1/
      (((2*i.1*i.2:ℕ):ℝ)*(Real.log ((N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ)))^2))≤c*∑ i∈S,G i := by
    rw [mul_sum]
    exact sum_le_sum hpoint
  have hh := hs0.trans (mul_le_mul_of_nonneg_left hsum hc)
  apply hh.trans_eq
  dsimp only [G,c]
  simp_rw [←sum_mul]
  rw [←mul_sum]
  ring

theorem goldbach_weighted_kernel_large (R z a : ℝ) (N : ℕ) (n : ℤ)
    (hN : 2≤N) (ha : 2≤a) :
    (∑ i∈(goldbachWeightedPairs N z).filter (fun i : ℕ×ℕ=>¬(i.1:ℝ)≤a),
      goldbachWeightedMultiplicative R n i.1/
        (((2*i.1*i.2:ℕ):ℝ)*(Real.log ((N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ)))^2))≤
      (1/2:ℝ)*∑ p∈goldbachWeightedActivePrimes N z a,(1/(p:ℝ))*
        ∑ u∈Ioc ⌊a⌋₊ ⌊(N:ℝ)^2/(2*(p:ℝ)^2)⌋₊,
          goldbachWeightedMultiplicative R n u/
            ((u:ℝ)*(Real.log ((N:ℝ)^2)-Real.log (2*(p:ℝ))-Real.log u)^2) := by
  classical
  let S := (goldbachWeightedPairs N z).filter (fun i : ℕ×ℕ=>¬(i.1:ℝ)≤a)
  let F := fun i : ℕ×ℕ=>goldbachWeightedMultiplicative R n i.1/
    (((2*i.1*i.2:ℕ):ℝ)*(Real.log ((N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ)))^2)
  have hcover : ∀ i∈S,i.2∈goldbachWeightedActivePrimes N z a ∧
      i.1∈Ioc ⌊a⌋₊ ⌊(N:ℝ)^2/(2*(i.2:ℝ)^2)⌋₊ := by
    intro i hi
    obtain ⟨hiI,hia⟩ := mem_filter.mp hi
    have hrect := goldbach_weighted_pair_rectangle N z i hiI
    have hub := (mem_Icc.mp hrect.2).2
    have hupper : (i.1:ℝ)≤(N:ℝ)^2/(2*(i.2:ℝ)^2) :=
      (Nat.le_floor_iff (by positivity : (0:ℝ)≤(N:ℝ)^2/(2*(i.2:ℝ)^2))).mp hub
    refine ⟨mem_filter.mpr ⟨hrect.1,(le_of_lt (lt_of_not_ge hia)).trans hupper⟩,
      mem_Ioc.mpr ⟨(Nat.floor_lt (by linarith : (0:ℝ)≤a)).mpr (lt_of_not_ge hia),hub⟩⟩
  have hs := goldbach_finite_fiber_upper S (goldbachWeightedActivePrimes N z a)
    (fun p : ℕ=>Ioc ⌊a⌋₊ ⌊(N:ℝ)^2/(2*(p:ℝ)^2)⌋₊) F hcover
    (by
      intro p hp u hu
      exact div_nonneg (goldbach_weighted_multiplicative_nonneg R n u)
        (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
  apply hs.trans_eq
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [mul_sum,mul_sum]
  apply sum_congr rfl
  intro u hu
  have hpP := (mem_filter.mp hp).1
  have hprime := (mem_filter.mp hpP).2.1
  have hp0 : (0:ℝ)<p := by exact_mod_cast hprime.pos
  have hua : a<(u:ℝ) := (Nat.floor_lt (by linarith : (0:ℝ)≤a)).mp (mem_Ioc.mp hu).1
  have hu0 : (0:ℝ)<u := by linarith
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have he : Real.log ((N:ℝ)^2/((2*u*p:ℕ):ℝ))=
      Real.log ((N:ℝ)^2)-Real.log (2*(p:ℝ))-Real.log u := by
    push_cast
    rw [show 2*(u:ℝ)*(p:ℝ)=(2*(p:ℝ))*(u:ℝ) by ring]
    rw [Real.log_div (sq_pos_of_pos hN0).ne' (mul_ne_zero (show 2*(p:ℝ)≠0 by positivity) hu0.ne'),
      Real.log_mul (show 2*(p:ℝ)≠0 by positivity) hu0.ne']
    ring
  dsimp only [F]
  rw [he]
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end PrimeSquares
