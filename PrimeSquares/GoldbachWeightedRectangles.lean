import PrimeSquares.GoldbachWeightedPairs

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_finite_fiber_upper (S : Finset (ℕ×ℕ)) (P : Finset ℕ)
    (U : ℕ→Finset ℕ) (F : ℕ×ℕ→ℝ)
    (hcover : ∀ i∈S,i.2∈P ∧ i.1∈U i.2)
    (hF : ∀ p∈P,∀ u∈U p,0≤F (u,p)) :
    (∑ i∈S,F i)≤∑ p∈P,∑ u∈U p,F (u,p) := by
  classical
  have he : (∑ p∈P,∑ i∈S.filter (fun i=>i.2=p),F i)=∑ i∈S,F i := by
    rw [sum_fiberwise_eq_sum_filter]
    congr 1
    exact filter_eq_self.mpr (fun i hi=>(hcover i hi).1)
  rw [←he]
  apply sum_le_sum
  intro p hp
  let S' := S.filter (fun i=>i.2=p)
  have hsub : S'.image Prod.fst⊆U p := by
    intro u hu
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hu
    obtain ⟨hiS,hip⟩ := mem_filter.mp hi
    simpa only [hip] using (hcover i hiS).2
  have hinj : Set.InjOn (Prod.fst : ℕ×ℕ→ℕ) (↑S') := by
    intro i hi j hj heq
    have hip := (mem_filter.mp hi).2
    have hjp := (mem_filter.mp hj).2
    exact Prod.ext heq (hip.trans hjp.symm)
  have hid : (∑ i∈S',F i)=∑ u∈S'.image Prod.fst,F (u,p) := by
    rw [sum_image hinj]
    apply sum_congr rfl
    intro i hi
    have hip := (mem_filter.mp hi).2
    rw [←hip]
  exact hid.trans_le (sum_le_sum_of_subset_of_nonneg hsub (fun u hu _=>hF p hp u hu))

noncomputable def goldbachWeightedRectanglePrimes (N : ℕ) (z : ℝ) : Finset ℕ := by
  classical
  exact (range (N+1)).filter (fun p=>p.Prime ∧ p%4=3 ∧ z≤(p:ℝ))

noncomputable def goldbachWeightedRectangleU (N p : ℕ) : Finset ℕ :=
  Icc 1 ⌊(N:ℝ)^2/(2*(p:ℝ)^2)⌋₊

theorem goldbach_weighted_pair_rectangle (N : ℕ) (z : ℝ) (i : ℕ×ℕ)
    (hi : i∈goldbachWeightedPairs N z) :
    i.2∈goldbachWeightedRectanglePrimes N z ∧ i.1∈goldbachWeightedRectangleU N i.2 := by
  classical
  obtain ⟨hu,_,hp,hp4,hpz,hpB,_⟩ := (mem_goldbach_weighted_pairs N z i).mp hi
  have huR : (1:ℝ)≤ i.1 := by exact_mod_cast hu
  have hpR : (0:ℝ)< i.2 := by exact_mod_cast hp.pos
  have hN0 : (0:ℝ)≤N := Nat.cast_nonneg _
  have hsq := (Real.lt_sqrt hpR.le).mp hpB
  have hsize : 2*(i.1:ℝ)*(i.2:ℝ)^2<(N:ℝ)^2 := by
    have hh := (lt_div_iff₀ (show 0<2*(i.1:ℝ) by positivity)).mp hsq
    nlinarith only [hh]
  have hpN : (i.2:ℝ)<N := by
    by_contra h
    have hNp : (N:ℝ)≤ i.2 := le_of_not_gt h
    have hs : (N:ℝ)^2≤(i.2:ℝ)^2 := pow_le_pow_left₀ hN0 hNp 2
    have hm := mul_le_mul_of_nonneg_right huR (sq_nonneg (i.2:ℝ))
    nlinarith only [hsize,hs,hm,sq_nonneg (i.2:ℝ)]
  have hpNN : i.2≤N := by exact_mod_cast hpN.le
  have hupper : (i.1:ℝ)≤(N:ℝ)^2/(2*(i.2:ℝ)^2) := by
    apply (le_div_iff₀ (show 0<2*(i.2:ℝ)^2 by positivity)).mpr
    nlinarith only [hsize]
  refine ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),hp,hp4,hpz⟩,mem_Icc.mpr ⟨by omega,?_⟩⟩
  exact (Nat.le_floor_iff (by positivity : (0:ℝ)≤(N:ℝ)^2/(2*(i.2:ℝ)^2))).mpr hupper

theorem goldbach_weighted_kernel_rectangle (R z : ℝ) (N : ℕ) (n : ℤ) :
    (∑ i∈goldbachWeightedPairs N z,
      goldbachWeightedMultiplicative R n i.1/
        (((2*i.1*i.2:ℕ):ℝ)*(Real.log ((N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ)))^2))≤
      (1/2:ℝ)*∑ p∈goldbachWeightedRectanglePrimes N z,(1/(p:ℝ))*
        ∑ u∈goldbachWeightedRectangleU N p,
          goldbachWeightedMultiplicative R n u/
            ((u:ℝ)*(Real.log ((N:ℝ)^2/(2*(u:ℝ)*(p:ℝ))))^2) := by
  have hh := goldbach_finite_fiber_upper (goldbachWeightedPairs N z)
    (goldbachWeightedRectanglePrimes N z) (goldbachWeightedRectangleU N)
    (fun i=>goldbachWeightedMultiplicative R n i.1/
      (((2*i.1*i.2:ℕ):ℝ)*(Real.log ((N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ)))^2))
    (fun i hi=>goldbach_weighted_pair_rectangle N z i hi)
    (fun p _ u _=>div_nonneg (goldbach_weighted_multiplicative_nonneg R n u)
      (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
  apply hh.trans_eq
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [mul_sum,mul_sum]
  apply sum_congr rfl
  intro u hu
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end PrimeSquares
