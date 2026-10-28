import PrimeSquares.GoldbachUpperSieveRemainder

set_option autoImplicit false
open Finset Filter
open scoped SchwartzMap
namespace PrimeSquares

theorem goldbach_lower_remainder_from_circle (ψ : 𝓢(ℝ,ℝ)) (N : ℕ) (hN : 4≤N)
    (B R K A : ℝ) (hCircle : GoldbachSieveCircleBoundAt ψ N B R K A)
    (c : ℕ→ℝ) (hc : ∀ d : ℕ,|c d|≤1) :
    (∑ n∈range (N^2),(goldbachLowerRemainderSum ψ N B R c n)^2)≤
      K*(N:ℝ)^4*(Real.log N)^(-A) := by
  classical
  have hN4 : (4:ℝ)≤N := by exact_mod_cast hN
  have hN0 : (0:ℝ)≤N := Nat.cast_nonneg _
  have hlog : 0<Real.log N := Real.log_pos (by linarith)
  have hpow := Real.rpow_pos_of_pos hlog B
  let T := (range (Nat.ceil (goldbachLowerSieveLevel B N))).filter (fun d=>0<d)
  let I := T.image (fun d : ℕ=>(1,24*d))
  let V := fun ℓ : ℕ=>Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)
  let a := fun i : ℕ×ℕ=>goldbachLowerSieveResidue (i.2/24)
  let u := fun i : ℕ×ℕ=>(c (i.2/24):ℂ)
  have hdiv (d : ℕ) : 24*d/24=d := by omega
  have hinj : Set.InjOn (fun d : ℕ=>(1,24*d)) (↑T:Set ℕ) := by
    intro d _ e _ he
    have hh := congrArg Prod.snd he
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0<24) hh
  have hI : I⊆goldbachCoefficientIndices ((N:ℝ)^(6/5:ℝ)) V := by
    intro i hi
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hi
    obtain ⟨hd,hpos⟩ := mem_filter.mp hd
    have hlev : (d:ℝ)<goldbachLowerSieveLevel B N := Nat.lt_ceil.mp (mem_range.mp hd)
    apply (mem_goldbachCoefficientIndices ((N:ℝ)^(6/5:ℝ)) V 1 (24*d)).mpr
    refine ⟨by decide,?_,Nat.mul_pos (by decide) hpos,?_⟩
    · simpa only [Nat.cast_one] using Real.one_lt_rpow (show (1:ℝ)<N by linarith) (show (0:ℝ)<6/5 by norm_num)
    · dsimp only [V]
      rw [Nat.cast_one,div_one,Real.sqrt_sq hN0,Real.rpow_neg hlog.le]
      dsimp only [goldbachLowerSieveLevel] at hlev
      have h := (lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<24) hpow)).mp hlev
      push_cast
      apply (lt_div_iff₀ hpow).mpr
      simpa only [div_eq_mul_inv] using (show (24:ℝ)*(d:ℝ)*(Real.log N)^B<N by nlinarith only [h])
  have ha : ∀ i∈I,(a i).Coprime i.2 := by
    intro i hi
    obtain ⟨d,_,rfl⟩ := mem_image.mp hi
    simpa only [a,hdiv] using goldbach_lower_residue_coprime d
  have hu : ∀ i∈I,‖u i‖≤1 := by
    intro i _
    simpa only [u,Complex.norm_real,Real.norm_eq_abs] using hc (i.2/24)
  have hbound := (hCircle I hI a ha u hu).1
  have he (n : ℕ) : goldbachLowerRemainderSum ψ N B R c n=
      (∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) R n).re := by
    dsimp only [I]
    rw [sum_image hinj]
    simp only [u,a,hdiv,Complex.re_sum,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rfl
  apply le_trans (sum_le_sum (fun n _=>?_)) hbound
  rw [he]
  have hh := Complex.abs_re_le_norm
    (∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) R n)
  nlinarith only [hh,abs_nonneg
    ((∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) R n).re),
    norm_nonneg (∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) R n),sq_abs
      ((∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) R n).re)]

end PrimeSquares
