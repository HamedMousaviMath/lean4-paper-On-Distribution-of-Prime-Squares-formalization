import PrimeSquares.GoldbachLowerSieveBridge
import PrimeSquares.GoldbachLowerSieveParameters
import PrimeSquares.GoldbachSieveRemainderTransport

set_option autoImplicit false
open Finset
open scoped SchwartzMap
namespace PrimeSquares

noncomputable def goldbachLowerRemainderSum (ψ : 𝓢(ℝ,ℝ)) (N : ℕ) (B R : ℝ)
    (c : ℕ→ℝ) (n : ℕ) : ℝ :=
  ∑ d∈(range (Nat.ceil (goldbachLowerSieveLevel B N))).filter (fun d=>0<d),
    c d*(goldbachFullRemainder ψ N 1 (24*d) (goldbachLowerSieveResidue d) R n).re

theorem goldbach_lower_remainder_zero_extension (ψ : 𝓢(ℝ,ℝ)) (N : ℕ) (B R : ℝ)
    (c : ℕ→ℝ) (n : ℕ) :
    (∑ d∈range (Nat.ceil (goldbachLowerSieveLevel B N)),c d*
      (if d=0 then 0 else
        (goldbachFullRemainder ψ N 1 (24*d) (goldbachLowerSieveResidue d) R n).re))=
      goldbachLowerRemainderSum ψ N B R c n := by
  classical
  unfold goldbachLowerRemainderSum
  rw [sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases hd : d=0
  · simp [hd]
  · simp [hd,Nat.pos_of_ne_zero hd]

theorem goldbach_lower_remainder_mean_square
    (HSW : RawPrimeSiegelWalfiszInput) (HBV : RawPrimeBombieriVinogradovInput)
    (Hminor : UniformRenGhoshInputs) (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x|→ψ x=0) {A : ℝ} (hA : 0<A) :
    ∃ B₀ C K : ℝ,0≤B₀ ∧ 0<C ∧ 0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧
      ∀ N : ℕ,N₀≤N→∀ B : ℝ,B₀≤B→∀ c : ℕ→ℝ,(∀ d : ℕ,|c d|≤1)→
        (∑ n∈range (N^2),(goldbachLowerRemainderSum ψ N B ((Real.log N)^C) c n)^2)≤
          K*(N:ℝ)^4*(Real.log N)^(-A) := by
  classical
  obtain ⟨B₀,C,K,hB₀,hC,hK,N₀,hN₀,hCircle⟩ :=
    goldbach_sieve_remainders_selected HSW HBV Hminor ψ hψ hsψ hA (by norm_num : (0:ℝ)<1/2)
  refine ⟨B₀,C,K,hB₀,hC,hK,N₀,hN₀,?_⟩
  intro N hN B hB c hc
  have hN4 : (4:ℝ)≤N := by exact_mod_cast hN₀.trans hN
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
  have hI : I⊆goldbachCoefficientIndices 2 V := by
    intro i hi
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hi
    obtain ⟨hd,hpos⟩ := mem_filter.mp hd
    have hlev : (d:ℝ)<goldbachLowerSieveLevel B N := Nat.lt_ceil.mp (mem_range.mp hd)
    apply (mem_goldbachCoefficientIndices 2 V 1 (24*d)).mpr
    refine ⟨by decide,by norm_num,Nat.mul_pos (by decide) hpos,?_⟩
    dsimp only [V]
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
  have hL : (2:ℝ)<(N:ℝ)^(2-(1/2:ℝ)) := by
    have hh : (N:ℝ)≤(N:ℝ)^(2-(1/2:ℝ)) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤N) (by norm_num : (1:ℝ)≤2-1/2)
    linarith
  have hbound := (hCircle N hN B 2 hB hL V (fun _ _ _=>le_rfl) I hI a ha u hu).1
  have he (n : ℕ) : goldbachLowerRemainderSum ψ N B ((Real.log N)^C) c n=
      (∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n).re := by
    dsimp only [I]
    rw [sum_image hinj]
    simp only [u,a,hdiv,Complex.re_sum,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rfl
  apply le_trans (sum_le_sum (fun n _=>?_)) hbound
  rw [he]
  have hh := Complex.abs_re_le_norm
    (∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n)
  nlinarith only [hh,abs_nonneg
    ((∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n).re),
    norm_nonneg (∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n),sq_abs
      ((∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n).re)]

end PrimeSquares
