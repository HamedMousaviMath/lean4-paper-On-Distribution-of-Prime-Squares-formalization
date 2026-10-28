import PrimeSquares.GoldbachUpperPresieveApplication
import PrimeSquares.GoldbachLowerCutoffFreedom

set_option autoImplicit false
open Finset Filter
open scoped SchwartzMap
namespace PrimeSquares

def GoldbachSieveCircleBoundAt (ψ : SchwartzMap ℝ ℝ) (N : ℕ) (B R M A : ℝ) : Prop :=
  ∀ I : Finset (ℕ×ℕ),I⊆goldbachCoefficientIndices ((N:ℝ)^(6/5:ℝ))
      (fun ℓ : ℕ=>Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B))→
    ∀ a : ℕ×ℕ→ℕ,(∀ i∈I,(a i).Coprime i.2)→
    ∀ d : ℕ×ℕ→ℂ,(∀ i∈I,‖d i‖≤1)→
      (∑ n∈range (N^2),‖∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) R n‖^2)≤
        M*(N:ℝ)^4*(Real.log N)^(-A) ∧
      (∑ n∈range (N^2),‖∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) R (n-1)‖^2)≤
        (2*M)*(N:ℝ)^4*(Real.log N)^(-A)

theorem goldbach_sieve_circle_bound_exists_above (Cmin : ℝ)
    (HSW : RawPrimeSiegelWalfiszInput) (HBV : RawPrimeBombieriVinogradovInput)
    (Hminor : UniformRenGhoshInputs) (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x|→ψ x=0) {A : ℝ} (hA : 0<A) :
    ∃ B C M : ℝ,Cmin≤C ∧ 0≤B ∧ 0<C ∧ 0<M ∧ ∀ᶠ N : ℕ in atTop,
      4≤N ∧ GoldbachSieveCircleBoundAt ψ N B ((Real.log N)^C) M A := by
  obtain ⟨B,C,M,hCmin,hB,hC,hM,N₀,hN₀,hCircle⟩ :=
    goldbach_sieve_remainders_selected_above Cmin HSW HBV Hminor ψ hψ hsψ hA (by norm_num : (0:ℝ)<3/4)
  refine ⟨B,C,M,hCmin,hB,hC,hM,?_⟩
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hN4 : 4≤N := hN₀.trans hN
  refine ⟨hN4,?_⟩
  intro I hI a ha d hd
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hL : (N:ℝ)^(6/5:ℝ)<(N:ℝ)^(2-(3/4:ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_lt hNr (by norm_num)
  have hh := hCircle N hN B ((N:ℝ)^(6/5:ℝ)) le_rfl hL
    (fun ℓ : ℕ=>Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) (fun _ _ _=>le_rfl)
      I hI a ha d hd
  exact ⟨hh.1,hh.2.1⟩

theorem goldbach_upper_remainder_from_circle (ψ : SchwartzMap ℝ ℝ) (N : ℕ) (hN : 4≤N)
    (B R M A : ℝ) (hCircle : GoldbachSieveCircleBoundAt ψ N B R M A)
    (c : ℕ→ℕ→ℝ) (hc : ∀ ℓ d : ℕ,|c ℓ d|≤1) :
    (∑ n∈range (N^2),(goldbachUpperRemainderSum ψ N B R c n)^2)≤
      (2*M)*(N:ℝ)^4*(Real.log N)^(-A) := by
  classical
  let L := goldbachClosedLSet N ((N:ℝ)^(8/9:ℝ))
  let T := L.sigma (fun ℓ=>((range (Nat.ceil (goldbachUpperDivisorLevel B N ℓ))).filter (fun d=>0<d)))
  let I := T.image (fun i : Sigma (fun _ : ℕ=>ℕ)=>(i.1,12*i.2))
  let a := fun i : ℕ×ℕ=>goldbachUpperSieveResidue i.1 (i.2/12)
  let u := fun i : ℕ×ℕ=>(c i.1 (i.2/12):ℂ)
  have hdiv (d : ℕ) : 12*d/12=d := by omega
  have hinj : Set.InjOn (fun i : Sigma (fun _ : ℕ=>ℕ)=>(i.1,12*i.2)) (↑T:Set (Sigma (fun _ : ℕ=>ℕ))) := by
    intro i _ j _ he
    have hfst := congrArg Prod.fst he
    have hsnd := congrArg Prod.snd he
    have hsnd' : i.2=j.2 := Nat.eq_of_mul_eq_mul_left (by decide : 0<12) hsnd
    exact Sigma.ext hfst (heq_of_eq hsnd')
  have hN0 : (0:ℝ)≤N := Nat.cast_nonneg _
  have hlog : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hpow := Real.rpow_pos_of_pos hlog B
  have hI : I⊆goldbachCoefficientIndices ((N:ℝ)^(6/5:ℝ))
      (fun ℓ : ℕ=>Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    obtain ⟨hℓ,hd⟩ := mem_sigma.mp hj
    obtain ⟨hd,hpos⟩ := mem_filter.mp hd
    have hlev : (j.2:ℝ)<goldbachUpperDivisorLevel B N j.1 := Nat.lt_ceil.mp (mem_range.mp hd)
    have hℓpos := goldbach_closed_multiplier_positive hℓ
    obtain ⟨_,_,_,_,_,_,_,hℓB,_,_,_⟩ := goldbach_weighted_multiplier_geometry (by omega : 2≤N) hℓ
    have hNr : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
    have hℓlarge := hℓB.trans_le (Real.rpow_le_rpow_of_exponent_le hNr (by norm_num : (10/9:ℝ)≤6/5))
    apply (mem_goldbachCoefficientIndices _ _ j.1 (12*j.2)).mpr
    refine ⟨hℓpos,hℓlarge,Nat.mul_pos (by decide) hpos,?_⟩
    rw [Real.rpow_neg hlog.le]
    dsimp only [goldbachUpperDivisorLevel] at hlev
    have hh := (lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<12) hpow)).mp hlev
    push_cast
    apply (lt_div_iff₀ hpow).mpr
    simpa only [div_eq_mul_inv] using (show (12:ℝ)*(j.2:ℝ)*(Real.log N)^B<
      Real.sqrt ((N:ℝ)^2/j.1) by nlinarith only [hh])
  have ha : ∀ i∈I,(a i).Coprime i.2 := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := mem_image.mp hi
    simpa only [a,hdiv] using goldbach_upper_residue_coprime j.1 j.2
  have hu : ∀ i∈I,‖u i‖≤1 := by
    intro i _
    simpa only [u,Complex.norm_real,Real.norm_eq_abs] using hc i.1 (i.2/12)
  have hbound := (hCircle I hI a ha u hu).2
  have he (n : ℕ) : goldbachUpperRemainderSum ψ N B R c n=
      (∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) R (n-1)).re := by
    dsimp only [I]
    rw [sum_image hinj]
    simp only [u,a,hdiv,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero]
    rw [show T=L.sigma (fun ℓ=>((range (Nat.ceil (goldbachUpperDivisorLevel B N ℓ))).filter (fun d=>0<d))) from rfl,
      sum_sigma]
    rfl
  apply le_trans (sum_le_sum (fun n _=>?_)) hbound
  rw [he]
  have hh := Complex.abs_re_le_norm
    (∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) R (n-1))
  nlinarith only [hh,abs_nonneg ((∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) R (n-1)).re),
    norm_nonneg (∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) R (n-1)),
    sq_abs ((∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) R (n-1)).re)]

end PrimeSquares
