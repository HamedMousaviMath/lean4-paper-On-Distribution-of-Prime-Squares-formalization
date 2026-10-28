import PrimeSquares.GoldbachWeightedFiniteIntegration
import PrimeSquares.GoldbachWeightedGeometry

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_weighted_pair_levels (N : ℕ) (hN : 2≤N) (R : ℝ)
    (hRN : R<(N:ℝ)^(2/9:ℝ)) (i : ℕ×ℕ)
    (hi : i∈goldbachWeightedPairs N ((N:ℝ)^(8/9:ℝ))) :
    0<2*i.1*i.2 ∧ R<goldbachUpperSieveLevel N (2*i.1*i.2) ∧
      (i.1:ℝ)<goldbachUpperSieveLevel N (2*i.1*i.2) ∧
      goldbachUpperSieveLevel N (2*i.1*i.2)<(i.2:ℝ) ∧
      2≤(N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ) := by
  have hv := (mem_goldbach_weighted_pairs N ((N:ℝ)^(8/9:ℝ)) i).mp hi
  have hclosed := mem_goldbachClosedLSet.mpr (goldbach_weighted_pair_multiplier N _ i hv)
  obtain ⟨u',p',_,_,_,_,_,_,_,hlow,hupp,_⟩ := goldbach_weighted_multiplier_geometry hN hclosed
  obtain ⟨hu,huB,hp,hp4,hpz,hpB,hU⟩ := hv
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hu0 : (0:ℝ)< i.1 := by exact_mod_cast hu
  have hp0 : (0:ℝ)< i.2 := by exact_mod_cast hp.pos
  have hℓ : 0<2*i.1*i.2 := mul_pos (mul_pos (by norm_num) hu) hp.pos
  have hℓR : (0:ℝ)<(2*i.1*i.2:ℕ) := by exact_mod_cast hℓ
  have hz0 : 0<(N:ℝ)^(8/9:ℝ) := Real.rpow_pos_of_pos hN0 _
  have hpow : ((N:ℝ)^(8/9:ℝ))^2*(N:ℝ)^(2/9:ℝ)=(N:ℝ)^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN0.le,←Real.rpow_add hN0]
    norm_num
  have huPow : (i.1:ℝ)<(N:ℝ)^(2/9:ℝ) := by
    apply huB.trans_le
    apply (div_le_iff₀ (show 0<2*((N:ℝ)^(8/9:ℝ))^2 by positivity)).mpr
    nlinarith only [hpow,sq_nonneg (N:ℝ)]
  have hsq := (Real.lt_sqrt hp0.le).mp hpB
  have hsize : 2*(i.1:ℝ)*(i.2:ℝ)^2<(N:ℝ)^2 := by
    have hh := (lt_div_iff₀ (show 0<2*(i.1:ℝ) by positivity)).mp hsq
    nlinarith only [hh]
  have hratio : (i.2:ℝ)<(N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ) := by
    apply (lt_div_iff₀ hℓR).mpr
    push_cast
    nlinarith only [hsize]
  have hp2 : (2:ℝ)≤ i.2 := by exact_mod_cast hp.two_le
  exact ⟨hℓ,hRN.trans hlow,huPow.trans hlow,hupp.trans_le hpz,hp2.trans hratio.le⟩

theorem goldbach_weighted_main_term_sum_normalization (ψ : SchwartzMap ℝ ℝ)
    (N n : ℕ) (hN : 2≤N) (R : ℝ) (hR : 3≤R) (hRN : R<(N:ℝ)^(2/9:ℝ))
    (hn : ((n:ℤ):ZMod 24)=12) :
    (∑ ℓ∈goldbachClosedLSet N ((N:ℝ)^(8/9:ℝ)),
      goldbachUpperMainTerm ψ N R ℓ n*goldbachUpperTheta R (goldbachUpperSieveLevel N ℓ) ℓ n)=
      6*goldbachWeightedB R n*
        ∑ i∈goldbachWeightedPairs N ((N:ℝ)^(8/9:ℝ)),
          (goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ))*
            goldbachWeightedOuterProduct R (goldbachUpperSieveLevel N (2*i.1*i.2)) 0*
            (goldbachSingularIntegral ψ N (2*i.1*i.2) R ((n:ℝ)-1) (N:ℝ) ((N:ℝ)^2)).re := by
  classical
  rw [goldbach_weighted_pairs_sum,mul_sum]
  apply sum_congr rfl
  intro i hi
  obtain ⟨hu,_,hp,_,_,_,hU⟩ := (mem_goldbach_weighted_pairs N ((N:ℝ)^(8/9:ℝ)) i).mp hi
  obtain ⟨_,hRz,huz,hzp,_⟩ := goldbach_weighted_pair_levels N hN R hRN i hi
  have he := goldbach_weighted_upper_normalization ψ N n R
    (goldbachUpperSieveLevel N (2*i.1*i.2)) hR hRz i.1 i.2 hu huz hp hzp.le hU hn
  rw [he]
  ring

theorem goldbach_weighted_main_term_smoothing (ψ : SchwartzMap ℝ ℝ) (hψ : ψ≠0) :
    ∃ K : ℝ,0<K ∧ ∀ N n : ℕ,2≤N→n<N^2→∀ R : ℝ,3≤R→R<(N:ℝ)^(2/9:ℝ)→
      ((n:ℤ):ZMod 24)=12→
      (∑ ℓ∈goldbachClosedLSet N ((N:ℝ)^(8/9:ℝ)),
        goldbachUpperMainTerm ψ N R ℓ n*goldbachUpperTheta R (goldbachUpperSieveLevel N ℓ) ℓ n)≤
        6*goldbachWeightedB R n*
          (∑ i∈goldbachWeightedPairs N ((N:ℝ)^(8/9:ℝ)),
            (goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ))*
              goldbachWeightedOuterProduct R (goldbachUpperSieveLevel N (2*i.1*i.2)) 0*
              (goldbachArchimedeanIntegral (2*i.1*i.2) ((n:ℝ)-1) (N:ℝ) ((N:ℝ)^2)).re)+
        (6*goldbachWeightedB R n)*(K*(N:ℝ)/Real.sqrt R)*
          ∑ i∈goldbachWeightedPairs N ((N:ℝ)^(8/9:ℝ)),
            goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ) := by
  obtain ⟨K,hK,hSmooth⟩ := goldbach_positive_singular_integral_complete ψ hψ
  refine ⟨K,hK,?_⟩
  intro N n hN hnN R hR hRN hn
  let I := goldbachWeightedPairs N ((N:ℝ)^(8/9:ℝ))
  let w := fun i : ℕ×ℕ=>goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ)
  let V := fun i : ℕ×ℕ=>goldbachWeightedOuterProduct R (goldbachUpperSieveLevel N (2*i.1*i.2)) 0
  let F := fun i : ℕ×ℕ=>goldbachSingularIntegral ψ N (2*i.1*i.2) R ((n:ℝ)-1) (N:ℝ) ((N:ℝ)^2)
  let G := fun i : ℕ×ℕ=>goldbachArchimedeanIntegral (2*i.1*i.2) ((n:ℝ)-1) (N:ℝ) ((N:ℝ)^2)
  have hE : ∀ i∈I,‖F i-G i‖≤K*(N:ℝ)/Real.sqrt R := by
    intro i hi
    have hℓ := (goldbach_weighted_pair_levels N hN R hRN i hi).1
    have hNr : (2:ℝ)≤N := by exact_mod_cast hN
    have hnR : (n:ℝ)<(N:ℝ)^2 := by exact_mod_cast hnN
    exact (hSmooth N (2*i.1*i.2) (by omega) hℓ R N ((N:ℝ)^2) ((n:ℝ)-1)
      (by linarith) hNr le_rfl (by nlinarith) (by linarith)).2.2
  have hw : ∀ i∈I,0≤w i := fun i _=>div_nonneg
    (goldbach_weighted_multiplicative_nonneg R n i.1) (Nat.cast_nonneg _)
  have hV : ∀ i∈I,0≤V i ∧ V i≤1 := fun i _=>
    ⟨(goldbach_weighted_outer_product_positive R _ 0).le,goldbach_weighted_outer_product_le_one R _ 0⟩
  have hs := goldbach_finite_smoothing_outer_upper I w V F G (K*(N:ℝ)/Real.sqrt R) hw hV
    (by positivity) hE
  have hB : 0≤6*goldbachWeightedB R n := mul_nonneg (by norm_num)
    (goldbach_weighted_B_positive R (by linarith) n).le
  have hh := mul_le_mul_of_nonneg_left hs hB
  rw [goldbach_weighted_main_term_sum_normalization ψ N n hN R hR hRN hn]
  convert hh using 1; ring

end PrimeSquares
