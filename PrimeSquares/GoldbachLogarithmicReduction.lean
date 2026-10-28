import PrimeSquares.GoldbachExceptionalSetReduction

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem logarithmic_square_threshold_bound {X L κ A C K B t k : ℝ}
    (hX : 0<X) (hL : 1≤L) (hκ : 0<κ) (hB : 0≤B) (hk : 0≤k)
    (hK : A+2*C≤K) (ht : κ*X*L^(-C)≤t)
    (hcount : k*t^2≤2*B*X^4*L^(-K)) :
    k≤(2*B/κ^2)*X^2*L^(-A) := by
  have hL0 : 0<L := by linarith
  have hw : 0<κ*X*L^(-C) := by positivity
  have hs := pow_le_pow_left₀ hw.le ht 2
  have hbound := (mul_le_mul_of_nonneg_left hs hk).trans hcount
  have hdiv : k≤2*B*X^4*L^(-K)/(κ*X*L^(-C))^2 :=
    (le_div_iff₀ (sq_pos_of_pos hw)).mpr hbound
  have hp : (L^(-C))^2=L^(-2*C) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hL0.le]
    congr 1
    ring
  have hfrac : L^(-K)/(L^(-C))^2=L^(-K+2*C) := by
    rw [hp,←Real.rpow_sub hL0]
    congr 1
    ring
  have he : 2*B*X^4*L^(-K)/(κ*X*L^(-C))^2=
      (2*B/κ^2)*X^2*L^(-K+2*C) := by
    calc
      _=(2*B/κ^2)*X^2*(L^(-K)/(L^(-C))^2) := by
        field_simp [hκ.ne',hX.ne',(Real.rpow_pos_of_pos hL0 (-C)).ne']
      _=_ := by rw [hfrac]
  refine hdiv.trans (he.le.trans ?_)
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hL (by linarith))
  positivity

/-- The final logarithmic saving is deduced from the paper's internal estimates;
these hypotheses are not added to the independent analytic input registry. -/
theorem goldbach_logarithmic_exceptional_bound (H : PrimitiveTwoSquaresCriterion)
    {N : ℕ} (hN : 2≤N) {α : ℝ} (hα1 : 1<α) (hα2 : α<2)
    (F : Finset ℕ) (hF : ∀ n∈F,12<n ∧ n%24=12 ∧ n<N^2)
    (M a b E₁ E₂ : ℕ→ℝ) {t κ A C K B : ℝ}
    (hκ : 0<κ) (hB : 0≤B) (hlog : 1≤Real.log N) (hK : A+2*C≤K)
    (ht : κ*(N:ℝ)*(Real.log N)^(-C)≤t)
    (hlower : ∀ n∈F,a n*M n+E₁ n≤((goldbachSiftedValues n ((N:ℝ)^(1/α))).card:ℝ))
    (hupper : ∀ n∈F,(goldbachUpperSieveSum n N ((N:ℝ)^(1/α)):ℝ)≤b n*M n+E₂ n)
    (hgap : ∀ n∈F,2*t≤(a n-b n)*M n)
    (hsmall : ∀ n∈F,2*((n-1).primeFactors.card:ℝ)≤t)
    (hsum : (∑ n∈F,(E₁ n)^2)+(∑ n∈F,(E₂ n)^2)≤B*(N:ℝ)^4*(Real.log N)^(-K)) :
    ((goldbachExceptionalSet F).card:ℝ)≤(2*B/κ^2)*(N:ℝ)^2*(Real.log N)^(-A) := by
  have hNR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hl0 : 0<Real.log N := by linarith
  have ht0 : 0<t := (show 0<κ*(N:ℝ)*(Real.log N)^(-C) by positivity).trans_le ht
  have hh := goldbach_exceptional_square_sum H hN hα1 hα2 F hF M a b E₁ E₂ ht0 hlower hupper hgap hsmall
  have hc : ((goldbachExceptionalSet F).card:ℝ)*t^2≤2*B*(N:ℝ)^4*(Real.log N)^(-K) := by
    have hm := mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ)≤2)
    nlinarith only [hh,hm]
  exact logarithmic_square_threshold_bound hNR hlog hκ hB (Nat.cast_nonneg _) hK ht hc

end PrimeSquares
