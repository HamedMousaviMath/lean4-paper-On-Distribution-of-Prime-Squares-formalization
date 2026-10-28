import PrimeSquares.GoldbachSectionNineReduction
import PrimeSquares.LogPowerAbsorption

set_option autoImplicit false
open Filter Finset
namespace PrimeSquares

/-- The small-n cutoff and arithmetic divisor error are eventually harmless,
uniformly for every n in the square range. -/
theorem goldbach_eventual_arithmetic_budgets (A C : ℝ) {κ : ℝ} (hκ : 0<κ) :
    ∃ N₀ : ℕ,2≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      1≤Real.log N ∧ 13≤(N:ℝ)^2*(Real.log N)^(-A) ∧
      ∀ n : ℕ,2≤n → n≤N^2 →
        2*((n-1).primeFactors.card:ℝ)≤κ*(N:ℝ)*(Real.log N)^(-C) := by
  obtain ⟨D,hD,herr⟩ := goldbach_prime_divisor_power_error (by norm_num : (0:ℝ)<1/2)
  have hA := (isLittleO_log_rpow_rpow_atTop A (by norm_num : (0:ℝ)<2)).bound
    (by norm_num : (0:ℝ)<1/13)
  have hC := (isLittleO_log_rpow_rpow_atTop C (by norm_num : (0:ℝ)<1/2)).bound
    (div_pos hκ (by positivity : 0<2*D))
  have hevent : ∀ᶠ x : ℝ in atTop,
      1≤Real.log x ∧ 13≤x^2*(Real.log x)^(-A) ∧
        2*D*x^(1/2:ℝ)≤κ*x*(Real.log x)^(-C) := by
    filter_upwards [eventually_ge_atTop (Real.exp 1),hA,hC] with x hx ha hc
    have hx0 : 0<x := (Real.exp_pos 1).trans_le hx
    have hx1 : 1≤x := (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hx
    have hl1 : 1≤Real.log x := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
    have hl0 : 0<Real.log x := by linarith
    have ha' : (Real.log x)^A≤(1/13:ℝ)*x^2 := by
      simpa only [Real.norm_eq_abs,Real.rpow_two,abs_of_nonneg (Real.rpow_nonneg hl0.le _),
        abs_of_nonneg (sq_nonneg x)] using ha
    have hc' : (Real.log x)^C≤(κ/(2*D))*x^(1/2:ℝ) := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hl0.le _),
        abs_of_nonneg (Real.rpow_nonneg hx0.le _)] using hc
    refine ⟨hl1,?_,?_⟩
    · have hb : (13:ℝ)*(Real.log x)^A≤x^2 := by nlinarith only [ha']
      have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hl0 A)).mpr hb
      simpa only [div_eq_mul_inv,Real.rpow_neg hl0.le] using hh
    · have hb := mul_le_mul_of_nonneg_left hc' (show 0≤2*D*x^(1/2:ℝ) by positivity)
      have hp : (x^(1/2:ℝ))^2=x := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hx0.le]
        norm_num
      have he : (2*D*x^(1/2:ℝ))*((κ/(2*D))*x^(1/2:ℝ))=κ*x := by
        calc
          _=κ*(x^(1/2:ℝ))^2 := by field_simp [hD.ne']
          _=_ := by rw [hp]
      have hm := hb.trans_eq he
      have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hl0 C)).mpr hm
      simpa only [div_eq_mul_inv,Real.rpow_neg hl0.le] using hh
  have hnEvent := (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop).eventually hevent
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp hnEvent
  refine ⟨max N₁ 2,le_max_right _ _,?_⟩
  intro N hN
  obtain ⟨hl,hcut,hbudget⟩ := hN₁ N ((le_max_left _ _).trans hN)
  refine ⟨hl,hcut,?_⟩
  intro n hn hsize
  have hh := herr N n (by omega) hn (by omega)
  have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤2)
  exact hh'.trans (by simpa only [mul_assoc] using hbudget)

/-- Only the internal analytic and sieve estimates remain in this final reduction;
the small-n and prime-divisor bookkeeping have been discharged. -/
theorem goldbach_section9_eventual_count_reduction (H : PrimitiveTwoSquaresCriterion)
    (A C : ℝ) {κ : ℝ} (hκ : 0<κ) :
    ∃ N₀ : ℕ,2≤N₀ ∧ ∀ N : ℕ,N₀≤N → ∀ α : ℝ,1<α → α<2 →
      ∀ (M a b E₁ E₂ : ℕ→ℝ) (B t : ℝ),0≤B →
      κ*(N:ℝ)*(Real.log N)^(-C)≤t →
      (∀ n∈goldbachLargeNumbers N ((N:ℝ)^2*(Real.log N)^(-A)),
        a n*M n+E₁ n≤((goldbachSiftedValues n ((N:ℝ)^(1/α))).card:ℝ)) →
      (∀ n∈goldbachLargeNumbers N ((N:ℝ)^2*(Real.log N)^(-A)),
        (goldbachUpperSieveSum n N ((N:ℝ)^(1/α)):ℝ)≤b n*M n+E₂ n) →
      (∀ n∈goldbachLargeNumbers N ((N:ℝ)^2*(Real.log N)^(-A)),2*t≤(a n-b n)*M n) →
      ((∑ n∈goldbachLargeNumbers N ((N:ℝ)^2*(Real.log N)^(-A)),(E₁ n)^2)+
        (∑ n∈goldbachLargeNumbers N ((N:ℝ)^2*(Real.log N)^(-A)),(E₂ n)^2)≤
          B*(N:ℝ)^4*(Real.log N)^(-(A+2*C+10))) →
      ((goldbachExceptionalSet (goldbachAdmissibleNumbers N)).card:ℝ)≤
        (2*B/κ^2+2)*(N:ℝ)^2*(Real.log N)^(-A) := by
  obtain ⟨N₀,hN₀,hbudget⟩ := goldbach_eventual_arithmetic_budgets A C hκ
  refine ⟨N₀,hN₀,?_⟩
  intro N hN α hα1 hα2 M a b E₁ E₂ B t hB ht hlower hupper hgap hsum
  obtain ⟨hl,hcut,herror⟩ := hbudget N hN
  apply goldbach_section9_count_reduction H (hN₀.trans hN) hα1 hα2 M a b E₁ E₂ hκ hB hl hcut ht
    hlower hupper hgap ?_ hsum
  intro n hn
  obtain ⟨hnlarge,_,hnsize⟩ := goldbachLargeNumbers_range hcut n hn
  exact (herror n (by omega) hnsize.le).trans ht

end PrimeSquares
