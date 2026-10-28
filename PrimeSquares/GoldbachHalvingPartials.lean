import PrimeSquares.GoldbachPrimeUnweighting
import PrimeSquares.CorrectedPrimeSquareInput

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_halving_partial_bound (F : ℕ→ℂ) (N : ℕ) {H B E : ℝ}
    (hH : 0≤H) (hB : 0≤B)
    (hsmall : ∀ m : ℕ,m≤N → (m:ℝ)≤H → ‖F m‖≤E)
    (hstep : ∀ m : ℕ,m≤N → H<(m:ℝ) → ‖F m-F (m/2)‖≤B*(m:ℝ)) :
    ∀ m : ℕ,m≤N → ‖F m‖≤2*B*(m:ℝ)+E := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases hms : (m:ℝ)≤H
    · exact (hsmall m hm hms).trans (by nlinarith [mul_nonneg hB (Nat.cast_nonneg m: (0:ℝ)≤m)])
    · have hmR : 0<(m:ℝ) := hH.trans_lt (lt_of_not_ge hms)
      have hmpos : 0<m := by exact_mod_cast hmR
      have hhalf : m/2<m := Nat.div_lt_self hmpos (by decide)
      have hih := ih (m/2) hhalf ((Nat.div_le_self m 2).trans hm)
      have ha := hstep m hm (lt_of_not_ge hms)
      have hsplit : F m=(F m-F (m/2))+F (m/2) := by ring
      have ht := (norm_add_le (F m-F (m/2)) (F (m/2))).trans (add_le_add ha hih)
      rw [←hsplit] at ht
      have hdiv : (2:ℝ)*(m/2:ℕ)≤(m:ℝ) := by exact_mod_cast Nat.mul_div_le m 2
      have hh := mul_le_mul_of_nonneg_left hdiv hB
      nlinarith only [ht,hh]

theorem goldbachMangoldtPrefix_halving (M : ℕ) (θ : PrimeCircle) :
    goldbachMangoldtPrefix M θ=goldbachMangoldtPrefix (M/2) θ+
      ∑ n∈Ioc (M/2) M,(ArithmeticFunction.vonMangoldt n:ℂ)*fourier ((n^2:ℕ):ℤ) θ := by
  simp only [goldbachMangoldtPrefix_Ioc]
  exact (sum_Ioc_consecutive _ (Nat.zero_le (M/2)) (Nat.div_le_self M 2)).symm

theorem goldbach_positive_quadratic_character (n : ℕ) (ξ : ℝ) :
    fourier ((n^2:ℕ):ℤ) (ξ:PrimeCircle)=quadraticOscillation (-ξ) n := by
  rw [fourier_coe_apply,quadraticOscillation]
  congr 1
  push_cast
  ring

theorem goldbachMangoldtPrefix_annular_Ren (M : ℕ) (ξ : ℝ) :
    goldbachMangoldtPrefix M (ξ:PrimeCircle)-goldbachMangoldtPrefix (M/2) (ξ:PrimeCircle)=
      renQuadraticSum ((M:ℝ)/2) ξ := by
  rw [goldbachMangoldtPrefix_halving,add_sub_cancel_left,renQuadraticSum]
  have hf : ⌊(M:ℝ)/2⌋₊=M/2 := Nat.floor_div_eq_div M 2
  simp only [hf,show 2*((M:ℝ)/2)=(M:ℝ) by ring,Nat.floor_natCast]
  apply sum_congr rfl
  intro n _
  rw [goldbach_positive_quadratic_character]

theorem goldbachMangoldtPrefix_annular_norm (M : ℕ) (hM : 1≤M) (ξ : ℝ) :
    ‖goldbachMangoldtPrefix M (ξ:PrimeCircle)-goldbachMangoldtPrefix (M/2) (ξ:PrimeCircle)‖=
      (M:ℝ)*‖annularWeightedSquareAverageSymbol M ArithmeticFunction.vonMangoldt (ξ:PrimeCircle)‖ := by
  have hm : (M:ℝ)≠0 := by exact_mod_cast (show M≠0 by omega)
  rw [goldbachMangoldtPrefix_annular_Ren,annularMangoldtSymbol_norm_Ren,
    ←mul_assoc,mul_inv_cancel₀ hm,one_mul]

theorem goldbachMangoldtPrefix_crude (N M : ℕ) (hMN : M≤N) (θ : PrimeCircle) :
    ‖goldbachMangoldtPrefix M θ‖≤(M:ℝ)*Real.log N := by
  rw [goldbachMangoldtPrefix_Ioc]
  calc
    _≤∑ n∈Ioc 0 M,‖(ArithmeticFunction.vonMangoldt n:ℂ)*fourier ((n^2:ℕ):ℤ) θ‖ := norm_sum_le _ _
    _≤∑ _n∈Ioc 0 M,Real.log N := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        show ‖fourier ((n^2:ℕ):ℤ) θ‖=1 from Circle.norm_coe _,mul_one]
      exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log
        (by exact_mod_cast (mem_Ioc.mp hn).1) (by exact_mod_cast (mem_Ioc.mp hn).2.trans hMN))
    _=_ := by simp only [sum_const,nsmul_eq_mul,Nat.card_Ioc,Nat.sub_zero]

/-- The annular norm condition here is internal; later it is discharged from
the existing general Ren/Ghosh inputs on the rescaled complementary arcs. -/
theorem goldbach_mangoldt_partials_from_annular (N : ℕ) (hN : 1≤N) (ξ : ℝ)
    {H B : ℝ} (hH : 0≤H) (hB : 0≤B)
    (hann : ∀ m : ℕ,m≤N → H<(m:ℝ) →
      ‖annularWeightedSquareAverageSymbol m ArithmeticFunction.vonMangoldt (ξ:PrimeCircle)‖≤B) :
    ∀ m : ℕ,m≤N → ‖goldbachMangoldtPrefix m (ξ:PrimeCircle)‖≤2*B*(N:ℝ)+H*Real.log N := by
  have hl : 0≤Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hh := goldbach_halving_partial_bound (fun m => goldbachMangoldtPrefix m (ξ:PrimeCircle)) N hH hB
    (fun m hm hms => (goldbachMangoldtPrefix_crude N m hm _).trans
      (mul_le_mul_of_nonneg_right hms hl))
    (fun m hm hml => by
      have hmpos : 1≤m := by
        have hmr : (0:ℝ)<m := hH.trans_lt hml
        exact_mod_cast hmr
      rw [goldbachMangoldtPrefix_annular_norm m hmpos ξ]
      simpa only [mul_comm B (m:ℝ)] using
        mul_le_mul_of_nonneg_left (hann m hm hml) (Nat.cast_nonneg m))
  intro m hm
  exact (hh m hm).trans (add_le_add
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hm : (m:ℝ)≤N) (by positivity : 0≤2*B)) le_rfl)

end PrimeSquares
