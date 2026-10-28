import PrimeSquares.GoldbachFiniteAbel
import PrimeSquares.MangoldtNonunits

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_sum_range_succ_eq_Ioc {E : Type*} [AddCommMonoid E]
    (f : ℕ→E) (hf : f 0=0) (N : ℕ) :
    (∑ n∈range (N+1),f n)=∑ n∈Ioc 0 N,f n := by
  have hs : range (N+1)=insert 0 (Ioc 0 N) := by
    ext n
    simp only [mem_range,mem_insert,mem_Ioc]
    omega
  rw [hs,sum_insert (by simp),hf,zero_add]

noncomputable def goldbachMangoldtPrefix (M : ℕ) (θ : PrimeCircle) : ℂ :=
  ∑ n∈range (M+1),(ArithmeticFunction.vonMangoldt n:ℂ)*fourier ((n^2:ℕ):ℤ) θ

noncomputable def goldbachLogRemovedMangoldtPrefix (M : ℕ) (θ : PrimeCircle) : ℂ :=
  ∑ n∈range (M+1),goldbachLogRemovalWeight n •
    ((ArithmeticFunction.vonMangoldt n:ℂ)*fourier ((n^2:ℕ):ℤ) θ)

theorem goldbachMangoldtPrefix_Ioc (M : ℕ) (θ : PrimeCircle) :
    goldbachMangoldtPrefix M θ=
      ∑ n∈Ioc 0 M,(ArithmeticFunction.vonMangoldt n:ℂ)*fourier ((n^2:ℕ):ℤ) θ :=
  goldbach_sum_range_succ_eq_Ioc _ (by simp) M

theorem goldbach_log_removed_mangoldt_bound (M : ℕ) (θ : PrimeCircle) {B : ℝ}
    (hB : 0≤B) (hprefix : ∀ m : ℕ,m≤M → ‖goldbachMangoldtPrefix m θ‖≤B) :
    ‖goldbachLogRemovedMangoldtPrefix M θ‖≤B/Real.log 2 := by
  have hG (k : ℕ) (hk : k≤M+1) :
      ‖∑ n∈range k,(ArithmeticFunction.vonMangoldt n:ℂ)*fourier ((n^2:ℕ):ℤ) θ‖≤B := by
    by_cases hk0 : k=0
    · simpa only [hk0,range_zero,sum_empty,norm_zero] using hB
    · have hk1 : 1≤k := by omega
      simpa only [goldbachMangoldtPrefix,Nat.sub_add_cancel hk1] using
        hprefix (k-1) (by omega)
  simpa only [goldbachLogRemovedMangoldtPrefix,goldbachLogRemovalWeight_zero,
    div_eq_mul_inv,one_mul] using
    goldbach_finite_abel_bound goldbachLogRemovalWeight
      (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)*fourier ((n^2:ℕ):ℤ) θ)
      (M+1) hB goldbachLogRemovalWeight_nonneg goldbachLogRemovalWeight_antitone hG

theorem goldbach_log_removed_prime_term {p : ℕ} (hp : p.Prime) (θ : PrimeCircle) :
    goldbachLogRemovalWeight p •
      ((ArithmeticFunction.vonMangoldt p:ℂ)*fourier ((p^2:ℕ):ℤ) θ)=
        fourier ((p^2:ℕ):ℤ) θ := by
  have hlog : Real.log p≠0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  rw [goldbachLogRemovalWeight_of_two_le hp.two_le,
    ArithmeticFunction.vonMangoldt_apply_prime hp,Complex.real_smul,
    ←mul_assoc,←Complex.ofReal_mul,one_div_mul_cancel hlog,Complex.ofReal_one,one_mul]

theorem goldbach_log_removed_mangoldt_split (M : ℕ) (θ : PrimeCircle) :
    goldbachLogRemovedMangoldtPrefix M θ=goldbachPrimeSquarePolynomial (M:ℝ) θ+
      ∑ n∈(range (M+1)).filter (fun n => ¬n.Prime),goldbachLogRemovalWeight n •
        ((ArithmeticFunction.vonMangoldt n:ℂ)*fourier ((n^2:ℕ):ℤ) θ) := by
  classical
  have hprime : (∑ n∈(range (M+1)).filter Nat.Prime,goldbachLogRemovalWeight n •
      ((ArithmeticFunction.vonMangoldt n:ℂ)*fourier ((n^2:ℕ):ℤ) θ))=
        goldbachPrimeSquarePolynomial (M:ℝ) θ := by
    simp only [goldbachPrimeSquarePolynomial,goldbachPrimeCutoff,Nat.floor_natCast,
      ContinuousMap.sum_apply]
    apply sum_congr rfl
    intro n hn
    exact goldbach_log_removed_prime_term (mem_filter.mp hn).2 θ
  unfold goldbachLogRemovedMangoldtPrefix
  rw [←sum_filter_add_sum_filter_not (range (M+1)) Nat.Prime,hprime]

theorem goldbach_prime_power_log_removal_error (N M : ℕ) (hN : 1≤N) (hMN : M≤N)
    (θ : PrimeCircle) :
    ‖goldbachLogRemovedMangoldtPrefix M θ-goldbachPrimeSquarePolynomial (M:ℝ) θ‖≤
      (2/Real.log 2)*Real.sqrt N*Real.log N := by
  classical
  rw [goldbach_log_removed_mangoldt_split,add_sub_cancel_left]
  have hterm (n : ℕ) : ‖goldbachLogRemovalWeight n •
      ((ArithmeticFunction.vonMangoldt n:ℂ)*fourier ((n^2:ℕ):ℤ) θ)‖≤
      goldbachLogRemovalWeight 0*ArithmeticFunction.vonMangoldt n := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (goldbachLogRemovalWeight_nonneg n),
      norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      show ‖fourier ((n^2:ℕ):ℤ) θ‖=1 from Circle.norm_coe _,mul_one]
    exact mul_le_mul_of_nonneg_right (goldbachLogRemovalWeight_antitone (Nat.zero_le n))
      ArithmeticFunction.vonMangoldt_nonneg
  have hbad : (∑ n∈(range (M+1)).filter (fun n => ¬n.Prime),ArithmeticFunction.vonMangoldt n)=
      ∑ n∈(Ioc 0 M).filter (fun n => ¬n.Prime),ArithmeticFunction.vonMangoldt n := by
    simp only [sum_filter]
    exact goldbach_sum_range_succ_eq_Ioc _ (by simp) M
  have hmass := mangoldt_nonprime_mass_bound hN (Ioc 0 M) (by
    intro n hn
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans hMN⟩)
  calc
    _≤∑ n∈(range (M+1)).filter (fun n => ¬n.Prime),
      ‖goldbachLogRemovalWeight n •
        ((ArithmeticFunction.vonMangoldt n:ℂ)*fourier ((n^2:ℕ):ℤ) θ)‖ := norm_sum_le _ _
    _≤∑ n∈(range (M+1)).filter (fun n => ¬n.Prime),
      goldbachLogRemovalWeight 0*ArithmeticFunction.vonMangoldt n :=
        sum_le_sum (fun n _ => hterm n)
    _=goldbachLogRemovalWeight 0*
      (∑ n∈(Ioc 0 M).filter (fun n => ¬n.Prime),ArithmeticFunction.vonMangoldt n) := by
        rw [←mul_sum,hbad]
    _≤goldbachLogRemovalWeight 0*(2*Real.sqrt N*Real.log N) :=
      mul_le_mul_of_nonneg_left hmass (goldbachLogRemovalWeight_nonneg 0)
    _=_ := by rw [goldbachLogRemovalWeight_zero]; ring

theorem goldbachPrimeSquarePolynomial_floor (U : ℝ) :
    goldbachPrimeSquarePolynomial U=goldbachPrimeSquarePolynomial (⌊U⌋₊:ℝ) := by
  simp only [goldbachPrimeSquarePolynomial,goldbachPrimeCutoff,Nat.floor_natCast]

/-- The weighted-to-unweighted prime bridge, with the proper-prime-power
error retained and all real endpoint conventions proved. -/
theorem goldbach_prime_from_mangoldt_partials (N : ℕ) (hN : 1≤N) (θ : PrimeCircle)
    {B : ℝ} (hB : 0≤B) (hprefix : ∀ m : ℕ,m≤N → ‖goldbachMangoldtPrefix m θ‖≤B)
    (U : ℝ) (hU : 0≤U) (hUN : U≤N) :
    ‖goldbachPrimeSquarePolynomial U θ‖≤B/Real.log 2+(2/Real.log 2)*Real.sqrt N*Real.log N := by
  have hM : ⌊U⌋₊≤N := by exact_mod_cast (Nat.floor_le hU).trans hUN
  have hw := goldbach_log_removed_mangoldt_bound ⌊U⌋₊ θ hB
    (fun m hm => hprefix m (hm.trans hM))
  have he := goldbach_prime_power_log_removal_error N ⌊U⌋₊ hN hM θ
  rw [goldbachPrimeSquarePolynomial_floor U]
  calc
    _=‖goldbachLogRemovedMangoldtPrefix ⌊U⌋₊ θ-
      (goldbachLogRemovedMangoldtPrefix ⌊U⌋₊ θ-goldbachPrimeSquarePolynomial (⌊U⌋₊:ℝ) θ)‖ := by
        congr 1
        ring
    _≤‖goldbachLogRemovedMangoldtPrefix ⌊U⌋₊ θ‖+
      ‖goldbachLogRemovedMangoldtPrefix ⌊U⌋₊ θ-goldbachPrimeSquarePolynomial (⌊U⌋₊:ℝ) θ‖ := norm_sub_le _ _
    _≤_ := add_le_add hw he

end PrimeSquares
