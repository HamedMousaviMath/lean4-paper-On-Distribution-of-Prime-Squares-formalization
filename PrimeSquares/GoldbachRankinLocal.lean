import PrimeSquares.GoldbachRankinEuler

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_geometric_partial_bound {a : ℝ} (ha0 : 0≤a) (ha1 : a<1) (J : ℕ) :
    (∑ j∈range J,a^j)≤1/(1-a) := by
  induction J with
  | zero => simp only [range_zero,sum_empty];positivity
  | succ J ih =>
    rw [sum_range_succ']
    simp only [pow_zero,pow_succ',←mul_sum]
    calc
      _≤1+a*(1/(1-a)) := by nlinarith [mul_le_mul_of_nonneg_left ih ha0]
      _=_ := by field_simp [sub_ne_zero.mpr ha1.ne'];ring

theorem goldbach_polynomial_local_bound {r a A : ℝ} (hr : 1<r) (ha : 0≤a)
    (hra : r^11*a<1) (hA : 1≤A) (hpoly : ∀ n : ℕ,(n:ℝ)+1≤A*r^n) :
    ∃ C : ℝ,0<C ∧ ∀ t : ℝ,0≤t →t≤a →∀ J : ℕ,
      (∑ j∈range (J+1),((j:ℝ)+1)^11*t^j)≤1+C*t := by
  let b := r^11*a
  let C := A^11*r^11/(1-b)
  have hb0 : 0≤b := by dsimp [b];positivity
  have hb1 : b<1 := hra
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro t ht hta J
  have hrt : r^11*t≤b := mul_le_mul_of_nonneg_left hta (by positivity)
  have hx0 : 0≤r^11*t := by positivity
  have hterm (j : ℕ) : (((j+1:ℕ):ℝ)+1)^11*t^(j+1)≤
      (A^11*(r^11*t))*b^j := by
    have hp := hpoly (j+1)
    have hpower := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity : (0:ℝ)≤((j+1:ℕ):ℝ)+1) hp 11)
      (pow_nonneg ht (j+1))
    have hcomm : (r^(j+1))^11=(r^11)^(j+1) := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
    calc
      _≤(A*r^(j+1))^11*t^(j+1) := hpower
      _=A^11*(r^11*t)^(j+1) := by rw [mul_pow,hcomm,mul_pow,mul_assoc]
      _=(A^11*(r^11*t))*(r^11*t)^j := by rw [pow_succ];ring
      _≤_ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hrt j) (by positivity)
  rw [sum_range_succ']
  simp only [Nat.cast_zero,zero_add,one_pow,pow_zero,mul_one]
  rw [add_comm (1:ℝ)]
  apply add_le_add_left
  calc
    _≤∑ j∈range J,(A^11*(r^11*t))*b^j := sum_le_sum (fun j _=>hterm j)
    _=(A^11*(r^11*t))*(∑ j∈range J,b^j) := by rw [mul_sum]
    _≤(A^11*(r^11*t))*(1/(1-b)) :=
      mul_le_mul_of_nonneg_left (goldbach_geometric_partial_bound hb0 hb1 J) (by positivity)
    _=C*t := by dsimp [C];ring

theorem goldbach_rankin_local_uniform :
    ∃ C : ℝ,0<C ∧ ∀ p : ℕ,p.Prime →∀ σ : ℝ,σ≤1/2 →∀ J : ℕ,
      (∑ j∈range (J+1),((j:ℝ)+1)^11*((p:ℝ)^(-1+σ))^j)≤
        1+C*(p:ℝ)^(-1+σ) := by
  let r := (2:ℝ)^(1/44:ℝ)
  let a := (2:ℝ)^(-(1/2:ℝ))
  have hr : 1<r := Real.one_lt_rpow (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<1/44)
  obtain ⟨A,hA,hpoly⟩ := exponent_add_one_le_geometric hr
  have ha : 0≤a := Real.rpow_nonneg (by norm_num) _
  have he : r^11*a=(2:ℝ)^(-(1/4:ℝ)) := by
    dsimp [r,a]
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤2),
      ←Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    norm_num
  have hra : r^11*a<1 := by
    rw [he]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  obtain ⟨C,hC,hbound⟩ := goldbach_polynomial_local_bound hr ha hra hA hpoly
  refine ⟨C,hC,?_⟩
  intro p hp σ hσ J
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have ht : (p:ℝ)^(-1+σ)≤a :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤p) (by linarith : -1+σ≤ -(1/2:ℝ))).trans
      (Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<2) hp2 (by norm_num : -(1/2:ℝ)≤0))
  exact hbound _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) ht J

end PrimeSquares
