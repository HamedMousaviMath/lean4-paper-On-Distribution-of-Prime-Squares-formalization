import PrimeSquares.GoldbachRankinLogProduct
import PrimeSquares.LogPowerAbsorption

set_option autoImplicit false
open Filter
namespace PrimeSquares

theorem goldbach_eventually_log_square_budget {W : ℝ} (hW : 0≤W) :
    ∀ᶠ x : ℝ in atTop,W*(1+(Real.log x)^2)≤x := by
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_log_rpow_le_rpow (2:ℝ)
    (by norm_num : (0:ℝ)<1/2),
    eventually_scaled_rpow_le_rpow (K:=2*W) (a:=(1/2:ℝ)) (b:=1) (by positivity) (by norm_num)] with x hx hl hs
  rw [Real.rpow_two] at hl
  rw [Real.rpow_one] at hs
  have h1 : 1≤x^(1/2:ℝ) := Real.one_le_rpow hx (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hl hW,mul_le_mul_of_nonneg_left h1 hW]

theorem goldbach_rankin_decay_log_budget {x Y L M D t : ℝ} (K : ℕ)
    (hx : 1<x) (hY : 0<Y) (hL : 0<L) (hM : 0≤M) (_hD : 0<D) (ht : 0<t)
    (hYL : x/2≤Real.log Y) (hLD : L≤D*Real.log x)
    (hb : 4*D*(t+(K:ℝ))*(Real.log x)^2≤x) (hpoly : M*L≤x) :
    Y^(-(1/(2*L)))*(M*L)^K≤x^(-t) := by
  have hxp : 0<x := by linarith
  have hlx : 0<Real.log x := Real.log_pos hx
  have htK : 0<t+(K:ℝ) := by positivity
  have hlarge : 2*L*((t+(K:ℝ))*Real.log x)≤Real.log Y := by
    have hm := mul_le_mul_of_nonneg_right hLD (by positivity : (0:ℝ)≤2*(t+(K:ℝ))*Real.log x)
    nlinarith
  have hpower : Y^(-(1/(2*L)))≤x^(-t-(K:ℝ)) := by
    rw [Real.rpow_def_of_pos hY,Real.rpow_def_of_pos hxp]
    apply Real.exp_le_exp.mpr
    have hd : (t+(K:ℝ))*Real.log x≤Real.log Y/(2*L) :=
      (le_div_iff₀ (by positivity : (0:ℝ)<2*L)).mpr (by nlinarith [hlarge])
    convert neg_le_neg hd using 1 <;> ring
  calc
    _≤x^(-t-(K:ℝ))*x^K := mul_le_mul hpower (pow_le_pow_left₀ (mul_nonneg hM hL.le) hpoly K)
      (pow_nonneg (mul_nonneg hM hL.le) K) (Real.rpow_nonneg hxp.le _)
    _=_ := by
      rw [←Real.rpow_natCast x K,←Real.rpow_add hxp]
      congr 1
      ring

theorem goldbach_rankin_parameter_decay {C M t : ℝ} (hC : 1≤C) (hM : 0<M)
    (ht : 0<t) (K : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      (Real.exp x/(100*Real.sqrt (x^C)))^(-(1/(2*Real.log (2*x^C))))*
        (M*Real.log (2*x^C))^K≤x^(-t) := by
  let D := C+1
  let W := 1+2*Real.log 100+C+M*D+4*D*(t+(K:ℝ))
  have hD : 0<D := by dsimp [D];linarith
  have hC0 : 0≤C := by linarith
  have hl100 : 0<Real.log (100:ℝ) := Real.log_pos (by norm_num)
  have hMD : 0≤M*D := by positivity
  have hF : 0≤4*D*(t+(K:ℝ)) := by positivity
  have hW : 0≤W := by dsimp [W];positivity
  filter_upwards [eventually_ge_atTop (Real.exp 1),goldbach_eventually_log_square_budget hW] with x hx hbudget
  have hx1 : 1<x := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hx
  have hxp : 0<x := by linarith
  have hlx : 1≤Real.log x := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
  have hRp : 0<x^C := Real.rpow_pos_of_pos hxp _
  have hL : Real.log (2*x^C)=Real.log 2+C*Real.log x := by
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hRp.ne',Real.log_rpow hxp]
  have hLp : 0<Real.log (2*x^C) := by rw [hL];have := Real.log_pos (by norm_num : (1:ℝ)<2);positivity
  have hYp : 0<Real.exp x/(100*Real.sqrt (x^C)) := by positivity
  have hYlog : Real.log (Real.exp x/(100*Real.sqrt (x^C)))=
      x-Real.log 100-C*Real.log x/2 := by
    rw [Real.log_div (Real.exp_ne_zero x) (by positivity),Real.log_exp,
      Real.log_mul (by norm_num : (100:ℝ)≠0) (Real.sqrt_pos.mpr hRp).ne',Real.log_sqrt hRp.le,Real.log_rpow hxp]
    ring
  have hB0 : 0≤1+(Real.log x)^2 := by positivity
  have hB1 : 1≤1+(Real.log x)^2 := by nlinarith [sq_nonneg (Real.log x)]
  have hBlog : Real.log x≤1+(Real.log x)^2 := by nlinarith [sq_nonneg (Real.log x-1/2)]
  have hpart (v : ℝ) (hv : v≤W) : v*(1+(Real.log x)^2)≤x :=
    (mul_le_mul_of_nonneg_right hv hB0).trans hbudget
  have hb : 4*D*(t+(K:ℝ))*(Real.log x)^2≤x :=
    (mul_le_mul_of_nonneg_left (by linarith : (Real.log x)^2≤1+(Real.log x)^2) hF).trans
      (hpart _ (by dsimp [W];linarith))
  have hLD : Real.log (2*x^C)≤D*Real.log x := by
    rw [hL]
    have h2 : Real.log (2:ℝ)≤1 := by nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    dsimp [D]
    nlinarith
  have hmB : M*(D*Real.log x)≤M*D*(1+(Real.log x)^2) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hBlog hMD
  have hpoly : M*Real.log (2*x^C)≤x :=
    (mul_le_mul_of_nonneg_left hLD hM.le).trans (hmB.trans (hpart _ (by dsimp [W];linarith)))
  have hYL : x/2≤Real.log (Real.exp x/(100*Real.sqrt (x^C))) := by
    have hh : 2*Real.log 100+C*Real.log x≤(2*Real.log 100+C)*(1+(Real.log x)^2) := by
      nlinarith [mul_le_mul_of_nonneg_left hB1 (by positivity : (0:ℝ)≤2*Real.log 100),
        mul_le_mul_of_nonneg_left hBlog hC0]
    have hh' := hh.trans (hpart _ (by dsimp [W];linarith))
    rw [hYlog]
    linarith
  exact goldbach_rankin_decay_log_budget K hx1 hYp hLp hM.le hD ht hYL hLD hb hpoly

end PrimeSquares
