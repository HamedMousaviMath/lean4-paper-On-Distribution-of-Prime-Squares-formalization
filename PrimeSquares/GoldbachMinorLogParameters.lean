import PrimeSquares.GoldbachUniformAnnularMinor

set_option autoImplicit false
namespace PrimeSquares

def goldbachMinorCutoffExponent (t : ℝ) : ℝ := t+2

def goldbachMinorRadiusThreshold (D : UniformRenGhoshInputs) (t : ℝ) : ℝ :=
  6*t+4*D.logarithmicPower+8

noncomputable def goldbachMinorPrimeConstant (D : UniformRenGhoshInputs) : ℝ :=
  (2*goldbachPrimeExponentialConstant D+3)/Real.log 2

theorem goldbachMinorPrimeConstant_pos (D : UniformRenGhoshInputs) :
    0<goldbachMinorPrimeConstant D := by
  have hp := goldbachPrimeExponentialConstant_nonneg D
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold goldbachMinorPrimeConstant
  positivity

theorem goldbach_log_minor_radius_identity {x L : ℝ} (hx : 0<x) (hL : 0<L)
    (C K : ℝ) : L^C*((x*L^(-K))/x)^2=L^(C-2*K) := by
  have hr : (x*L^(-K))/x=L^(-K) := by field_simp [hx.ne']
  rw [hr,←Real.rpow_natCast,←Real.rpow_mul hL.le,←Real.rpow_add hL]
  congr 1
  ring

theorem goldbach_log_minor_annular_budget (D : UniformRenGhoshInputs)
    {x L t C : ℝ} (hx : 0<x) (hL : 1≤L)
    (hC : goldbachMinorRadiusThreshold D t≤C) :
    goldbachPrimeExponentialConstant D*L^D.logarithmicPower*
        (L^C*((x*L^(-goldbachMinorCutoffExponent t))/x)^2)^(-(1/4:ℝ))≤
      goldbachPrimeExponentialConstant D*L^(-t-1) := by
  have hL0 : 0<L := by linarith
  rw [goldbach_log_minor_radius_identity hx hL0,
    ←Real.rpow_mul hL0.le,mul_assoc,←Real.rpow_add hL0]
  apply mul_le_mul_of_nonneg_left _ (goldbachPrimeExponentialConstant_nonneg D)
  apply Real.rpow_le_rpow_of_exponent_le hL
  unfold goldbachMinorRadiusThreshold at hC
  unfold goldbachMinorCutoffExponent
  linarith

theorem goldbach_log_minor_small_cutoff {x L t : ℝ} (hL : 0<L) :
    (x*L^(-goldbachMinorCutoffExponent t))*L=x*L^(-t-1) := by
  calc
    _=x*(L^(-goldbachMinorCutoffExponent t)*L^(1:ℝ)) := by rw [Real.rpow_one]; ring
    _=x*L^(-goldbachMinorCutoffExponent t+1) := by rw [Real.rpow_add hL]
    _=x*L^(-t-1) := by
      congr 2
      unfold goldbachMinorCutoffExponent
      ring

/-- Elementary logarithmic algebra turns the proved numeric prime estimate
into the required saving. All eventual analytic inequalities are separated. -/
theorem goldbach_prime_minor_log_parameters (D : UniformRenGhoshInputs)
    (N : ℕ) (hN : 1≤N) {t C : ℝ} (ht : 0<t)
    (hC : goldbachMinorRadiusThreshold D t≤C) (hlog : 1≤Real.log N)
    (hH4 : 4≤(N:ℝ)*(Real.log N)^(-goldbachMinorCutoffExponent t))
    (hstart : (D.startingScale:ℝ)≤(N:ℝ)*(Real.log N)^(-goldbachMinorCutoffExponent t))
    (hExp : Real.exp 1≤(N:ℝ)*(Real.log N)^(-goldbachMinorCutoffExponent t))
    (hpower : ((Real.log N)^C)^4≤((N:ℝ)*(Real.log N)^(-goldbachMinorCutoffExponent t))/2)
    (hsqrt : Real.sqrt N*Real.log N≤(N:ℝ)*(Real.log N)^(-t))
    (ξ U : ℝ) (hU : 0≤U) (hUN : U≤N)
    (hout : (ξ:PrimeCircle)∈GoldbachMinorArcs N ((Real.log N)^C)) :
    ‖goldbachPrimeSquarePolynomial U (ξ:PrimeCircle)‖≤
      goldbachMinorPrimeConstant D*(N:ℝ)*(Real.log N)^(-t) := by
  have hn0 : (0:ℝ)<N := by exact_mod_cast hN
  have hl0 : 0<Real.log N := by linarith
  have hcp : 0≤C := by
    have hd := D.power_nonneg
    unfold goldbachMinorRadiusThreshold at hC
    linarith
  have hminexp : 0≤C-2*goldbachMinorCutoffExponent t := by
    have hd := D.power_nonneg
    unfold goldbachMinorRadiusThreshold at hC
    unfold goldbachMinorCutoffExponent
    linarith
  have hR : 1≤(Real.log N)^C := Real.one_le_rpow hlog hcp
  have hmin : 1≤(Real.log N)^C*
      (((N:ℝ)*(Real.log N)^(-goldbachMinorCutoffExponent t))/(N:ℝ))^2 := by
    rw [goldbach_log_minor_radius_identity hn0 hl0]
    exact Real.one_le_rpow hlog hminexp
  have hb := goldbach_prime_minor_from_numeric_parameters D N hN ξ
    hH4 hstart hExp hR hmin hpower hout U hU hUN
  have ha := goldbach_log_minor_annular_budget D hn0 hlog hC
  have hsmall := goldbach_log_minor_small_cutoff (x:=(N:ℝ)) (t:=t) hl0
  have hsave : (Real.log N)^(-t-1)≤(Real.log N)^(-t) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by linarith)
  have hnum : 2*(goldbachPrimeExponentialConstant D*(Real.log N)^D.logarithmicPower*
      ((Real.log N)^C*(((N:ℝ)*(Real.log N)^(-goldbachMinorCutoffExponent t))/(N:ℝ))^2)^(-(1/4:ℝ)))*
        (N:ℝ)+((N:ℝ)*(Real.log N)^(-goldbachMinorCutoffExponent t))*Real.log N≤
      (2*goldbachPrimeExponentialConstant D+1)*(N:ℝ)*(Real.log N)^(-t) := by
    rw [hsmall]
    have hmain := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha (by norm_num : (0:ℝ)≤2)) hn0.le
    have hcomb : 2*(goldbachPrimeExponentialConstant D*(Real.log N)^(-t-1))*(N:ℝ)+
        (N:ℝ)*(Real.log N)^(-t-1)=
          (2*goldbachPrimeExponentialConstant D+1)*(N:ℝ)*(Real.log N)^(-t-1) := by ring
    have hmono := mul_le_mul_of_nonneg_left hsave
      (by have hp := goldbachPrimeExponentialConstant_nonneg D; positivity :
        0≤(2*goldbachPrimeExponentialConstant D+1)*(N:ℝ))
    exact (add_le_add hmain le_rfl).trans (hcomb.le.trans hmono)
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  calc
    _≤_ := hb
    _≤((2*goldbachPrimeExponentialConstant D+1)*(N:ℝ)*(Real.log N)^(-t))/Real.log 2+
        (2/Real.log 2)*((N:ℝ)*(Real.log N)^(-t)) :=
      add_le_add (div_le_div_of_nonneg_right hnum hl2.le)
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsqrt (by positivity : 0≤2/Real.log 2))
    _=goldbachMinorPrimeConstant D*(N:ℝ)*(Real.log N)^(-t) := by
      unfold goldbachMinorPrimeConstant
      ring

end PrimeSquares
