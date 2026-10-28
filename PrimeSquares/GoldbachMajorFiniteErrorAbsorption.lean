import PrimeSquares.GoldbachMajorSourceCounts

set_option autoImplicit false
open Filter
namespace PrimeSquares

theorem goldbach_source_index_card_printed (N : ℕ) (hN : 1≤N) (hlog : 1≤Real.log N)
    (L B δ : ℝ) (V : ℕ→ℝ) (hB : 0≤B) (hδ : 0<δ)
    (hL : L<(N:ℝ)^(2-δ))
    (hV : ∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L → V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) :
    ((goldbachCoefficientIndices L V).card:ℝ)^2≤3*(N:ℝ)^(4-δ)*Real.log N := by
  have hnR : (0:ℝ)<N := by exact_mod_cast hN
  have hpow : (N:ℝ)^(2-δ)≤(N:ℝ)^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN : (1:ℝ)≤N) (by linarith : 2-δ≤(2:ℝ))
  have hp : (Real.log N)^(-B)≤1 := Real.rpow_le_one_of_one_le_of_nonpos hlog (by linarith)
  have hVp : ∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L → V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ) := by
    intro ℓ hℓ hℓL
    have hh := mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg ((N:ℝ)^2/ℓ))
    exact (hV ℓ hℓ hℓL).trans (by simpa only [mul_one] using hh)
  have hc := goldbach_source_index_card_square N hlog L V (hL.le.trans hpow) hVp
  have hmax : max L 0≤(N:ℝ)^(2-δ) := max_le hL.le (Real.rpow_nonneg hnR.le _)
  have he : (N:ℝ)^2*(N:ℝ)^(2-δ)=(N:ℝ)^(4-δ) := by
    rw [←Real.rpow_two,←Real.rpow_add hnR]
    congr 1
    ring
  calc
    _≤3*(N:ℝ)^2*max L 0*Real.log N := hc
    _≤3*(N:ℝ)^2*(N:ℝ)^(2-δ)*Real.log N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax (by positivity)) (by linarith)
    _=3*(N:ℝ)^(4-δ)*Real.log N := by
      rw [mul_assoc (3:ℝ) ((N:ℝ)^2),he]

theorem goldbach_major_finite_error_eventual {δ : ℝ} (hδ : 0<δ) (C t : ℝ) :
    ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      1≤Real.log N ∧ 12*(Real.log N)^(2*C+2*t+1)≤(N:ℝ)^δ := by
  have hp := (isLittleO_log_rpow_rpow_atTop (2*C+2*t+1) hδ).bound
    (by norm_num : (0:ℝ)<1/12)
  have he : ∀ᶠ x : ℝ in atTop,
      1≤Real.log x ∧ 12*(Real.log x)^(2*C+2*t+1)≤x^δ := by
    filter_upwards [eventually_ge_atTop (Real.exp 1),hp] with x hx hb
    have hx0 : 0<x := (Real.exp_pos 1).trans_le hx
    have hl : 1≤Real.log x := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
    have hb' : (Real.log x)^(2*C+2*t+1)≤(1/12:ℝ)*x^δ := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by linarith : 0≤Real.log x) _),
        abs_of_nonneg (Real.rpow_nonneg hx0.le _)] using hb
    exact ⟨hl,by nlinarith only [hb']⟩
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop).eventually he
  obtain ⟨M,hM⟩ := eventually_atTop.mp hn
  refine ⟨max M 4,le_max_right _ _,?_⟩
  intro N hN
  exact hM N ((le_max_left _ _).trans hN)

theorem goldbach_major_finite_error_numeric {x l I δ C t : ℝ}
    (hx : 0<x) (hl : 0<l) (hI : 0≤I)
    (hcard : I^2≤3*x^(4-δ)*l) (hbudget : 12*l^(2*C+2*t+1)≤x^δ) :
    2*l^C*I≤x^2*l^(-t) := by
  have hLC : (l^C)^2=l^(2*C) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hl.le]
    congr 1
    ring
  have hLt : (l^(-t))^2=l^(-2*t) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hl.le]
    congr 1
    ring
  have hN : x^(4-δ)*x^δ=x^4 := by
    rw [←Real.rpow_add hx]
    have he : (4-δ)+δ=4 := by ring
    rw [he]
    exact Real.rpow_natCast x 4
  have hLprod : l^(2*C)*l=l^(2*C+1) := by rw [Real.rpow_add hl,Real.rpow_one]
  have hbudget' : 12*l^(2*C+1)≤x^δ*l^(-2*t) := by
    have hb : (12*l^(2*C+1))*l^(2*t)≤x^δ := by
      rw [mul_assoc,←Real.rpow_add hl]
      have he : (2*C+1)+2*t=2*C+2*t+1 := by ring
      rw [he]
      exact hbudget
    have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hl (2*t))).mpr hb
    have he : -2*t= -(2*t) := by ring
    rw [he,Real.rpow_neg hl.le]
    simpa only [div_eq_mul_inv] using hh
  have hsq : (2*l^C*I)^2≤(x^2*l^(-t))^2 := calc
    _=4*l^(2*C)*I^2 := by rw [←hLC];ring
    _≤4*l^(2*C)*(3*x^(4-δ)*l) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _=x^(4-δ)*(12*l^(2*C+1)) := by rw [←hLprod];ring
    _≤x^(4-δ)*(x^δ*l^(-2*t)) :=
      mul_le_mul_of_nonneg_left hbudget' (Real.rpow_nonneg hx.le _)
    _=x^4*l^(-2*t) := by rw [←mul_assoc,hN]
    _=(x^2*l^(-t))^2 := by rw [mul_pow,hLt];ring
  have htarget : 0≤x^2*l^(-t) := by positivity
  have hleft : 0≤2*l^C*I := by positivity
  nlinarith

theorem goldbach_source_finite_error_absorbed {δ : ℝ} (hδ : 0<δ) (C t : ℝ) :
    ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      1≤Real.log N ∧ ∀ (L B : ℝ) (V : ℕ→ℝ),0≤B → L<(N:ℝ)^(2-δ) →
      (∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L → V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) →
      2*(Real.log N)^C*((goldbachCoefficientIndices L V).card:ℝ)≤(N:ℝ)^2*(Real.log N)^(-t) := by
  obtain ⟨N₀,hN₀,hbudget⟩ := goldbach_major_finite_error_eventual hδ C t
  refine ⟨N₀,hN₀,?_⟩
  intro N hN
  obtain ⟨hl,hb⟩ := hbudget N hN
  refine ⟨hl,?_⟩
  intro L B V hB hL hV
  exact goldbach_major_finite_error_numeric (by exact_mod_cast (show 0<N by omega))
    (by linarith) (Nat.cast_nonneg _)
    (goldbach_source_index_card_printed N (by omega) hl L B δ V hB hδ hL hV) hb

end PrimeSquares
