import PrimeSquares.PrimeFactorPower

set_option autoImplicit false
namespace PrimeSquares

set_option maxRecDepth 10000 in
theorem goldbach_upper_boundary_data :
    Nat.Prime 491 ∧ Nat.Prime 13 ∧ Nat.Prime 7 ∧
      660%24=12 ∧ 491%24=11 ∧ 491+13^2=660 ∧ 660<27^2 ∧
      490=2*5*7*7 ∧ 7%4=3 ∧ 5%4=1 ∧ Nat.Coprime 70 659 := by
  norm_num
  decide

theorem goldbach_seventy_no_strict_factor :
    ¬∃ u p : ℕ,p.Prime ∧ p%4=3 ∧ (7:ℝ)<p ∧ 70=2*u*p := by
  rintro ⟨u,p,hp,hp4,hp7,he⟩
  have hd : p∣70 := ⟨2*u,by simpa only [mul_comm p] using he⟩
  rw [show (70:ℕ)=2*(5*7) by norm_num,hp.dvd_mul,hp.dvd_mul] at hd
  rcases hd with hd|hd|hd
  · have hh := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hd
    norm_num [hh] at hp4
  · have hh := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp hd
    norm_num [hh] at hp4
  · have hh := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp hd
    norm_num [hh] at hp7

noncomputable def goldbachBoundaryAlpha : ℝ := Real.log 27/Real.log 7

theorem goldbachBoundaryAlpha_range : 1<goldbachBoundaryAlpha ∧ goldbachBoundaryAlpha<2 := by
  have hl7 : 0<Real.log (7:ℝ) := Real.log_pos (by norm_num)
  have hlow : Real.log (7:ℝ)<Real.log 27 := Real.log_lt_log (by norm_num) (by norm_num)
  have hhigh : Real.log (27:ℝ)<2*Real.log 7 := by
    calc
      _<Real.log ((7:ℝ)^2) := Real.log_lt_log (by norm_num) (by norm_num)
      _=_ := by rw [Real.log_pow]; norm_num
  unfold goldbachBoundaryAlpha
  exact ⟨(lt_div_iff₀ hl7).mpr (by linarith),(div_lt_iff₀ hl7).mpr hhigh⟩

theorem goldbachBoundaryAlpha_cutoff : (27:ℝ)^(1/goldbachBoundaryAlpha)=7 := by
  have hl7 : Real.log (7:ℝ)≠0 := ne_of_gt (Real.log_pos (by norm_num))
  have hl27 : Real.log (27:ℝ)≠0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.rpow_def_of_pos (by norm_num)]
  have he : Real.log (27:ℝ)*(1/goldbachBoundaryAlpha)=Real.log 7 := by
    unfold goldbachBoundaryAlpha
    field_simp
  rw [he,Real.exp_log (by norm_num : (0:ℝ)<7)]

theorem goldbach_boundary_closed_geometry :
    (5:ℝ)<27^2/(2*7^2) ∧ (7:ℝ)<Real.sqrt (27^2/(2*5)) ∧
      ¬7∣659 ∧ ∀ p : ℕ,p.Prime → p∣5 → p%4=1 := by
  refine ⟨by norm_num,Real.lt_sqrt_of_sq_lt (by norm_num),by decide,?_⟩
  intro p hp hd
  have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp hd
  norm_num [he]

end PrimeSquares
