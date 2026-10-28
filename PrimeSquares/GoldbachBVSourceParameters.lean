import PrimeSquares.GoldbachLinearBVRow

set_option autoImplicit false
open Filter
namespace PrimeSquares

theorem goldbach_progression_scale_logs (N ℓ : ℕ) (hN : 1≤N) (hℓ : 0<ℓ)
    (δ : ℝ) (hsize : (ℓ:ℝ)<(N:ℝ)^(2-δ)) :
    (N:ℝ)^δ<(N:ℝ)^2/ℓ ∧ (N:ℝ)^2/ℓ≤(N:ℝ)^2 ∧
      δ*Real.log N≤Real.log ((N:ℝ)^2/ℓ) ∧
      Real.log ((N:ℝ)^2/ℓ)≤2*Real.log N := by
  have hnR : (0:ℝ)<N := by exact_mod_cast hN
  have hlR : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  have hl1 : (1:ℝ)≤ℓ := by exact_mod_cast hℓ
  have hp := mul_lt_mul_of_pos_right hsize (Real.rpow_pos_of_pos hnR δ)
  rw [←Real.rpow_add hnR] at hp
  have hexp : (2-δ)+δ=2 := by ring
  rw [hexp,Real.rpow_two] at hp
  have hlow : (N:ℝ)^δ<(N:ℝ)^2/ℓ := (lt_div_iff₀ hlR).mpr (by nlinarith)
  have hupp : (N:ℝ)^2/ℓ≤(N:ℝ)^2 := (div_le_iff₀ hlR).mpr (by nlinarith [sq_nonneg (N:ℝ)])
  have hx0 : 0<(N:ℝ)^2/ℓ := div_pos (sq_pos_of_pos hnR) hlR
  refine ⟨hlow,hupp,?_,?_⟩
  · simpa only [Real.log_rpow hnR] using
      Real.log_le_log (Real.rpow_pos_of_pos hnR δ) hlow.le
  · simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log hx0 hupp

theorem goldbach_bv_log_level {x X V C L B : ℝ}
    (hlog : 1≤Real.log x) (hXlog : 0<Real.log X)
    (hupper : Real.log X≤2*Real.log x) (hL : 0≤L)
    (hB : C+L+1≤B) (hbig : (2:ℝ)^L≤Real.log x)
    (hV : V≤Real.sqrt X*(Real.log x)^(-B)) :
    V*(Real.log x)^C≤Real.sqrt X*(Real.log X)^(-L) := by
  have hl0 : 0<Real.log x := by linarith
  have hden : (Real.log X)^L≤(Real.log x)^(L+1) := by
    calc
      _≤(2*Real.log x)^L := Real.rpow_le_rpow hXlog.le hupper hL
      _=(2:ℝ)^L*(Real.log x)^L := Real.mul_rpow (by norm_num) hl0.le
      _≤Real.log x*(Real.log x)^L :=
        mul_le_mul_of_nonneg_right hbig (Real.rpow_nonneg hl0.le _)
      _=(Real.log x)^(L+1) := by rw [Real.rpow_add hl0,Real.rpow_one];ring
  have hi := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hXlog L) hden
  have hinv : (Real.log x)^(-L-1)≤(Real.log X)^(-L) := by
    have he : -L-1= -(L+1) := by ring
    rw [he,Real.rpow_neg hl0.le,Real.rpow_neg hXlog.le]
    simpa only [one_div] using hi
  calc
    _≤(Real.sqrt X*(Real.log x)^(-B))*(Real.log x)^C :=
      mul_le_mul_of_nonneg_right hV (Real.rpow_nonneg hl0.le _)
    _=Real.sqrt X*(Real.log x)^(C-B) := by
      rw [mul_assoc,←Real.rpow_add hl0]
      congr 2
      ring
    _≤Real.sqrt X*(Real.log x)^(-L-1) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlog (by linarith)) (Real.sqrt_nonneg _)
    _≤Real.sqrt X*(Real.log X)^(-L) := mul_le_mul_of_nonneg_left hinv (Real.sqrt_nonneg _)

theorem goldbach_bv_log_saving {x X δ T : ℝ} (hlog : 0<Real.log x)
    (hδ : 0<δ) (hT : 0≤T) (hlower : δ*Real.log x≤Real.log X) :
    (Real.log X)^(-T)≤δ^(-T)*(Real.log x)^(-T) := by
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos hδ hlog) hlower (by linarith : -T≤0)
  simpa only [Real.mul_rpow hδ.le hlog.le] using hp

theorem goldbach_bv_source_eventual_threshold {δ L X₀ : ℝ} (hδ : 0<δ) (hX₀ : 4≤X₀) :
    ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      1≤Real.log N ∧ (2:ℝ)^L≤Real.log N ∧ X₀≤(N:ℝ)^δ := by
  have he : ∀ᶠ x : ℝ in atTop,
      1≤Real.log x ∧ (2:ℝ)^L≤Real.log x ∧ X₀≤x^δ := by
    filter_upwards [eventually_ge_atTop (Real.exp (max 1 ((2:ℝ)^L))),
      eventually_scaled_rpow_le_rpow (by linarith : 0≤X₀) hδ] with x hx hp
    have hl : max 1 ((2:ℝ)^L)≤Real.log x := by
      simpa only [Real.log_exp] using Real.log_le_log
        (Real.exp_pos (max 1 ((2:ℝ)^L))) hx
    exact ⟨(le_max_left _ _).trans hl,(le_max_right _ _).trans hl,
      by simpa only [Real.rpow_zero,mul_one] using hp⟩
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop).eventually he
  obtain ⟨M,hM⟩ := eventually_atTop.mp hn
  refine ⟨max M 4,le_max_right _ _,?_⟩
  intro N hN
  exact hM N ((le_max_left _ _).trans hN)

theorem goldbach_lcm_bv_level (k q : ℕ) (hk : 0<k) (hq : 0<q)
    {V R H : ℝ} (hkv : (k:ℝ)<V) (hqR : (q:ℝ)≤R) (hVR : V*R≤H) :
    (k.lcm q:ℝ)≤H := by
  have hlcm : (k.lcm q:ℝ)≤(k:ℝ)*(q:ℝ) := by exact_mod_cast Nat.lcm_le_mul hk hq
  have hV : 0≤V := (Nat.cast_nonneg k).trans hkv.le
  exact hlcm.trans ((mul_le_mul hkv.le hqR (Nat.cast_nonneg _) hV).trans hVR)

end PrimeSquares
