import PrimeSquares.QuadraticCorrelationRelative

set_option autoImplicit false
open Finset Filter
open scoped Topology
namespace PrimeSquares

theorem quadratic_GK_absolute_error (HW : RawSplitQuadraticWeilInput)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (S : Finset (ZMod p)) :
    |quadraticCorrelation p S-primeResidueDensity p^S.card*(p:ℝ)| ≤
      (6*(S.card:ℝ)*(3:ℝ)^S.card)*(1-primeResidueDensity p)*
        (p:ℝ)^(-(1/3:ℝ))*(primeResidueDensity p^S.card*(p:ℝ)) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1:ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hb := primeResidueDensity_bounds p hp
  have hr0 : 0 ≤ primeResidueDensity p := by linarith
  have hpow := primeResidueDensity_power_lower p hp S.card
  have hfac : 1 ≤ (2*(1-primeResidueDensity p))*
      ((3:ℝ)^S.card*primeResidueDensity p^S.card) := by
    have hnon : 0 ≤ 2*(1-primeResidueDensity p) := by linarith
    have hm := mul_le_mul_of_nonneg_left hpow hnon
    nlinarith
  have hsqrt : Real.sqrt (p:ℝ) ≤ (p:ℝ)^(2/3:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
  have hrate : (p:ℝ)^(-(1/3:ℝ))*(p:ℝ)=(p:ℝ)^(2/3:ℝ) := by
    calc
      _ = (p:ℝ)^(-(1/3:ℝ))*(p:ℝ)^((1:ℝ)) := by rw [Real.rpow_one]
      _ = (p:ℝ)^(-(1/3:ℝ)+(1:ℝ)) := (Real.rpow_add hp0 _ _).symm
      _ = _ := by norm_num
  calc
    _ ≤ 3*(S.card:ℝ)*Real.sqrt p := quadraticCorrelation_density_error HW p hp S
    _ ≤ 3*(S.card:ℝ)*(p:ℝ)^(2/3:ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ ≤ (3*(S.card:ℝ)*(p:ℝ)^(2/3:ℝ))*
        ((2*(1-primeResidueDensity p))*((3:ℝ)^S.card*primeResidueDensity p^S.card)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac
        (by positivity : 0 ≤ 3*(S.card:ℝ)*(p:ℝ)^(2/3:ℝ))
    _ = _ := by
      calc
        _ = (6*(S.card:ℝ)*(3:ℝ)^S.card)*(1-primeResidueDensity p)*
            primeResidueDensity p^S.card*((p:ℝ)^(-(1/3:ℝ))*(p:ℝ)) := by rw [hrate]; ring
        _ = _ := by ring

theorem quadratic_GK_relative_error (HW : RawSplitQuadraticWeilInput)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (S : Finset (ZMod p)) :
    |quadraticCorrelation p S/(primeResidueDensity p^S.card*(p:ℝ))-1| ≤
      (6*(S.card:ℝ)*(3:ℝ)^S.card)*(1-primeResidueDensity p)*(p:ℝ)^(-(1/3:ℝ)) := by
  have hb := primeResidueDensity_bounds p hp
  have hr0 : 0 < primeResidueDensity p := by linarith
  have hp0 : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hbase : 0 < primeResidueDensity p^S.card*(p:ℝ) := by positivity
  have heq : quadraticCorrelation p S/(primeResidueDensity p^S.card*(p:ℝ))-1 =
      (quadraticCorrelation p S-primeResidueDensity p^S.card*(p:ℝ))/
        (primeResidueDensity p^S.card*(p:ℝ)) := by field_simp
  rw [heq, abs_div, abs_of_pos hbase]
  exact (div_le_iff₀ hbase).mpr (quadratic_GK_absolute_error HW p hp S)

theorem quadratic_GK_uniform_correlation (HW : RawSplitQuadraticWeilInput) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∀ S : Finset (ZMod p), S.card=k →
        |quadraticCorrelation p S/(primeResidueDensity p^k*(p:ℝ))-1| ≤
          K*(1-primeResidueDensity p)*(p:ℝ)^(-(1/3:ℝ)) := by
  refine ⟨6*(k:ℝ)*(3:ℝ)^k, by positivity, ?_⟩
  intro p _ hp S hS
  simpa only [hS] using quadratic_GK_relative_error HW p hp S

theorem quadratic_GK_tuple (HW : RawSplitQuadraticWeilInput)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k : ℕ) (h : Fin k → ZMod p)
    (hi : Function.Injective h) :
    let N : ℝ := ((Finset.univ.filter (fun t : ZMod p =>
      ∀ i : Fin k, t+h i ∈ unitSquareResidues p)).card : ℝ)
    |N-(p:ℝ)/(2:ℝ)^k| ≤ 2*(k:ℝ)*Real.sqrt p ∧
      |N/(primeResidueDensity p^k*(p:ℝ))-1| ≤
        (6*(k:ℝ)*(3:ℝ)^k)*(1-primeResidueDensity p)*(p:ℝ)^(-(1/3:ℝ)) := by
  classical
  have hc : (Finset.univ.image h).card=k := by
    rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]
  have hcount : quadraticCorrelation p (Finset.univ.image h) =
      ((Finset.univ.filter (fun t : ZMod p => ∀ i : Fin k,
        t+h i ∈ unitSquareResidues p)).card : ℝ) := by
    simp [quadraticCorrelation]
  constructor
  · simpa only [hc, hcount] using quadraticCorrelation_Weil_error HW p hp (Finset.univ.image h)
  · simpa only [hc, hcount] using quadratic_GK_relative_error HW p hp (Finset.univ.image h)

theorem primeResidueDensity_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → P ≤ p →
      (primeResidueDensity p)⁻¹ ≤ (p:ℝ)^ε := by
  have ht : Tendsto (fun p : ℕ => (p:ℝ)^ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨P,hP⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (3:ℝ))
  refine ⟨P, ?_⟩
  intro p _ hp hpP
  have hb := primeResidueDensity_bounds p hp
  have hr0 : 0 < primeResidueDensity p := by linarith
  have hinv : (primeResidueDensity p)⁻¹ ≤ 3 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hr0).mpr
    linarith
  exact hinv.trans (hP p hpP)

end PrimeSquares
