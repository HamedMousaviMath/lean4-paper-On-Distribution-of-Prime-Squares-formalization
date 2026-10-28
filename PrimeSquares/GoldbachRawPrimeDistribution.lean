import PrimeSquares.GoldbachMajorUpsilonIdentity
import PrimeSquares.LogPowerAbsorption

set_option autoImplicit false
open Filter Finset
namespace PrimeSquares

/-- Independent classical SW input for ordinary unweighted prime counts.
No quadratic phase, Goldbach coefficient family or circle-method endpoint
appears in the assumption. Its proof may remain external. -/
def RawPrimeSiegelWalfiszInput : Prop :=
  ∀ T : ℝ,0<T → ∀ C : ℝ,0≤C → ∃ M : ℝ,0<M ∧
    ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      ∀ q a : ℕ,0<q → (q:ℝ)≤(Real.log N)^C → a.Coprime q →
      ∀ y : ℝ,2≤y → y≤N →
        ‖(goldbachPrimeProgressionCount q a y:ℂ)-goldbachPrimeProgressionModel q y‖≤
          M*(N:ℝ)*(Real.log N)^(-T)

/-- Independent classical BV input with an endpoint maximum, encoded by an
error majorant for the actual ordinary prime counts. The modulus sum is
unweighted. The finite fixed-q fibre theorem supplies the paper's reindexing. -/
def RawPrimeBombieriVinogradovInput : Prop :=
  ∀ T : ℝ,0<T → ∃ L M X₀ : ℝ,0≤L ∧ 0<M ∧ 4≤X₀ ∧
    ∀ X : ℝ,X₀≤X → ∃ E : ℕ→ℝ,(∀ h,0≤E h) ∧
      (∀ h a : ℕ,0<h → (h:ℝ)≤Real.sqrt X*(Real.log X)^(-L) → a.Coprime h →
        ∀ y : ℝ,2≤y → y≤X →
          ‖(goldbachPrimeProgressionCount h a y:ℂ)-goldbachPrimeProgressionModel h y‖≤E h) ∧
      (∑ h∈Icc 1 ⌊Real.sqrt X*(Real.log X)^(-L)⌋₊,E h)≤M*X*(Real.log X)^(-T)

theorem goldbach_prime_count_discrepancy_real (k a : ℕ) (x : ℝ) :
    ‖(goldbachPrimeProgressionCount k a x:ℂ)-goldbachPrimeProgressionModel k x‖=
      |goldbachPrimeProgressionCount k a x-goldbachLi x/(k.totient:ℝ)| := by
  have he : (goldbachPrimeProgressionCount k a x:ℂ)-goldbachPrimeProgressionModel k x=
      ((goldbachPrimeProgressionCount k a x-goldbachLi x/(k.totient:ℝ):ℝ):ℂ) := by
    simp only [goldbachPrimeProgressionModel,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_natCast]
    ring
  rw [he,Complex.norm_real,Real.norm_eq_abs]

theorem goldbach_major_radius_eventual_budget (C t : ℝ) :
    ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      1≤Real.log N ∧ (Real.log N)^C≤(N:ℝ)*(Real.log N)^(-t) := by
  have he : ∀ᶠ x : ℝ in atTop,
      1≤Real.log x ∧ (Real.log x)^C≤x*(Real.log x)^(-t) := by
    filter_upwards [eventually_ge_atTop (Real.exp 1),
      eventually_log_rpow_le_rpow (C+t) (by norm_num : (0:ℝ)<1)] with x hx hp
    have hl : 1≤Real.log x := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
    have hl0 : 0<Real.log x := by linarith
    refine ⟨hl,?_⟩
    have hb : (Real.log x)^C*(Real.log x)^t≤x := by
      rw [←Real.rpow_add hl0]
      simpa only [Real.rpow_one] using hp
    have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hl0 t)).mpr hb
    simpa only [div_eq_mul_inv,Real.rpow_neg hl0.le] using hh
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop).eventually he
  obtain ⟨M,hM⟩ := eventually_atTop.mp hn
  refine ⟨max M 4,le_max_right _ _,?_⟩
  intro N hN
  exact hM N ((le_max_left _ _).trans hN)

theorem goldbach_square_major_numeric (q : ℕ) [NeZero q] (a : ℤ)
    {N U B R : ℝ} (hN : 0<N) (hU : 2≤U) (hUN : U≤N) (hB : 0≤B)
    (hR : 1≤R) (hqR : (q:ℝ)≤R) (γ : ℝ) (hγ : |γ|≤R/N^2)
    (herr : ∀ u : (ZMod q)ˣ,∀ y∈Set.Icc 2 U,
      ‖(goldbachPrimeProgressionCount q (u:ZMod q).val y:ℂ)-goldbachPrimeProgressionModel q y‖≤B) :
    ‖goldbachPrimeSquarePolynomial U (((a:ℝ)/q+γ:ℝ):PrimeCircle)-
      principalSquareSum q (-(a:ZMod q))*goldbachSquareIntegral U γ‖≤
        R+(1+4*Real.pi)*R^2*B := by
  have hU0 : 0≤U := by linarith
  have hγU : |γ| *U^2≤R := by
    have hp : |γ| *N^2≤R := (le_div_iff₀ (sq_pos_of_pos hN)).mp hγ
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hU0 hUN 2) (abs_nonneg γ)).trans hp
  have hfac : 1+4*Real.pi*|γ| *U^2≤(1+4*Real.pi)*R := by
    have hp := mul_le_mul_of_nonneg_left hγU (by positivity : 0≤4*Real.pi)
    nlinarith
  have hφq : (q.totient:ℝ)≤q := by exact_mod_cast Nat.totient_le q
  have hφ : (q.totient:ℝ)≤R := hφq.trans hqR
  have hb : 0≤B*(1+4*Real.pi*|γ| *U^2) := by positivity
  apply (goldbach_square_major_from_counts q a hU hB γ herr).trans
  apply add_le_add hqR
  calc
    _≤R*(B*(1+4*Real.pi*|γ| *U^2)) := mul_le_mul_of_nonneg_right hφ hb
    _≤R*(B*((1+4*Real.pi)*R)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfac hB) (by linarith : 0≤R)
    _=(1+4*Real.pi)*R^2*B := by ring

theorem goldbach_major_log_product {L : ℝ} (hL : 0<L) (C T M x : ℝ) :
    (L^C)^2*(M*x*L^(-T))=M*x*L^(2*C-T) := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hL.le]
  calc
    _=(M*x)*(L^(C*2)*L^(-T)) := by ring_nf
    _=(M*x)*L^(C*2+ -T) := by rw [Real.rpow_add hL]
    _=M*x*L^(2*C-T) := by congr 2;ring

end PrimeSquares
