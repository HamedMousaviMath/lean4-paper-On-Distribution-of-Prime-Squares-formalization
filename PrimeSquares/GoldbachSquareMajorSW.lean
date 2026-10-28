import PrimeSquares.GoldbachRawPrimeDistribution

set_option autoImplicit false
namespace PrimeSquares

/-- Full actual SW square approximation, uniform in every real U and every
major-arc numerator. Only ordinary prime-count SW is an external input. -/
theorem goldbach_square_major_siegel_walfisz (H : RawPrimeSiegelWalfiszInput)
    {t C : ℝ} (ht : 0<t) (hC : 0≤C) :
    ∃ K : ℝ,0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      ∀ q : ℕ,0<q → (q:ℝ)≤(Real.log N)^C →
      ∀ (a : ℤ) (U γ : ℝ),2≤U → U≤N → |γ|≤(Real.log N)^C/(N:ℝ)^2 →
      ∀ hq : NeZero q,
        ‖goldbachPrimeSquarePolynomial U (((a:ℝ)/q+γ:ℝ):PrimeCircle)-
          @principalSquareSum q hq (-(a:ZMod q))*goldbachSquareIntegral U γ‖≤
            K*(N:ℝ)*(Real.log N)^(-t) := by
  let T := t+2*C+1
  have hT : 0<T := by dsimp [T];linarith
  obtain ⟨M,hM,N₁,hN₁,hSW⟩ := H T hT C hC
  obtain ⟨N₂,hN₂,hbudget⟩ := goldbach_major_radius_eventual_budget C t
  let K := 1+(1+4*Real.pi)*M
  have hK : 0<K := by dsimp [K];positivity
  refine ⟨K,hK,max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro N hN q hq hqR a U γ hU hUN hγ hqI
  let : NeZero q := hqI
  have hNN₁ := (le_max_left N₁ N₂).trans hN
  have hNN₂ := (le_max_right N₁ N₂).trans hN
  obtain ⟨hlog,hRbudget⟩ := hbudget N hNN₂
  have hnR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlR : 0<Real.log N := by linarith
  have hR : 1≤(Real.log N)^C := Real.one_le_rpow hlog hC
  have hB : 0≤M*(N:ℝ)*(Real.log N)^(-T) := by positivity
  have hcounts : ∀ u : (ZMod q)ˣ,∀ y∈Set.Icc 2 U,
      ‖(goldbachPrimeProgressionCount q (u:ZMod q).val y:ℂ)-goldbachPrimeProgressionModel q y‖≤
        M*(N:ℝ)*(Real.log N)^(-T) := by
    intro u y hy
    have hu : (u:ZMod q).val.Coprime q := by
      apply (ZMod.isUnit_iff_coprime (u:ZMod q).val q).mp
      simpa only [ZMod.natCast_zmod_val] using u.isUnit
    exact hSW N hNN₁ q (u:ZMod q).val hq hqR hu y hy.1 (hy.2.trans hUN)
  have hb := goldbach_square_major_numeric q a hnR hU hUN hB hR hqR γ hγ hcounts
  have he : 2*C-T= -t-1 := by dsimp [T];ring
  rw [mul_assoc (1+4*Real.pi),goldbach_major_log_product hlR C T M (N:ℝ),he] at hb
  have hsave : (Real.log N)^(-t-1)≤(Real.log N)^(-t) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by linarith)
  have hm : 0≤(1+4*Real.pi)*M*(N:ℝ) := by positivity
  calc
    _≤(Real.log N)^C+(1+4*Real.pi)*(M*(N:ℝ)*(Real.log N)^(-t-1)) := hb
    _≤(N:ℝ)*(Real.log N)^(-t)+(1+4*Real.pi)*(M*(N:ℝ)*(Real.log N)^(-t)) :=
      add_le_add hRbudget (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsave hm)
    _=K*(N:ℝ)*(Real.log N)^(-t) := by dsimp [K];ring

end PrimeSquares
