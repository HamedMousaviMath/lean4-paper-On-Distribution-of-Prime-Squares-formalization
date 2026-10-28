import PrimeSquares.QuadraticIntegralBound
import PrimeSquares.CyclicFullSquareCoefficients
import PrimeSquares.OutsideSourceArcs

set_option autoImplicit false
namespace PrimeSquares

/-- Independent classical scalar Weyl approximation in rational-center form.
    This is a consequence of the quadratic approximation of Fiedler--Jurkat--Korner
    restated in Han--Lacey--Yang, arXiv:1907.05734v2, Theorem3.1, with Dirichlet
    selection and reduction of a/(2q) included in this unformalized interface.
    It contains no Q, circle-model sum, IW operator, or maximal conclusion. -/
def RawQuadraticWeylApproximationInput (E : ℝ) : Prop :=
  ∀ (M : ℕ), 1 ≤ M → ∀ ξ : ℝ, ∃ r : ℚ,
    r.den ≤ 8*M ∧ |ξ-(r : ℝ)| ≤ 1/(4*(M : ℝ)*(r.den : ℝ)) ∧
    ‖weightedSquareAverageSymbol M (fun _ => 1) (ξ : PrimeCircle)-
      rationalFullSquareGauss r*initialQuadraticModel M (ξ-(r : ℝ))‖ ≤
        E*Real.sqrt (r.den : ℝ)/(M : ℝ)

theorem rationalFullSquareGauss_half_decay (r : ℚ) :
    ‖rationalFullSquareGauss r‖ ≤ 2*(Real.sqrt (r.den : ℝ))⁻¹ := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  have ha : IsUnit (r.num : ZMod r.den) :=
    (ZMod.coe_int_isUnit_iff_isCoprime r.num r.den).mpr r.isCoprime_num_den.symm
  have h := normalizedCompleteGauss_decay r.den _ ha.neg
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  simpa only [rationalFullSquareGauss, Real.rpow_neg hq.le, ←Real.sqrt_eq_rpow] using h

theorem quadratic_weyl_center_unique {N M R ξ : ℝ} {r s : ℚ}
    (hN : 0 < N) (hM : 0 < M) (hR : 0 ≤ R) (hMN : N ≤ 2*M) (hMN' : M ≤ N)
    (hNR : 32*R ≤ N) (hr : (r.den : ℝ) ≤ 8*M) (hs : (s.den : ℝ) ≤ R)
    (hsmall : |ξ-(r : ℝ)| ≤ 1/(4*M*(r.den : ℝ)))
    (harc : |ξ-(s : ℝ)| ≤ R/((s.den : ℝ)*N^2)) : r = s := by
  have hr0 : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hs0 : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  have hdist : |(r : ℝ)-(s : ℝ)| ≤ 1/(4*M*(r.den : ℝ))+R/((s.den : ℝ)*N^2) := by
    calc
      _ ≤ |(r : ℝ)-ξ|+|ξ-(s : ℝ)| := abs_sub_le _ _ _
      _ = |ξ-(r : ℝ)|+|ξ-(s : ℝ)| := by rw [abs_sub_comm (r : ℝ) ξ]
      _ ≤ _ := add_le_add hsmall harc
  by_contra hne
  have hsep := (rational_separation r s hne).trans hdist
  have hmul := (div_le_iff₀ (mul_pos hr0 hs0)).mp hsep
  have he : (1/(4*M*(r.den : ℝ))+R/((s.den : ℝ)*N^2))*
      ((r.den : ℝ)*(s.den : ℝ)) = (s.den : ℝ)/(4*M)+R*(r.den : ℝ)/N^2 := by
    field_simp
  rw [he] at hmul
  have hfirst : (s.den : ℝ)/(4*M) ≤ R/(2*N) := by
    calc
      _ ≤ R/(4*M) := div_le_div_of_nonneg_right hs (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left hR (by positivity) (by linarith)
  have hsecond : R*(r.den : ℝ)/N^2 ≤ 8*R/N := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hN) hN).mpr
    have hd : (r.den : ℝ) ≤ 8*N := by linarith
    have hm := mul_le_mul_of_nonneg_left hd (mul_nonneg hR hN.le)
    nlinarith
  have hupper : (s.den : ℝ)/(4*M)+R*(r.den : ℝ)/N^2 ≤ (17*R)/(2*N) := by
    calc
      _ ≤ R/(2*N)+8*R/N := add_le_add hfirst hsecond
      _ = _ := by ring
  have hlt : (17*R)/(2*N) < 1 := by
    apply (div_lt_one (by positivity : 0 < 2*N)).mpr
    linarith
  linarith

end PrimeSquares
