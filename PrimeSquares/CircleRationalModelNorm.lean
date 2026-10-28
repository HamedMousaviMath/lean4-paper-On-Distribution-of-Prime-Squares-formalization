import PrimeSquares.CircleRationalModel

namespace PrimeSquares

theorem centeredRationalSymbol_norm {N : ℕ} (hN : 2 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (r : ℚ) (hκ : ‖κ r‖ ≤ 1) (x : ℝ) :
    ‖centeredRationalSymbol N (by omega) χ κ β r x‖ ≤
      gaussModelConstant*(r.den : ℝ)^(-(5/12 : ℝ)) := by
  let : NeZero r.den := ⟨r.den_pos.ne'⟩
  have ha : IsUnit (r.num : ZMod r.den) :=
    (ZMod.coe_int_isUnit_iff_isCoprime r.num r.den).mpr r.isCoprime_num_den.symm
  exact (localizedAnnularGaussModel_norm_le N _ (χ r) (κ r) β _ _ x).trans
    (((Classical.choose_spec annularGaussModel_uniform_bounds).2
      N r.den (χ r) (κ r) β (r.num : ZMod r.den) hN hβ0 hβ1 ha hκ).1 x)

theorem circleRationalModelTerm_norm {N : ℕ} (hN : 2 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (r : ℚ) (hκ : ‖κ r‖ ≤ 1)
    (θ : PrimeCircle) :
    ‖circleRationalModelTerm N (by omega) χ κ β r θ‖ ≤
      3*(gaussModelConstant*(r.den : ℝ)^(-(5/12 : ℝ))) := by
  exact compactCircleLift_norm_bound (centeredRationalSymbol N (by omega) χ κ β r)
    (centeredRationalSymbol_support N (by omega) χ κ β r)
    (centeredRationalSymbol_norm hN χ κ hβ0 hβ1 r hκ) _

end PrimeSquares
