import PrimeSquares.CyclicSquareMeasures
import PrimeSquares.UniformFiniteGroupAverages

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def cyclicReducedFourier {q P : ℕ} [NeZero q] [NeZero P]
    (hd : q∣P) (ν : ZMod P → ℂ) (a : ZMod q) : ℂ :=
  ∑ z : ZMod P,ν z*ZMod.stdAddChar (-a*(ZMod.castHom hd (ZMod q) z))

theorem cyclicReducedSquare_test {q P : ℕ} [NeZero q] [NeZero P]
    (hd : q∣P) (χ : DirichletCharacter ℂ P) (a : ZMod q) :
    cyclicReducedFourier hd (cyclicSquareMeasure P χ) a =
      (P.totient : ℂ)⁻¹ * ∑ u : (ZMod P)ˣ,
        χ u*ZMod.stdAddChar (-a*((ZMod.unitsMap hd u : (ZMod q)ˣ) : ZMod q)^2) := by
  rw [cyclicReducedFourier,cyclicSquareMeasure_test]
  simp only [map_pow,ZMod.castHom_apply,ZMod.unitsMap_val]

theorem cyclicReducedSquare_changeLevel {q P : ℕ} [NeZero q] [NeZero P]
    (hd : q∣P) (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    cyclicReducedFourier hd (cyclicSquareMeasure P (DirichletCharacter.changeLevel hd χ)) a =
      twistedSquareSum q χ a := by
  rw [cyclicReducedSquare_test]
  have he := finite_group_pullback_average (ZMod.unitsMap hd) (ZMod.unitsMap_surjective hd)
    (fun u : (ZMod q)ˣ => χ u*ZMod.stdAddChar (-a*(u : ZMod q)^2))
  simpa only [ZMod.card_units_eq_totient,DirichletCharacter.changeLevel_eq_cast_of_dvd,
    ZMod.unitsMap_val,twistedSquareSum,twistedUnitQuadraticGaussSum] using he

theorem character_kernel_witness {q P : ℕ} [NeZero P] (hd : q∣P)
    (χ : DirichletCharacter ℂ P) (hc : ¬χ.conductor∣q) :
    ∃ v : (ZMod P)ˣ,ZMod.unitsMap hd v=1 ∧ χ v≠1 := by
  classical
  by_contra hn
  have hk : (ZMod.unitsMap hd).ker≤χ.toUnitHom.ker := by
    intro v hv
    rw [MonoidHom.mem_ker]
    apply Units.ext
    change χ v=1
    by_contra hχ
    exact hn ⟨v,by simpa only [MonoidHom.mem_ker] using hv,hχ⟩
  have hf : χ.FactorsThrough q := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr hk
  exact hc ((χ.mem_conductorSet_iff_conductor_dvd hd).mp hf)

theorem cyclicReducedSquare_conductor_zero {q P : ℕ} [NeZero q] [NeZero P]
    (hd : q∣P) (χ : DirichletCharacter ℂ P) (hc : ¬χ.conductor∣q) (a : ZMod q) :
    cyclicReducedFourier hd (cyclicSquareMeasure P χ) a=0 := by
  obtain ⟨v,hv,hχ⟩ := character_kernel_witness hd χ hc
  rw [cyclicReducedSquare_test]
  have he := finite_group_twisted_pullback_zero (ZMod.unitsMap hd)
    ((Units.coeHom ℂ).comp χ.toUnitHom)
    (fun u : (ZMod q)ˣ => ZMod.stdAddChar (-a*(u : ZMod q)^2)) v hv hχ
  change ∑ u : (ZMod P)ˣ,χ u*ZMod.stdAddChar (-a*(ZMod.unitsMap hd u : ZMod q)^2)=0 at he
  rw [he,mul_zero]

theorem cyclicReducedSquare_conductor_formula {q P : ℕ} [NeZero q] [NeZero P]
    (hd : q∣P) (χ : DirichletCharacter ℂ P) :
    (∃ χq : DirichletCharacter ℂ q,χ=DirichletCharacter.changeLevel hd χq ∧
      ∀ a : ZMod q,cyclicReducedFourier hd (cyclicSquareMeasure P χ) a=twistedSquareSum q χq a)
      ↔χ.conductor∣q := by
  constructor
  · rintro ⟨χq,he,_⟩
    exact (χ.mem_conductorSet_iff_conductor_dvd hd).mp ⟨hd,χq,he⟩
  · intro hc
    obtain ⟨_,χq,he⟩ := (χ.mem_conductorSet_iff_conductor_dvd hd).mpr hc
    refine ⟨χq,he,?_⟩
    intro a
    rw [he]
    exact cyclicReducedSquare_changeLevel hd χq a

theorem cyclicRationalFourier_eq_reduced {q P : ℕ} [NeZero q] [NeZero P]
    (hd : q∣P) (ν : ZMod P → ℂ) (a : ℤ) :
    (∑ z : ZMod P,ν z*negativeFourierCharacter (z.val : ℤ)
      (((a : ℝ)/q : ℝ) : PrimeCircle))=cyclicReducedFourier hd ν (a : ZMod q) := by
  unfold cyclicReducedFourier
  apply sum_congr rfl
  intro z _
  have hz : (z.val : ZMod q)=ZMod.castHom hd (ZMod q) z := by
    change (z.val : ZMod q)=ZMod.cast z
    rw [←ZMod.cast_natCast hd z.val,ZMod.natCast_zmod_val]
  rw [negativeFourierCharacter_rational]
  simp only [Int.cast_neg,Int.cast_mul,Int.cast_natCast,hz,neg_mul]

theorem cyclicReducedPrincipalSquare {q P : ℕ} [NeZero q] [NeZero P]
    (hd : q∣P) (a : ZMod q) :
    cyclicReducedFourier hd (cyclicSquareMeasure P 1) a=principalSquareSum q a := by
  simpa only [map_one,twistedSquareSum_principal] using cyclicReducedSquare_changeLevel hd 1 a

end PrimeSquares
