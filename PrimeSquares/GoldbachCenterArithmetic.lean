import PrimeSquares.GoldbachMajorFamilyIntegrand
import PrimeSquares.SourceCircleDoubleSum
import PrimeSquares.UnitRationalSourceCoordinates

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachCenterArithmetic (q k : ℕ) (ℓ b n a : ℤ) : ℂ :=
  if h : q=0 then 0 else
    letI : NeZero q := ⟨h⟩
    principalSquareSum q (-(a:ZMod q))*upsilon q k b (-(a:ZMod q)*(ℓ:ZMod q))*
      ZMod.stdAddChar (-(a:ZMod q)*(n:ZMod q))

theorem goldbach_center_arithmetic_eq (q k : ℕ) [NeZero q] (ℓ b n a : ℤ) :
    goldbachCenterArithmetic q k ℓ b n a=
      principalSquareSum q (-(a:ZMod q))*upsilon q k b (-(a:ZMod q)*(ℓ:ZMod q))*
        ZMod.stdAddChar (-(a:ZMod q)*(n:ZMod q)) := by
  simp only [goldbachCenterArithmetic,dite_eq_right (NeZero.ne q)]

theorem goldbach_center_arithmetic_unit_sum (q k : ℕ) [NeZero q] (ℓ b n : ℤ) :
    (∑ u : (ZMod q)ˣ,goldbachCenterArithmetic q k ℓ b n ((u:ZMod q).val:ℤ))=
      generalCoefficient q k ℓ b n := by
  simp only [goldbach_center_arithmetic_eq,Int.cast_natCast,ZMod.natCast_zmod_val]
  rw [generalCoefficient_eq]
  refine Fintype.sum_equiv (Equiv.mulLeft (-1 : (ZMod q)ˣ)) _ _ ?_
  intro u
  simp only [Equiv.coe_mulLeft,Units.val_neg,neg_one_mul]
  ring

theorem goldbach_rational_negative_character (r : ℚ) (n : ℤ) :
    realFourierPhase (-(n:ℝ)*(r:ℝ))=
      ZMod.stdAddChar (-(r.num:ZMod r.den)*(n:ZMod r.den)) := by
  have he : ((-r.num*n:ℤ):ZMod r.den)=-(r.num:ZMod r.den)*(n:ZMod r.den) := by push_cast;ring
  rw [←he,ZMod.stdAddChar_coe,realFourierPhase,Rat.cast_def]
  congr 1
  push_cast
  ring

theorem goldbach_center_arithmetic_rational (r : ℚ) (k : ℕ) (ℓ b n : ℤ) :
    goldbachCenterArithmetic r.den k ℓ b n r.num=
      realFourierPhase (-(n:ℝ)*(r:ℝ))*principalSquareSum r.den (-(r.num:ZMod r.den))*
        upsilon r.den k b (-(r.num:ZMod r.den)*(ℓ:ZMod r.den)) := by
  rw [goldbach_center_arithmetic_eq,goldbach_rational_negative_character]
  ring

theorem goldbach_centers_weighted_arithmetic (Y : ℝ) (β : ℕ→ℂ) (k : ℕ) (ℓ b n : ℤ) :
    (∑ r∈sourceRationalCenters Y,β r.den*goldbachCenterArithmetic r.den k ℓ b n r.num)=
      ∑ q∈Icc 1 ⌊Y⌋₊,β q*generalCoefficient q k ℓ b n := by
  rw [sourceRationalCenters_sum_units]
  apply sum_congr rfl
  intro q hq
  let : NeZero q := ⟨by have hh := (mem_Icc.mp hq).1;omega⟩
  rw [denominatorUnitSum_pos]
  simp only [unitRational_den,unitRational_num]
  rw [←mul_sum,goldbach_center_arithmetic_unit_sum]

end PrimeSquares
