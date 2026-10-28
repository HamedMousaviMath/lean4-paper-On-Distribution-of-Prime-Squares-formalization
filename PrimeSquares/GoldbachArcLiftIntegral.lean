import PrimeSquares.GoldbachRankinArithmeticTail

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace PrimeSquares

noncomputable def goldbachArcLift (r : ℚ) (f : ℝ→ℂ) (θ : PrimeCircle) : ℂ :=
  f (goldbachArcCoordinate r θ)

theorem goldbach_arc_coordinate_real_shift (r : ℚ) {x : ℝ}
    (hx : x∈Set.Ico (-(1/2:ℝ)) (1/2)) :
    goldbachArcCoordinate r ((x:PrimeCircle)+((r:ℝ):PrimeCircle))=x := by
  change (AddCircle.equivIco (1:ℝ) (-(1/2:ℝ))
    (((x:PrimeCircle)+((r:ℝ):PrimeCircle))-((r:ℝ):PrimeCircle))).val=x
  rw [add_sub_cancel_right]
  have hx' : x∈Set.Ico (-(1/2:ℝ)) (-(1/2:ℝ)+1) := by convert hx using 1;norm_num
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hx')

theorem goldbach_arc_lift_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℚ) (f : ℝ→E) (hf : ∀ x : ℝ,(1/2:ℝ)≤|x| →f x=0) :
    (∫ θ : PrimeCircle,f (goldbachArcCoordinate r θ) ∂AddCircle.haarAddCircle)=∫ x : ℝ,f x := by
  let g := fun θ : PrimeCircle=>f (goldbachArcCoordinate r θ)
  change (∫ θ : PrimeCircle,g θ ∂AddCircle.haarAddCircle)=_
  rw [←integral_add_right_eq_self g (((r:ℝ):PrimeCircle))]
  rw [←goldbach_circle_volume_eq_haar,
    ←AddCircle.integral_preimage (1:ℝ) (-(1/2:ℝ))]
  rw [show (-(1/2:ℝ))+(1:ℝ)=1/2 by ring,←integral_Ico_eq_integral_Ioc]
  calc
    _=∫ x in Set.Ico (-(1/2:ℝ)) (1/2),f x := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      exact congrArg f (goldbach_arc_coordinate_real_shift r hx)
    _=_ := by
      rw [←integral_indicator measurableSet_Ico]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x∈Set.Ico (-(1/2:ℝ)) (1/2)
      · exact Set.indicator_of_mem hx f
      · have habs : (1/2:ℝ)≤|x| := by
          by_cases hlo : -(1/2:ℝ)≤x
          · have hhi : (1/2:ℝ)≤x := by
              by_contra h
              exact hx ⟨hlo,lt_of_not_ge h⟩
            linarith [le_abs_self x]
          · have hh : x< -(1/2:ℝ) := lt_of_not_ge hlo
            linarith [neg_le_abs x]
        rw [Set.indicator_of_notMem hx,hf x habs]

theorem goldbach_arc_lift_fourier_integral (r : ℚ) (f : ℝ→ℂ)
    (hf : ∀ x : ℝ,(1/2:ℝ)≤|x| →f x=0) (n : ℤ) :
    (∫ θ : PrimeCircle,goldbachArcLift r f θ*fourier (-n) θ ∂AddCircle.haarAddCircle)=
      realFourierPhase (-(n:ℝ)*(r:ℝ))*(∫ γ : ℝ,f γ*realFourierPhase (-(n:ℝ)*γ)) := by
  let F := fun x : ℝ=>f x*fourier (-n) (((x+(r:ℝ)):ℝ):PrimeCircle)
  have hs : ∀ x : ℝ,(1/2:ℝ)≤|x| →F x=0 := by
    intro x hx
    dsimp only [F]
    rw [hf x hx,zero_mul]
  have he (θ : PrimeCircle) : goldbachArcLift r f θ*fourier (-n) θ=F (goldbachArcCoordinate r θ) := by
    have hc : (((goldbachArcCoordinate r θ+(r:ℝ)):ℝ):PrimeCircle)=θ := by
      rw [AddCircle.coe_add,goldbachArcCoordinate_coe]
      abel
    dsimp only [F,goldbachArcLift]
    rw [hc]
  simp only [he]
  rw [goldbach_arc_lift_integral r F hs,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with γ
  dsimp only [F]
  rw [realFourierPhase_integer_character,Int.cast_neg,
    show (γ+(r:ℝ))*(-(n:ℝ))=(-(n:ℝ)*(r:ℝ))+(-(n:ℝ)*γ) by ring,realFourierPhase_add]
  ring

theorem goldbach_arc_lift_energy (r : ℚ) (f : ℝ→ℂ)
    (hf : ∀ x : ℝ,(1/2:ℝ)≤|x| →f x=0) :
    (∫ θ : PrimeCircle,‖goldbachArcLift r f θ‖^2 ∂AddCircle.haarAddCircle)=∫ γ : ℝ,‖f γ‖^2 := by
  apply goldbach_arc_lift_integral r (fun x : ℝ=>‖f x‖^2)
  intro x hx
  rw [hf x hx,norm_zero,zero_pow (by decide : 2≠0)]

theorem goldbach_arc_lift_memLp (r : ℚ) (f : ℝ→ℂ) (hf : StronglyMeasurable f)
    {B : ℝ} (hB : ∀ x : ℝ,‖f x‖≤B) (p : ℝ≥0∞) :
    MemLp (goldbachArcLift r f) p AddCircle.haarAddCircle :=
  MemLp.of_bound (hf.comp_measurable (goldbachArcCoordinate_measurable r)).aestronglyMeasurable B
    (Filter.Eventually.of_forall (fun θ=>hB (goldbachArcCoordinate r θ)))

end PrimeSquares
