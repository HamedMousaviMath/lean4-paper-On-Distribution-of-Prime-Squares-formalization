import PrimeSquares.GoldbachPresieveCoefficients

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachDivIndicator (d a : ℕ) : ℝ := if d∣a then 1 else 0
noncomputable def goldbachSiftIndicator (P : Finset ℕ) (a : ℕ) : ℝ :=
  if ∀ p∈P,¬p∣a then 1 else 0
noncomputable def goldbachPresievePair (u lo hi : ℕ→ℝ) (i : ℕ×ℕ) : ℝ :=
  u i.2*(if 0≤u i.2 then lo i.1 else hi i.1)

theorem goldbach_div_indicator_nonneg (d a : ℕ) : 0≤goldbachDivIndicator d a := by
  unfold goldbachDivIndicator
  split_ifs <;> norm_num

theorem goldbach_sift_indicator_nonneg (P : Finset ℕ) (a : ℕ) :
    0≤goldbachSiftIndicator P a := by
  unfold goldbachSiftIndicator
  split_ifs <;> norm_num

theorem goldbach_div_indicator_product (e d a : ℕ) (hc : e.Coprime d) :
    goldbachDivIndicator (e*d) a=goldbachDivIndicator e a*goldbachDivIndicator d a := by
  have heq : e*d∣a ↔ e∣a ∧ d∣a :=
    ⟨fun h=>⟨(dvd_mul_right e d).trans h,(dvd_mul_left d e).trans h⟩,
      fun h=>hc.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  by_cases he : e∣a <;> by_cases hd : d∣a <;> simp [goldbachDivIndicator,heq,he,hd]

theorem goldbach_sift_indicator_union (P Q : Finset ℕ) (a : ℕ) :
    goldbachSiftIndicator (P∪Q) a=goldbachSiftIndicator P a*goldbachSiftIndicator Q a := by
  classical
  unfold goldbachSiftIndicator
  split_ifs <;> norm_num <;> aesop (add simp [mem_union])

theorem goldbach_presieve_pair_bound (E D : Finset ℕ) (u lo hi : ℕ→ℝ)
    (hu : ∀ d∈D,|u d|≤1) (hlo : ∀ e∈E,|lo e|≤1) (hhi : ∀ e∈E,|hi e|≤1)
    (i : ℕ×ℕ) (hi' : i∈E×ˢD) : |goldbachPresievePair u lo hi i|≤1 := by
  obtain ⟨he,hd⟩ := mem_product.mp hi'
  unfold goldbachPresievePair
  rw [abs_mul]
  have h : |if 0≤u i.2 then lo i.1 else hi i.1|≤1 := by
    split_ifs
    · exact hlo i.1 he
    · exact hhi i.1 he
  exact (mul_le_mul (hu i.2 hd) h (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem goldbach_presieve_pair_sum (E D : Finset ℕ) (u lo hi j₀ j₁ : ℕ→ℝ) :
    (∑ i∈E×ˢD,goldbachPresievePair u lo hi i*j₀ i.1*j₁ i.2)=
      ∑ d∈D,u d*(if 0≤u d then ∑ e∈E,lo e*j₀ e else ∑ e∈E,hi e*j₀ e)*j₁ d := by
  rw [sum_product,sum_comm]
  apply sum_congr rfl
  intro d _
  by_cases h : 0≤u d
  · simp only [goldbachPresievePair,h,ite_true]
    calc
      _=(∑ e∈E,u d*(lo e*j₀ e))*j₁ d := by
        rw [sum_mul]
        apply sum_congr rfl
        intro e _
        ring
      _=_ := by rw [mul_sum]
  · simp only [goldbachPresievePair,h,ite_false]
    calc
      _=(∑ e∈E,u d*(hi e*j₀ e))*j₁ d := by
        rw [sum_mul]
        apply sum_congr rfl
        intro e _
        ring
      _=_ := by rw [mul_sum]

theorem goldbach_presieve_pair_divisor_sum (E D : Finset ℕ)
    (hc : ∀ e∈E,∀ d∈D,e.Coprime d) (u lo hi : ℕ→ℝ) (a : ℕ) :
    (∑ i∈E×ˢD,goldbachPresievePair u lo hi i*goldbachDivIndicator (i.1*i.2) a)=
      ∑ d∈D,u d*(if 0≤u d then ∑ e∈E,lo e*goldbachDivIndicator e a
        else ∑ e∈E,hi e*goldbachDivIndicator e a)*goldbachDivIndicator d a := by
  calc
    _=∑ i∈E×ˢD,goldbachPresievePair u lo hi i*goldbachDivIndicator i.1 a*goldbachDivIndicator i.2 a := by
      apply sum_congr rfl
      intro i hi'
      obtain ⟨he,hd⟩ := mem_product.mp hi'
      rw [goldbach_div_indicator_product i.1 i.2 a (hc i.1 he i.2 hd)]
      ring
    _=_ := goldbach_presieve_pair_sum E D u lo hi (fun e=>goldbachDivIndicator e a) (fun d=>goldbachDivIndicator d a)

theorem goldbach_presieve_pointwise_lower (E D P Q : Finset ℕ)
    (hc : ∀ e∈E,∀ d∈D,e.Coprime d) (lo hi u : ℕ→ℝ) (a : ℕ)
    (hlo : (∑ e∈E,lo e*goldbachDivIndicator e a)≤goldbachSiftIndicator P a)
    (hhi : goldbachSiftIndicator P a≤∑ e∈E,hi e*goldbachDivIndicator e a)
    (hu : (∑ d∈D,u d*goldbachDivIndicator d a)≤goldbachSiftIndicator Q a) :
    (∑ i∈E×ˢD,goldbachPresievePair u lo hi i*goldbachDivIndicator (i.1*i.2) a)≤
      goldbachSiftIndicator (P∪Q) a := by
  rw [goldbach_presieve_pair_divisor_sum E D hc]
  calc
    _≤∑ d∈D,(u d*goldbachSiftIndicator P a)*goldbachDivIndicator d a := by
      apply sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_right
        (goldbach_presieve_signed_sandwich (u d) _ _ _ hlo hhi).1 (goldbach_div_indicator_nonneg d a)
    _=(∑ d∈D,u d*goldbachDivIndicator d a)*goldbachSiftIndicator P a := by
      rw [sum_mul]
      apply sum_congr rfl
      intro d _
      ring
    _≤goldbachSiftIndicator Q a*goldbachSiftIndicator P a :=
      mul_le_mul_of_nonneg_right hu (goldbach_sift_indicator_nonneg P a)
    _=_ := by rw [goldbach_sift_indicator_union];ring

theorem goldbach_presieve_pointwise_upper (E D P Q : Finset ℕ)
    (hc : ∀ e∈E,∀ d∈D,e.Coprime d) (lo hi u : ℕ→ℝ) (a : ℕ)
    (hlo : (∑ e∈E,lo e*goldbachDivIndicator e a)≤goldbachSiftIndicator P a)
    (hhi : goldbachSiftIndicator P a≤∑ e∈E,hi e*goldbachDivIndicator e a)
    (hu : goldbachSiftIndicator Q a≤∑ d∈D,u d*goldbachDivIndicator d a) :
    goldbachSiftIndicator (P∪Q) a≤
      ∑ i∈E×ˢD,goldbachPresievePair u hi lo i*goldbachDivIndicator (i.1*i.2) a := by
  rw [goldbach_presieve_pair_divisor_sum E D hc]
  calc
    _=goldbachSiftIndicator Q a*goldbachSiftIndicator P a := by rw [goldbach_sift_indicator_union];ring
    _≤(∑ d∈D,u d*goldbachDivIndicator d a)*goldbachSiftIndicator P a :=
      mul_le_mul_of_nonneg_right hu (goldbach_sift_indicator_nonneg P a)
    _=∑ d∈D,(u d*goldbachSiftIndicator P a)*goldbachDivIndicator d a := by
      rw [sum_mul]
      apply sum_congr rfl
      intro d _
      ring
    _≤_ := by
      apply sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_right
        (goldbach_presieve_signed_sandwich (u d) _ _ _ hlo hhi).2 (goldbach_div_indicator_nonneg d a)

end PrimeSquares
