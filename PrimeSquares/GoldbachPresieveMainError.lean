import PrimeSquares.GoldbachPresieveFiniteSequence

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_presieve_main_error (E D : Finset ℕ) (u lo hi g : ℕ→ℝ) (V ε : ℝ)
    (hlo : |(∑ e∈E,lo e*g e)-V|≤ε*V)
    (hhi : |(∑ e∈E,hi e*g e)-V|≤ε*V) (hg : ∀ d∈D,0≤g d) :
    |(∑ i∈E×ˢD,goldbachPresievePair u lo hi i*g i.1*g i.2)-V*(∑ d∈D,u d*g d)|≤
      ε*V*(∑ d∈D,|u d| * g d) := by
  rw [goldbach_presieve_pair_sum]
  have heq : (∑ d∈D,u d*(if 0≤u d then ∑ e∈E,lo e*g e else ∑ e∈E,hi e*g e)*g d)-
      V*(∑ d∈D,u d*g d)=
      ∑ d∈D,(u d*g d)*((if 0≤u d then ∑ e∈E,lo e*g e else ∑ e∈E,hi e*g e)-V) := by
    rw [mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro d _
    ring
  rw [heq]
  calc
    _≤∑ d∈D,|(u d*g d)*((if 0≤u d then ∑ e∈E,lo e*g e else ∑ e∈E,hi e*g e)-V)| :=
      abs_sum_le_sum_abs _ _
    _≤∑ d∈D,(|u d| * g d)*(ε*V) := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul,abs_mul,abs_of_nonneg (hg d hd)]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (hg d hd))
      split_ifs
      · exact hlo
      · exact hhi
    _=_ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring

theorem goldbach_presieve_quantitative_lower {ι : Type*} (A : Finset ι) (a : ι→ℕ)
    (E D P Q : Finset ℕ) (hc : ∀ e∈E,∀ d∈D,e.Coprime d) (lo hi u g r : ℕ→ℝ)
    (X V₀ V₁ ε₀ ε₁ f : ℝ) (hX : 0≤X) (hV₀ : 0≤V₀)
    (hlo : ∀ t : ℕ,(∑ e∈E,lo e*goldbachDivIndicator e t)≤goldbachSiftIndicator P t)
    (hhi : ∀ t : ℕ,goldbachSiftIndicator P t≤∑ e∈E,hi e*goldbachDivIndicator e t)
    (hu : ∀ t : ℕ,(∑ d∈D,u d*goldbachDivIndicator d t)≤goldbachSiftIndicator Q t)
    (hA : ∀ i∈E×ˢD,goldbachSequenceDivisorCount A a (i.1*i.2)=X*g (i.1*i.2)+r (i.1*i.2))
    (hmul : ∀ e∈E,∀ d∈D,g (e*d)=g e*g d) (hg : ∀ d∈D,0≤g d)
    (hBminus : |(∑ e∈E,lo e*g e)-V₀|≤ε₀*V₀)
    (hBplus : |(∑ e∈E,hi e*g e)-V₀|≤ε₀*V₀)
    (hB₁ : V₁*(f-ε₁)≤∑ d∈D,u d*g d) :
    X*(V₀*V₁*(f-ε₁)-ε₀*V₀*(∑ d∈D,|u d| * g d))+
        (∑ m∈(E×ˢD).image (fun i=>i.1*i.2),
          goldbachPresievePushforward (E×ˢD) (goldbachPresievePair u lo hi) m*r m)≤
      goldbachSequenceSiftedCount A a (P∪Q) := by
  have hseq := goldbach_presieve_sequence_lower A a E D P Q hc lo hi u hlo hhi hu
  rw [goldbach_presieve_sequence_expansion A a E D (goldbachPresievePair u lo hi) X g r hA hmul] at hseq
  have herr := goldbach_presieve_main_error E D u lo hi g V₀ ε₀ hBminus hBplus hg
  have hb := mul_le_mul_of_nonneg_left hB₁ hV₀
  have hmain : V₀*V₁*(f-ε₁)-ε₀*V₀*(∑ d∈D,|u d| * g d)≤
      ∑ i∈E×ˢD,goldbachPresievePair u lo hi i*g i.1*g i.2 := by
    have h := (abs_le.mp herr).1
    nlinarith
  rw [goldbach_presieve_pushforward_reindex]
  exact (add_le_add (mul_le_mul_of_nonneg_left hmain hX) le_rfl).trans hseq

theorem goldbach_presieve_quantitative_upper {ι : Type*} (A : Finset ι) (a : ι→ℕ)
    (E D P Q : Finset ℕ) (hc : ∀ e∈E,∀ d∈D,e.Coprime d) (lo hi u g r : ℕ→ℝ)
    (X V₀ V₁ ε₀ ε₁ F : ℝ) (hX : 0≤X) (hV₀ : 0≤V₀)
    (hlo : ∀ t : ℕ,(∑ e∈E,lo e*goldbachDivIndicator e t)≤goldbachSiftIndicator P t)
    (hhi : ∀ t : ℕ,goldbachSiftIndicator P t≤∑ e∈E,hi e*goldbachDivIndicator e t)
    (hu : ∀ t : ℕ,goldbachSiftIndicator Q t≤∑ d∈D,u d*goldbachDivIndicator d t)
    (hA : ∀ i∈E×ˢD,goldbachSequenceDivisorCount A a (i.1*i.2)=X*g (i.1*i.2)+r (i.1*i.2))
    (hmul : ∀ e∈E,∀ d∈D,g (e*d)=g e*g d) (hg : ∀ d∈D,0≤g d)
    (hBminus : |(∑ e∈E,lo e*g e)-V₀|≤ε₀*V₀)
    (hBplus : |(∑ e∈E,hi e*g e)-V₀|≤ε₀*V₀)
    (hB₁ : (∑ d∈D,u d*g d)≤V₁*(F+ε₁)) :
    goldbachSequenceSiftedCount A a (P∪Q)≤
      X*(V₀*V₁*(F+ε₁)+ε₀*V₀*(∑ d∈D,|u d| * g d))+
        ∑ m∈(E×ˢD).image (fun i=>i.1*i.2),
          goldbachPresievePushforward (E×ˢD) (goldbachPresievePair u hi lo) m*r m := by
  have hseq := goldbach_presieve_sequence_upper A a E D P Q hc lo hi u hlo hhi hu
  rw [goldbach_presieve_sequence_expansion A a E D (goldbachPresievePair u hi lo) X g r hA hmul] at hseq
  have herr := goldbach_presieve_main_error E D u hi lo g V₀ ε₀ hBplus hBminus hg
  have hb := mul_le_mul_of_nonneg_left hB₁ hV₀
  have hmain : (∑ i∈E×ˢD,goldbachPresievePair u hi lo i*g i.1*g i.2)≤
      V₀*V₁*(F+ε₁)+ε₀*V₀*(∑ d∈D,|u d| * g d) := by
    have h := (abs_le.mp herr).2
    nlinarith
  rw [goldbach_presieve_pushforward_reindex]
  exact hseq.trans (add_le_add (mul_le_mul_of_nonneg_left hmain hX) le_rfl)

end PrimeSquares
