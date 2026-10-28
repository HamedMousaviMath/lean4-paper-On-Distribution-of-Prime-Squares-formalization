import PrimeSquares.GoldbachPresievePointwise

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachSequenceDivisorCount {ι : Type*}
    (A : Finset ι) (a : ι→ℕ) (d : ℕ) : ℝ :=
  ((A.filter (fun x=>d∣a x)).card:ℝ)

noncomputable def goldbachSequenceSiftedCount {ι : Type*}
    (A : Finset ι) (a : ι→ℕ) (P : Finset ℕ) : ℝ := by
  classical
  exact ((A.filter (fun x=>∀ p∈P,¬p∣a x)).card:ℝ)

theorem goldbach_sequence_divisor_count_sum {ι : Type*}
    (A : Finset ι) (a : ι→ℕ) (d : ℕ) :
    goldbachSequenceDivisorCount A a d=∑ x∈A,goldbachDivIndicator d (a x) := by
  classical
  simp only [goldbachSequenceDivisorCount,goldbachDivIndicator,card_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem goldbach_sequence_sifted_count_sum {ι : Type*}
    (A : Finset ι) (a : ι→ℕ) (P : Finset ℕ) :
    goldbachSequenceSiftedCount A a P=∑ x∈A,goldbachSiftIndicator P (a x) := by
  classical
  simp only [goldbachSequenceSiftedCount,goldbachSiftIndicator,card_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem goldbach_sequence_weighted_divisor_sum {ι : Type*}
    (A : Finset ι) (a : ι→ℕ) (B : Finset (ℕ×ℕ)) (c : ℕ×ℕ→ℝ) :
    (∑ i∈B,c i*goldbachSequenceDivisorCount A a (i.1*i.2))=
      ∑ x∈A,∑ i∈B,c i*goldbachDivIndicator (i.1*i.2) (a x) := by
  simp_rw [goldbach_sequence_divisor_count_sum,mul_sum]
  exact sum_comm

theorem goldbach_presieve_sequence_lower {ι : Type*} (A : Finset ι) (a : ι→ℕ)
    (E D P Q : Finset ℕ) (hc : ∀ e∈E,∀ d∈D,e.Coprime d) (lo hi u : ℕ→ℝ)
    (hlo : ∀ t : ℕ,(∑ e∈E,lo e*goldbachDivIndicator e t)≤goldbachSiftIndicator P t)
    (hhi : ∀ t : ℕ,goldbachSiftIndicator P t≤∑ e∈E,hi e*goldbachDivIndicator e t)
    (hu : ∀ t : ℕ,(∑ d∈D,u d*goldbachDivIndicator d t)≤goldbachSiftIndicator Q t) :
    (∑ i∈E×ˢD,goldbachPresievePair u lo hi i*goldbachSequenceDivisorCount A a (i.1*i.2))≤
      goldbachSequenceSiftedCount A a (P∪Q) := by
  rw [goldbach_sequence_weighted_divisor_sum,goldbach_sequence_sifted_count_sum]
  exact sum_le_sum (fun x _=>goldbach_presieve_pointwise_lower E D P Q hc lo hi u (a x)
    (hlo (a x)) (hhi (a x)) (hu (a x)))

theorem goldbach_presieve_sequence_upper {ι : Type*} (A : Finset ι) (a : ι→ℕ)
    (E D P Q : Finset ℕ) (hc : ∀ e∈E,∀ d∈D,e.Coprime d) (lo hi u : ℕ→ℝ)
    (hlo : ∀ t : ℕ,(∑ e∈E,lo e*goldbachDivIndicator e t)≤goldbachSiftIndicator P t)
    (hhi : ∀ t : ℕ,goldbachSiftIndicator P t≤∑ e∈E,hi e*goldbachDivIndicator e t)
    (hu : ∀ t : ℕ,goldbachSiftIndicator Q t≤∑ d∈D,u d*goldbachDivIndicator d t) :
    goldbachSequenceSiftedCount A a (P∪Q)≤
      ∑ i∈E×ˢD,goldbachPresievePair u hi lo i*goldbachSequenceDivisorCount A a (i.1*i.2) := by
  rw [goldbach_sequence_weighted_divisor_sum,goldbach_sequence_sifted_count_sum]
  exact sum_le_sum (fun x _=>goldbach_presieve_pointwise_upper E D P Q hc lo hi u (a x)
    (hlo (a x)) (hhi (a x)) (hu (a x)))

theorem goldbach_presieve_sequence_expansion {ι : Type*}
    (A : Finset ι) (a : ι→ℕ) (E D : Finset ℕ) (c : ℕ×ℕ→ℝ) (X : ℝ) (g r : ℕ→ℝ)
    (hA : ∀ i∈E×ˢD,goldbachSequenceDivisorCount A a (i.1*i.2)=X*g (i.1*i.2)+r (i.1*i.2))
    (hg : ∀ e∈E,∀ d∈D,g (e*d)=g e*g d) :
    (∑ i∈E×ˢD,c i*goldbachSequenceDivisorCount A a (i.1*i.2))=
      X*(∑ i∈E×ˢD,c i*g i.1*g i.2)+∑ i∈E×ˢD,c i*r (i.1*i.2) := by
  calc
    _=∑ i∈E×ˢD,(X*(c i*g i.1*g i.2)+c i*r (i.1*i.2)) := by
      apply sum_congr rfl
      intro i hi
      obtain ⟨he,hd⟩ := mem_product.mp hi
      rw [hA i (mem_product.mpr ⟨he,hd⟩),hg i.1 he i.2 hd]
      ring
    _=_ := by rw [sum_add_distrib,mul_sum]

theorem goldbach_presieve_disjoint_support_coprime (E D P Q : Finset ℕ)
    (hPQ : Disjoint P Q)
    (hE : ∀ e∈E,∀ p : ℕ,p.Prime→p∣e→p∈P)
    (hD : ∀ d∈D,∀ p : ℕ,p.Prime→p∣d→p∈Q) :
    ∀ e∈E,∀ d∈D,e.Coprime d := by
  intro e he d hd
  apply Nat.coprime_of_dvd
  intro p hp hpe hpd
  exact (disjoint_left.mp hPQ) (hE e he p hp hpe) (hD d hd p hp hpd)

end PrimeSquares
