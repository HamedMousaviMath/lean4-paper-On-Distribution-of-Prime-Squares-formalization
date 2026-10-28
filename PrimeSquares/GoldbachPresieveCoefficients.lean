import PrimeSquares.GeneralLocalEuler

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_presieve_signed_sandwich (u L t U : ℝ) (hL : L≤t) (hU : t≤U) :
    u*(if 0≤u then L else U)≤u*t ∧
      u*t≤u*(if 0≤u then U else L) := by
  by_cases hu : 0≤u
  · simp only [hu,ite_true]
    exact ⟨mul_le_mul_of_nonneg_left hL hu,mul_le_mul_of_nonneg_left hU hu⟩
  · simp only [hu,ite_false]
    exact ⟨mul_le_mul_of_nonpos_left hU (le_of_not_ge hu),
      mul_le_mul_of_nonpos_left hL (le_of_not_ge hu)⟩

theorem goldbach_presieve_unique_product (E D : Finset ℕ)
    (hE : ∀ e∈E,0 < e) (hc : ∀ e∈E,∀ d∈D,e.Coprime d) :
    Set.InjOn (fun i : ℕ×ℕ=>i.1*i.2) (↑(E×ˢD) : Set (ℕ×ℕ)) := by
  intro a ha b hb hab
  change a.1*a.2=b.1*b.2 at hab
  obtain ⟨haE,haD⟩ := mem_product.mp ha
  obtain ⟨hbE,hbD⟩ := mem_product.mp hb
  have h₁ : a.1∣b.1 := (hc a.1 haE b.2 hbD).dvd_mul_right.mp
    (hab ▸ dvd_mul_right a.1 a.2)
  have h₂ : b.1∣a.1 := (hc b.1 hbE a.2 haD).dvd_mul_right.mp
    (hab.symm ▸ dvd_mul_right b.1 b.2)
  have he : a.1=b.1 := Nat.dvd_antisymm h₁ h₂
  have hd : a.2=b.2 := Nat.eq_of_mul_eq_mul_left (hE a.1 haE) (by simpa only [he] using hab)
  exact Prod.ext he hd

noncomputable def goldbachPresievePushforward (A : Finset (ℕ×ℕ))
    (c : ℕ×ℕ→ℝ) (m : ℕ) : ℝ :=
  ∑ i∈A,if i.1*i.2=m then c i else 0

theorem goldbach_presieve_pushforward_bound (A : Finset (ℕ×ℕ))
    (hA : Set.InjOn (fun i : ℕ×ℕ=>i.1*i.2) (↑A : Set (ℕ×ℕ)))
    (c : ℕ×ℕ→ℝ) (hc : ∀ i∈A,|c i|≤1) (m : ℕ) :
    |goldbachPresievePushforward A c m|≤1 := by
  classical
  have hcard : (A.filter (fun i=>i.1*i.2=m)).card≤1 := by
    apply card_le_one.mpr
    intro a ha b hb
    exact hA (mem_filter.mp ha).1 (mem_filter.mp hb).1
      ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
  unfold goldbachPresievePushforward
  rw [←sum_filter]
  calc
    _≤∑ i∈A.filter (fun i=>i.1*i.2=m),|c i| := abs_sum_le_sum_abs _ _
    _≤∑ _i∈A.filter (fun i=>i.1*i.2=m),(1:ℝ) :=
      sum_le_sum (fun i hi=>hc i (mem_filter.mp hi).1)
    _=((A.filter (fun i=>i.1*i.2=m)).card:ℝ) := by simp only [sum_const,nsmul_eq_mul,mul_one]
    _≤1 := by exact_mod_cast hcard

theorem goldbach_presieve_pushforward_reindex (A : Finset (ℕ×ℕ))
    (c : ℕ×ℕ→ℝ) (r : ℕ→ℝ) :
    (∑ m∈A.image (fun i=>i.1*i.2),goldbachPresievePushforward A c m*r m)=
      ∑ i∈A,c i*r (i.1*i.2) := by
  classical
  unfold goldbachPresievePushforward
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have him : i.1*i.2∈A.image (fun i=>i.1*i.2) := mem_image.mpr ⟨i,hi,rfl⟩
  simp only [ite_mul,zero_mul]
  rw [sum_ite_eq,ite_eq_left him]

theorem goldbach_presieve_level (E D : Finset ℕ) (D₀ D₁ : ℝ)
    (hE : ∀ e∈E,0 < e ∧ (e:ℝ) < D₀)
    (hD : ∀ d∈D,0 < d ∧ (d:ℝ) < D₁)
    (c : ℕ×ℕ→ℝ) (m : ℕ) (hm : D₀*D₁≤m) :
    goldbachPresievePushforward (E×ˢD) c m=0 := by
  classical
  apply sum_eq_zero
  intro i hi
  obtain ⟨he,hd⟩ := mem_product.mp hi
  have he0 : (0:ℝ) < i.1 := by exact_mod_cast (hE i.1 he).1
  have hd0 : (0:ℝ) < i.2 := by exact_mod_cast (hD i.2 hd).1
  have hlt : (i.1:ℝ)*(i.2:ℝ) < D₀*D₁ :=
    mul_lt_mul (hE i.1 he).2 (hD i.2 hd).2.le hd0 (he0.trans (hE i.1 he).2).le
  have hne : i.1*i.2≠m := by
    intro heq
    have hh : ((i.1*i.2:ℕ):ℝ) < D₀*D₁ := by simpa only [Nat.cast_mul] using hlt
    rw [heq] at hh
    exact (not_lt_of_ge hm) hh
  exact ite_eq_right hne

end PrimeSquares
