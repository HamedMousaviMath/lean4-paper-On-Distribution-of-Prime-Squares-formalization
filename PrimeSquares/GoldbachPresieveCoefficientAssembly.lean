import PrimeSquares.GoldbachPresieveMainError

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_presieve_pushforward_off_image (A : Finset (ℕ×ℕ))
    (c : ℕ×ℕ→ℝ) (m : ℕ) (hm : m∉A.image (fun i=>i.1*i.2)) :
    goldbachPresievePushforward A c m=0 := by
  classical
  apply sum_eq_zero
  intro i hi
  exact ite_eq_right (fun heq=>hm (mem_image.mpr ⟨i,hi,heq⟩))

theorem goldbach_presieve_pushforward_superset (A : Finset (ℕ×ℕ))
    (c : ℕ×ℕ→ℝ) (r : ℕ→ℝ) (T : Finset ℕ)
    (hT : A.image (fun i=>i.1*i.2)⊆T) :
    (∑ m∈T,goldbachPresievePushforward A c m*r m)=∑ i∈A,c i*r (i.1*i.2) := by
  classical
  calc
    _=∑ m∈A.image (fun i=>i.1*i.2),goldbachPresievePushforward A c m*r m := by
      apply (sum_subset hT _).symm
      intro m _ hm
      rw [goldbach_presieve_pushforward_off_image A c m hm,zero_mul]
    _=_ := goldbach_presieve_pushforward_reindex A c r

theorem goldbach_presieve_coefficient_properties (E D : Finset ℕ) (D₀ D₁ : ℝ)
    (hE : ∀ e∈E,0 < e ∧ (e:ℝ) < D₀)
    (hD : ∀ d∈D,0 < d ∧ (d:ℝ) < D₁)
    (hc : ∀ e∈E,∀ d∈D,e.Coprime d) (u lo hi : ℕ→ℝ)
    (hu : ∀ d∈D,|u d|≤1) (hlo : ∀ e∈E,|lo e|≤1) (hhi : ∀ e∈E,|hi e|≤1) :
    (∀ m : ℕ,|goldbachPresievePushforward (E×ˢD) (goldbachPresievePair u lo hi) m|≤1) ∧
    (∀ m : ℕ,D₀*D₁≤m→goldbachPresievePushforward (E×ˢD) (goldbachPresievePair u lo hi) m=0) := by
  refine ⟨?_,?_⟩
  · exact goldbach_presieve_pushforward_bound (E×ˢD)
      (goldbach_presieve_unique_product E D (fun e he=>(hE e he).1) hc)
      (goldbachPresievePair u lo hi) (goldbach_presieve_pair_bound E D u lo hi hu hlo hhi)
  · exact goldbach_presieve_level E D D₀ D₁ hE hD (goldbachPresievePair u lo hi)

theorem goldbach_presieve_product_range (E D : Finset ℕ) (D₀ D₁ : ℝ)
    (hE : ∀ e∈E,0 < e ∧ (e:ℝ) < D₀)
    (hD : ∀ d∈D,0 < d ∧ (d:ℝ) < D₁) :
    (E×ˢD).image (fun i=>i.1*i.2)⊆range (Nat.ceil (D₀*D₁)) := by
  intro m hm
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hm
  obtain ⟨he,hd⟩ := mem_product.mp hi
  have he0 : (0:ℝ) < i.1 := by exact_mod_cast (hE i.1 he).1
  have hd0 : (0:ℝ) < i.2 := by exact_mod_cast (hD i.2 hd).1
  have hlt : (i.1:ℝ)*(i.2:ℝ) < D₀*D₁ :=
    mul_lt_mul (hE i.1 he).2 (hD i.2 hd).2.le hd0 (he0.trans (hE i.1 he).2).le
  apply mem_range.mpr
  apply Nat.lt_ceil.mpr
  simpa only [Nat.cast_mul] using hlt

theorem goldbach_presieve_remainder_level (E D : Finset ℕ) (D₀ D₁ : ℝ)
    (hE : ∀ e∈E,0 < e ∧ (e:ℝ) < D₀)
    (hD : ∀ d∈D,0 < d ∧ (d:ℝ) < D₁) (c : ℕ×ℕ→ℝ) (r : ℕ→ℝ) :
    (∑ m∈range (Nat.ceil (D₀*D₁)),goldbachPresievePushforward (E×ˢD) c m*r m)=
      ∑ i∈E×ˢD,c i*r (i.1*i.2) :=
  goldbach_presieve_pushforward_superset (E×ˢD) c r _ (goldbach_presieve_product_range E D D₀ D₁ hE hD)

end PrimeSquares
