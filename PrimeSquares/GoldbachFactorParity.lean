import PrimeSquares.PrimeFactorPower

set_option autoImplicit false
namespace PrimeSquares

def badModFourFactors (L : List ℕ) : List ℕ := L.filter (fun p => decide (p%4=3))
def goodModFourFactors (L : List ℕ) : List ℕ := L.filter (fun p => decide (p%4≠3))

theorem mem_badModFourFactors {L : List ℕ} {p : ℕ} :
    p∈badModFourFactors L ↔ p∈L ∧ p%4=3 := by
  simp only [badModFourFactors,List.mem_filter,decide_eq_true_eq]

theorem mem_goodModFourFactors {L : List ℕ} {p : ℕ} :
    p∈goodModFourFactors L ↔ p∈L ∧ p%4≠3 := by
  simp only [goodModFourFactors,List.mem_filter,decide_eq_true_eq]

theorem modFourFactors_product (L : List ℕ) :
    L.prod=(badModFourFactors L).prod*(goodModFourFactors L).prod := by
  induction L with
  | nil => simp [badModFourFactors,goodModFourFactors]
  | cons a L ih =>
    by_cases ha : a%4=3
    · simpa [badModFourFactors,goodModFourFactors,ha,mul_assoc] using congrArg (fun m => a*m) ih
    · simpa [badModFourFactors,goodModFourFactors,ha,mul_assoc,mul_left_comm] using congrArg (fun m => a*m) ih

theorem odd_list_product_mod_four (L : List ℕ)
    (hL : ∀ p∈L,p%4=1 ∨ p%4=3) :
    L.prod%4=if (badModFourFactors L).length%2=0 then 1 else 3 := by
  induction L with
  | nil => simp [badModFourFactors]
  | cons a L ih =>
    have htail : ∀ p∈L,p%4=1 ∨ p%4=3 := fun p hp => hL p (List.mem_cons_of_mem a hp)
    have hh := ih htail
    rcases hL a (by simp) with ha|ha
    · have hb : badModFourFactors (a::L)=badModFourFactors L := by simp [badModFourFactors,ha]
      rw [List.prod_cons,hb,Nat.mul_mod,ha,one_mul,Nat.mod_mod]
      exact hh
    · have hb : badModFourFactors (a::L)=a::badModFourFactors L := by simp [badModFourFactors,ha]
      rw [List.prod_cons,hb,List.length_cons,Nat.mul_mod,ha,hh]
      by_cases hc : (badModFourFactors L).length%2=0
      · have hc' : ((badModFourFactors L).length+1)%2=1 := by omega
        simp [hc,hc']
      · have hc' : ((badModFourFactors L).length+1)%2=0 := by omega
        simp [hc,hc']

theorem modFourFactors_bad_count_even (L : List ℕ)
    (hL : ∀ p∈L,p%4=1 ∨ p%4=3) (hm : L.prod%4=1) :
    (badModFourFactors L).length%2=0 := by
  have hh := odd_list_product_mod_four L hL
  by_contra hc
  simp only [hc,ite_false,hm] at hh
  omega

theorem list_product_ge_length_power (L : List ℕ) {z : ℝ} (hz : 0≤z)
    (hL : ∀ p∈L,z≤(p:ℝ)) : z^L.length≤(L.prod:ℝ) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := hL a (by simp)
    have ht := ih (fun p hp => hL p (List.mem_cons_of_mem a hp))
    simp only [List.length_cons,List.prod_cons,Nat.cast_mul,pow_succ]
    calc
      z^L.length*z≤(L.prod:ℝ)*(a:ℝ) :=
        mul_le_mul ht ha hz (Nat.cast_nonneg _)
      _=(a:ℝ)*(L.prod:ℝ) := mul_comm _ _

/-- Multiplicity is retained: repeated bad primes occupy repeated list entries. -/
theorem exactly_two_badModFourFactors (L : List ℕ)
    (hL : ∀ p∈L,p%4=1 ∨ p%4=3) (hpos : 0<L.prod) (hm : L.prod%4=1)
    {z : ℝ} (hz : 1≤z) (hlarge : ∀ p∈badModFourFactors L,z≤(p:ℝ))
    (hsize : (L.prod:ℝ)<z^4) (hne : badModFourFactors L≠[]) :
    ∃ a b : ℕ,badModFourFactors L=[a,b] := by
  have heven := modFourFactors_bad_count_even L hL hm
  have hlen0 : 0<(badModFourFactors L).length := List.length_pos_iff.mpr hne
  have hd : (badModFourFactors L).prod∣L.prod :=
    (show List.Sublist (badModFourFactors L) L from List.filter_sublist).prod_dvd_prod
  have hprod : ((badModFourFactors L).prod:ℝ)≤(L.prod:ℝ) := by
    exact_mod_cast Nat.le_of_dvd hpos hd
  have hlower := list_product_ge_length_power (badModFourFactors L) (by linarith : 0≤z) hlarge
  have hlen : (badModFourFactors L).length<4 := by
    by_contra hc
    have hp := pow_le_pow_right₀ hz (show 4≤(badModFourFactors L).length by omega)
    exact (not_lt_of_ge (hp.trans (hlower.trans hprod))) hsize
  exact List.length_eq_two.mp (by omega)

end PrimeSquares
