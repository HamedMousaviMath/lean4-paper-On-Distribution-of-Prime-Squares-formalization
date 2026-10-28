import PrimeSquares.QuadraticTwistCancellation
import PrimeSquares.GaussProduct

/-!
# Support of character-twisted quadratic sums

The support assertion of Lemma 3.27 is proved for any quadratic character
at level q₀d, whether or not it is primitive or induced. In particular it
applies to every real character induced from level q₀.
-/

open Finset

namespace PrimeSquares

theorem twistedSquareSum_support (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic)
    (a : ZMod q) (ha : IsUnit a) (hne : twistedSquareSum q χ a ≠ 0) :
    q.factorization 2 ≤ 5 ∧ ∀ p ∈ q.primeFactors, p ≠ 2 → q.factorization p = 1 := by
  constructor
  · by_contra! hj
    have hd : 2 ^ 6 ∣ q :=
      (Nat.prime_two.pow_dvd_iff_le_factorization (NeZero.ne q)).mpr (by omega)
    exact hne (twistedSquareSum_sixtyfour_dvd q (by simpa using hd) χ hχ a ha)
  · intro p hp hp2
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hj : 0 < q.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    by_contra! he
    exact hne (twistedSquareSum_odd_prime_square q p hp' hp2
      ((hp'.pow_dvd_iff_le_factorization (NeZero.ne q)).mpr (by omega)) χ hχ a ha)

theorem oddSquarefree_decomposition_of_factorization (q : ℕ) (hq : q ≠ 0)
    (h2 : q.factorization 2 ≤ 5)
    (ho : ∀ p ∈ q.primeFactors, p ≠ 2 → q.factorization p = 1) :
    ∃ j d : ℕ, j ≤ 5 ∧ 0 < d ∧ ¬2 ∣ d ∧ Squarefree d ∧ q = 2 ^ j * d := by
  classical
  let d := q / 2 ^ q.factorization 2
  have hd : 0 < d := Nat.ordCompl_pos 2 hq
  have hodd : ¬2 ∣ d := Nat.not_dvd_ordCompl Nat.prime_two hq
  have hsf : Squarefree d := by
    apply Nat.squarefree_of_factorization_le_one hd.ne'
    intro p
    dsimp only [d]
    rw [Nat.factorization_ordCompl, Finsupp.erase_apply]
    by_cases hp2 : p = 2
    · simp [hp2]
    · rw [ite_eq_right hp2]
      by_cases hz : q.factorization p = 0
      · simp [hz]
      · have hm : p ∈ q.primeFactors := Finsupp.mem_support_iff.mpr hz
        rw [ho p hm hp2]
  exact ⟨q.factorization 2, d, h2, hd, hodd, hsf,
    (Nat.ordProj_mul_ordCompl_eq_self q 2).symm⟩

theorem twistedSquareSum_support_decomposition (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic)
    (a : ZMod q) (ha : IsUnit a) (hne : twistedSquareSum q χ a ≠ 0) :
    ∃ j d : ℕ, j ≤ 5 ∧ 0 < d ∧ ¬2 ∣ d ∧ Squarefree d ∧ q = 2 ^ j * d := by
  have hs := twistedSquareSum_support q χ hχ a ha hne
  exact oddSquarefree_decomposition_of_factorization q (NeZero.ne q) hs.1 hs.2

/-- Equation e:sqfreeconds, with coprimality to the original level included. -/
theorem twistedSquareSum_conductor_support (q₀ d : ℕ) [NeZero q₀] [NeZero d]
    (χ : DirichletCharacter ℂ (q₀ * d)) (hχ : χ.IsQuadratic)
    (a : ZMod (q₀ * d)) (ha : IsUnit a) (hne : twistedSquareSum (q₀ * d) χ a ≠ 0) :
    ∃ ν d₁ : ℕ, ν ≤ 5 ∧ 0 < d₁ ∧ Squarefree d₁ ∧
      d₁.Coprime (2 * q₀) ∧ d = 2 ^ ν * d₁ := by
  have hs := twistedSquareSum_support (q₀ * d) χ hχ a ha hne
  have hle : d.factorization ≤ (q₀ * d).factorization :=
    Nat.factorization_le_factorization_mul_right (NeZero.ne q₀)
  have hd2 : d.factorization 2 ≤ 5 := (hle 2).trans hs.1
  have hdo : ∀ p ∈ d.primeFactors, p ≠ 2 → d.factorization p = 1 := by
    intro p hp hp2
    have hj : 0 < d.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    have hm : p ∈ (q₀ * d).primeFactors :=
      Finsupp.mem_support_iff.mpr (show (q₀ * d).factorization p ≠ 0 by
        have := hle p
        omega)
    have he := hs.2 p hm hp2
    have := hle p
    omega
  obtain ⟨ν, d₁, hν, hd₁, hodd, hsf, he⟩ :=
    oddSquarefree_decomposition_of_factorization d (NeZero.ne d) hd2 hdo
  have hd₁d : d₁ ∣ d := by rw [he]; exact Nat.dvd_mul_left d₁ (2 ^ ν)
  have hc₂ : d₁.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).symm
  have hc₀ : d₁.Coprime q₀ := by
    apply Nat.coprime_of_dvd
    intro p hp hpd₁ hpq₀
    have hp2 : p ≠ 2 := fun he => hodd (he ▸ hpd₁)
    have hdp : p ^ 2 ∣ q₀ * d := by
      simpa only [pow_two] using Nat.mul_dvd_mul hpq₀ (hpd₁.trans hd₁d)
    exact False.elim (hne (twistedSquareSum_odd_prime_square (q₀ * d) p hp hp2 hdp χ hχ a ha))
  exact ⟨ν, d₁, hν, hd₁, hsf, hc₂.mul_right hc₀, he⟩

/-- The paper's induced real character satisfies all support conclusions. -/
theorem induced_real_twistedSquareSum_support (q₀ d : ℕ) [NeZero q₀] [NeZero d]
    (χ₀ : DirichletCharacter ℂ q₀) (hχ₀ : ∀ r, star (χ₀ r) = χ₀ r)
    (a : ZMod (q₀ * d)) (ha : IsUnit a)
    (hne : twistedSquareSum (q₀ * d)
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ d) χ₀) a ≠ 0) :
    ∃ ν d₁ : ℕ, ν ≤ 5 ∧ 0 < d₁ ∧ Squarefree d₁ ∧
      d₁.Coprime (2 * q₀) ∧ d = 2 ^ ν * d₁ := by
  exact twistedSquareSum_conductor_support q₀ d _
    (quadratic_character_changeLevel _ χ₀ ((dirichletCharacter_quadratic_iff_real q₀ χ₀).mpr hχ₀))
    a ha hne

end PrimeSquares
