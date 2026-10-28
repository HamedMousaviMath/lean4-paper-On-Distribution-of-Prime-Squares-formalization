import PrimeSquares.GoldbachArithmeticDecay

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_source_arithmetic_coefficient_sum (N q : ℕ) [NeZero q] (hN : 1≤N)
    (hlog : 1≤Real.log N) (L B : ℝ) (V : ℕ→ℝ) (hB : 0≤B) (hL : L≤(N:ℝ)^2)
    (hV : ∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L →
      V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B))
    (b : ℕ×ℕ→ℤ) (hb : ∀ i∈goldbachCoefficientIndices L V,IsCoprime (i.2:ℤ) (b i)) (n : ℤ) :
    (∑ i∈goldbachCoefficientIndices L V,
      ‖generalCoefficient q i.2 (i.1:ℤ) (b i) n‖/((i.1:ℝ)*(i.2.totient:ℝ)))≤
        (9*Real.exp 2)*(q.divisors.card:ℝ)^11/(q:ℝ)*(Real.log N)^2 := by
  let T := (q.divisors.card:ℝ)^9/(q:ℝ)
  calc
    _≤∑ i∈goldbachCoefficientIndices L V,T*
        ((q.gcd (i.1*i.2):ℝ)/((i.1:ℝ)*(i.2.totient:ℝ))) := by
      apply sum_le_sum
      intro i hi
      have hk := ((mem_goldbachCoefficientIndices L V i.1 i.2).mp hi).2.2.1
      have : NeZero i.2 := ⟨hk.ne'⟩
      have hh := goldbach_general_coefficient_divisor_bound q i.2 i.1 (b i) n (hb i hi)
      rw [Nat.mul_comm i.2 i.1] at hh
      apply (div_le_div_of_nonneg_right hh (show 0≤(i.1:ℝ)*(i.2.totient:ℝ) by positivity)).trans_eq
      dsimp only [T]
      ring
    _=T*(∑ i∈goldbachCoefficientIndices L V,
        (q.gcd (i.1*i.2):ℝ)/((i.1:ℝ)*(i.2.totient:ℝ))) := (mul_sum _ _ _).symm
    _≤T*((9*Real.exp 2)*(q.divisors.card:ℝ)^2*(Real.log N)^2) :=
      mul_le_mul_of_nonneg_left (goldbach_source_arithmetic_harmonic N q hN (NeZero.pos q)
        hlog L B V hB hL hV) (by dsimp only [T];positivity)
    _=_ := by dsimp only [T];ring

theorem goldbach_source_finite_arithmetic_tail (N : ℕ) (hN : 1≤N)
    (hlog : 1≤Real.log N) (L B : ℝ) (V : ℕ→ℝ) (hB : 0≤B) (hL : L≤(N:ℝ)^2)
    (hV : ∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L →
      V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B))
    (b : ℕ×ℕ→ℤ) (hb : ∀ i∈goldbachCoefficientIndices L V,IsCoprime (i.2:ℤ) (b i))
    (d H : ℕ×ℕ→ℂ) (hd : ∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1)
    {M : ℝ} (hM : 0≤M) (hH : ∀ i∈goldbachCoefficientIndices L V,‖H i‖≤M)
    (S : Finset ℕ) (hS : ∀ q∈S,0<q) (n : ℤ) :
    ‖∑ i∈goldbachCoefficientIndices L V,(d i*H i)/((i.1:ℂ)*(i.2.totient:ℂ))*
      (∑ q∈S,generalCoefficient q i.2 (i.1:ℤ) (b i) n)‖≤
      (9*Real.exp 2)*M*(Real.log N)^2*(∑ q∈S,(q.divisors.card:ℝ)^11/(q:ℝ)) := by
  have he : (∑ i∈goldbachCoefficientIndices L V,(d i*H i)/((i.1:ℂ)*(i.2.totient:ℂ))*
      (∑ q∈S,generalCoefficient q i.2 (i.1:ℤ) (b i) n))=
      ∑ q∈S,∑ i∈goldbachCoefficientIndices L V,
        (d i*H i)/((i.1:ℂ)*(i.2.totient:ℂ))*generalCoefficient q i.2 (i.1:ℤ) (b i) n := by
    simp_rw [mul_sum]
    exact sum_comm
  rw [he]
  calc
    _≤∑ q∈S,‖∑ i∈goldbachCoefficientIndices L V,
        (d i*H i)/((i.1:ℂ)*(i.2.totient:ℂ))*generalCoefficient q i.2 (i.1:ℤ) (b i) n‖ := norm_sum_le _ _
    _≤∑ q∈S,M*((9*Real.exp 2)*(q.divisors.card:ℝ)^11/(q:ℝ)*(Real.log N)^2) := by
      apply sum_le_sum
      intro q hq
      have : NeZero q := ⟨(hS q hq).ne'⟩
      calc
        _≤∑ i∈goldbachCoefficientIndices L V,
            ‖(d i*H i)/((i.1:ℂ)*(i.2.totient:ℂ))*generalCoefficient q i.2 (i.1:ℤ) (b i) n‖ := norm_sum_le _ _
        _≤∑ i∈goldbachCoefficientIndices L V,M*
            (‖generalCoefficient q i.2 (i.1:ℤ) (b i) n‖/((i.1:ℝ)*(i.2.totient:ℝ))) := by
          apply sum_le_sum
          intro i hi
          rw [norm_mul,norm_div,norm_mul,norm_mul,Complex.norm_natCast,Complex.norm_natCast]
          have hh := mul_le_mul (hd i hi) (hH i hi) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
          apply (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hh
            (show 0≤(i.1:ℝ)*(i.2.totient:ℝ) by positivity)) (norm_nonneg _)).trans_eq
          ring
        _=M*(∑ i∈goldbachCoefficientIndices L V,
            ‖generalCoefficient q i.2 (i.1:ℤ) (b i) n‖/((i.1:ℝ)*(i.2.totient:ℝ))) := (mul_sum _ _ _).symm
        _≤_ := mul_le_mul_of_nonneg_left (goldbach_source_arithmetic_coefficient_sum N q hN
          hlog L B V hB hL hV b hb n) hM
    _=_ := by rw [mul_sum];apply sum_congr rfl;intro q _;ring

end PrimeSquares
