import PrimeSquares.ExceptionalDenominatorSet

open Finset
namespace PrimeSquares

theorem conductor_multiple_reindex {A : Type*} [AddCommMonoid A] {q₀ M : ℕ} (hq₀ : 0 < q₀)
    (Q : ℝ) (F : ℕ → A) :
    (∑ q ∈ (Icc 1 M).filter (fun q => q₀ ∣ q ∧ conductorMajorant q₀*((q/q₀ : ℕ) : ℝ) ≤ Q),F q)=
      ∑ d ∈ realExceptionalDenominators q₀ M Q,F (q₀*d) := by
  classical
  apply sum_bij (fun q _ => q/q₀)
  · intro q hq
    obtain ⟨hqM,hd,hw⟩ := mem_filter.mp hq
    have hp := conductor_quotient_positive hq₀ (mem_Icc.mp hqM).1 hd
    rw [mem_realExceptionalDenominators hq₀]
    exact ⟨hp,hw,by rw [Nat.mul_div_cancel' hd];exact (mem_Icc.mp hqM).2⟩
  · intro q hq t ht he
    have hqdiv := (mem_filter.mp hq).2.1
    have htdiv := (mem_filter.mp ht).2.1
    have hh := congrArg (fun d : ℕ => q₀*d) he
    simpa only [Nat.mul_div_cancel' hqdiv,Nat.mul_div_cancel' htdiv] using hh
  · intro d hd
    obtain ⟨hd1,hw,hM⟩ := (mem_realExceptionalDenominators hq₀ Q).mp hd
    have he : q₀*d/q₀=d := Nat.mul_div_cancel_left d hq₀
    refine ⟨q₀*d,mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith,hM⟩,Nat.dvd_mul_right q₀ d,?_⟩,he⟩
    simpa only [he] using hw
  · intro q hq
    have hd := (mem_filter.mp hq).2.1
    rw [Nat.mul_div_cancel' hd]

end PrimeSquares
