import PrimeSquares.IndividualDenominatorTail
namespace PrimeSquares
theorem denominator_prefix_not_common_tail :
    ¬∃ (a b : ℂ) (t₀ t₁ : Bool),
      denominatorActivation 2 2=(if t₀ then a else 0) ∧
      denominatorActivation 2 3=(if t₀ then b else 0) ∧
      denominatorActivation 3 2=(if t₁ then a else 0) ∧
      denominatorActivation 3 3=(if t₁ then b else 0) := by
  rintro ⟨a,b,t₀,t₁,ha,hb,hc,hd⟩
  cases t₀ with
  | false => norm_num [denominatorActivation] at ha
  | true =>
    cases t₁ with
    | false => norm_num [denominatorActivation] at hd
    | true =>
      norm_num [denominatorActivation] at ha hb hc hd
      exact zero_ne_one (hb.trans hd.symm)
end PrimeSquares
