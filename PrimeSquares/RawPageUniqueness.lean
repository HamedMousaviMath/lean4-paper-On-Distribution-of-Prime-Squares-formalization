import PrimeSquares.SourceInducedCharacters
import PrimeSquares.ThresholdEnvelopeBounds

open Filter Finset Topology
namespace PrimeSquares

/-- A zero below 1 is expressed by ordinary partial sums, rather than an
unconditional `tsum` of a conditionally convergent Dirichlet series. The
analytic bridge to the continued L-function belongs to the raw Page input. -/
def dirichletPartialSumZero {q : ℕ} (χ : DirichletCharacter ℂ q) (β : ℝ) : Prop :=
  Tendsto (fun X : ℕ => ∑ n ∈ Icc 1 X,χ (n : ZMod q)/Complex.ofReal ((n : ℝ)^β)) atTop (𝓝 0)

structure PageZeroDatum where
  conductor : ℕ
  conductor_two : 2 ≤ conductor
  character : DirichletCharacter ℂ conductor
  quadratic : character.IsQuadratic
  primitive : character.IsPrimitive
  nonprincipal : character ≠ 1
  beta : ℝ
  beta_pos : 0<beta
  beta_lt_one : beta<1
  zero : dirichletPartialSumZero character beta

/-- Independent deep number-theoretic boundary: Landau-Page uniqueness for
primitive real characters and their real zeros in its standard logarithmic
region. This definition assumes no operator estimate or paper proposition. -/
def RawPageUniquenessInput (c : ℝ) : Prop :=
  ∀ U : ℝ,2 ≤ U → ∀ D E : PageZeroDatum,
    (D.conductor : ℝ) ≤ U → (E.conductor : ℝ) ≤ U →
    1-c/Real.log U<D.beta → 1-c/Real.log U<E.beta → D=E

def PageConductorEligible (c : ℝ) (D : PageZeroDatum) : Prop :=
  1-(c/2)/Real.log D.conductor<D.beta

theorem page_dyadic_uniqueness {c : ℝ} (hc : 0<c) (hPage : RawPageUniquenessInput c)
    (D E : PageZeroDatum) (hD : PageConductorEligible c D) (hE : PageConductorEligible c E)
    (hbin : Nat.log2 D.conductor=Nat.log2 E.conductor) : D=E := by
  let s := Nat.log2 D.conductor
  let U : ℝ := (2 : ℝ)^(s+1)
  have hD0 : D.conductor ≠ 0 := by have h := D.conductor_two;omega
  have hE0 : E.conductor ≠ 0 := by have h := E.conductor_two;omega
  have hd := (Nat.log2_eq_iff hD0).mp (show Nat.log2 D.conductor=s from rfl)
  have he := (Nat.log2_eq_iff hE0).mp (show Nat.log2 E.conductor=s from hbin.symm)
  have hU : 2 ≤ U := by
    have h : (2 : ℝ)^1 ≤ (2 : ℝ)^(s+1) := pow_le_pow_right₀ (by norm_num) (by omega : 1 ≤ s+1)
    simpa only [pow_one] using h
  have hlu : 0<Real.log U := Real.log_pos (by linarith)
  have hclose (F : PageZeroDatum) (hb : 2^s ≤ F.conductor) (hel : PageConductorEligible c F) :
      1-c/Real.log U<F.beta := by
    have hq2 : (2 : ℝ) ≤ F.conductor := by exact_mod_cast F.conductor_two
    have hq : (0 : ℝ)<F.conductor := by linarith
    have hlq : 0<Real.log F.conductor := Real.log_pos (by linarith)
    have hbase : (2 : ℝ)^s ≤ F.conductor := by exact_mod_cast hb
    have hpow : U ≤ (F.conductor : ℝ)^2 := by
      dsimp [U]
      rw [pow_succ]
      nlinarith
    have hlog : Real.log U ≤ 2*Real.log F.conductor := by
      have h := Real.log_le_log (by linarith : 0<U) hpow
      simpa only [Real.log_pow,Nat.cast_ofNat] using h
    have hdiv : (c/2)/Real.log F.conductor ≤ c/Real.log U := by
      rw [div_div]
      exact div_le_div_of_nonneg_left hc.le hlu hlog
    exact lt_of_le_of_lt (by linarith) hel
  exact hPage U hU D E (by dsimp [U];exact_mod_cast hd.2.le) (by dsimp [U];exact_mod_cast he.2.le)
    (hclose D hd.1 hD) (hclose E he.1 hE)

theorem page_source_region_eligible {c R : ℝ} (hc : 0<c) (D : PageZeroDatum)
    (hR : (D.conductor : ℝ) ≤ R) (hbeta : 1-(c/2)/Real.log R<D.beta) :
    PageConductorEligible c D := by
  have hq : (1 : ℝ)<D.conductor := by exact_mod_cast (by have h := D.conductor_two;omega : 1<D.conductor)
  have hlq : 0<Real.log D.conductor := Real.log_pos hq
  have hl := Real.log_le_log (by linarith : (0 : ℝ)<D.conductor) hR
  have hdiv := div_le_div_of_nonneg_left (show 0 ≤ c/2 by positivity) hlq hl
  change 1-(c/2)/Real.log D.conductor<D.beta
  exact lt_of_le_of_lt (by linarith) hbeta

end PrimeSquares
