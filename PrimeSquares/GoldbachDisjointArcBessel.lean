import PrimeSquares.GoldbachArcLiftIntegral
import PrimeSquares.FiniteDisjointSquareEnergy

set_option autoImplicit false
open Finset MeasureTheory
open scoped ENNReal
namespace PrimeSquares

theorem goldbach_arc_lifts_disjoint {Y ε : ℝ} (hY : 1≤Y)
    (hε : 2*ε<1/Y^2) {r s : ℚ} (hr : r∈sourceRationalCenters Y)
    (hs : s∈sourceRationalCenters Y) (hrs : r≠s) (f g : ℝ→ℂ)
    (hf : ∀ x : ℝ,f x≠0 →|x|≤ε) (hg : ∀ x : ℝ,g x≠0 →|x|≤ε) (θ : PrimeCircle) :
    goldbachArcLift r f θ=0 ∨ goldbachArcLift s g θ=0 := by
  by_cases hfr : goldbachArcLift r f θ=0
  · exact Or.inl hfr
  by_cases hgs : goldbachArcLift s g θ=0
  · exact Or.inr hgs
  exfalso
  have hdistR : dist θ ((r:ℝ):PrimeCircle)≤ε := by
    rw [←goldbachArcCoordinate_abs]
    exact hf _ hfr
  have hdistS : dist θ ((s:ℝ):PrimeCircle)≤ε := by
    rw [←goldbachArcCoordinate_abs]
    exact hg _ hgs
  obtain ⟨ξ,rfl⟩ := Quotient.exists_rep θ
  obtain ⟨k,hk⟩ := (goldbach_circle_ball_real_lift (r:ℝ) ξ ε).mp hdistR
  obtain ⟨l,hl⟩ := (goldbach_circle_ball_real_lift (s:ℝ) ξ ε).mp hdistS
  have hr' := (mem_sourceRationalCenters (by linarith : 0≤Y) r).mp hr
  have hs' := (mem_sourceRationalCenters (by linarith : 0≤Y) s).mp hs
  exact hrs (canonicalLift_small_arc_unique hr'.1 hs'.1 hr'.2 hs'.2 hε hk hl).1

theorem goldbach_disjoint_arc_bessel (S : Finset ℚ) (T : Finset ℤ) (f : ℚ→ℝ→ℂ)
    (hhalf : ∀ r∈S,∀ x : ℝ,(1/2:ℝ)≤|x| →f r x=0)
    (hLp : ∀ r∈S,MemLp (goldbachArcLift r (f r)) 2 AddCircle.haarAddCircle)
    (hdisj : ∀ r∈S,∀ s∈S,r≠s →∀ θ : PrimeCircle,
      goldbachArcLift r (f r) θ=0 ∨ goldbachArcLift s (f s) θ=0) :
    (∑ n∈T,‖∑ r∈S,realFourierPhase (-(n:ℝ)*(r:ℝ))*
      (∫ γ : ℝ,f r γ*realFourierPhase (-(n:ℝ)*γ))‖^2)≤
        ∑ r∈S,∫ γ : ℝ,‖f r γ‖^2 := by
  classical
  let G := fun θ : PrimeCircle=>∑ r∈S,goldbachArcLift r (f r) θ
  have hG : MemLp G 2 AddCircle.haarAddCircle := memLp_finsetSum S hLp
  have he (θ : PrimeCircle) : ‖G θ‖^2=∑ r∈S,‖goldbachArcLift r (f r) θ‖^2 := by
    apply norm_sum_square_single_support S
    intro r hr s hs hrf hsf
    by_contra hne
    exact (hdisj r hr s hs hne θ).elim hrf hsf
  have henergy : (∫ θ : PrimeCircle,‖G θ‖^2 ∂AddCircle.haarAddCircle)=
      ∑ r∈S,∫ γ : ℝ,‖f r γ‖^2 := by
    simp only [he]
    rw [integral_finsetSum S (fun r hr=>(hLp r hr).integrable_norm_pow (by decide : 2≠0))]
    apply sum_congr rfl
    intro r hr
    exact goldbach_arc_lift_energy r (f r) (hhalf r hr)
  have hcoeff (n : ℤ) : (∫ θ : PrimeCircle,G θ*fourier (-n) θ ∂AddCircle.haarAddCircle)=
      ∑ r∈S,realFourierPhase (-(n:ℝ)*(r:ℝ))*(∫ γ : ℝ,f r γ*realFourierPhase (-(n:ℝ)*γ)) := by
    have hchar : MemLp ((fourier (-n)) : PrimeCircle→ℂ) ∞ AddCircle.haarAddCircle :=
      ContinuousMap.memLp AddCircle.haarAddCircle ℂ _
    have hi (r : ℚ) (hr : r∈S) : Integrable
        (fun θ : PrimeCircle=>goldbachArcLift r (f r) θ*fourier (-n) θ) AddCircle.haarAddCircle :=
      ((hLp r hr).mul hchar).integrable (by norm_num : (1:ℝ≥0∞)≤2)
    simp only [G,sum_mul]
    rw [integral_finsetSum S hi]
    apply sum_congr rfl
    intro r hr
    exact goldbach_arc_lift_fourier_integral r (f r) (hhalf r hr) n
  have hb := goldbach_restricted_function_bessel T Set.univ MeasurableSet.univ G hG
  simp only [Measure.restrict_univ] at hb
  calc
    _=(∑ n∈T,‖∫ θ : PrimeCircle,G θ*fourier (-n) θ ∂AddCircle.haarAddCircle‖^2) := by
      simp only [hcoeff]
    _≤∫ θ : PrimeCircle,‖G θ‖^2 ∂AddCircle.haarAddCircle := hb
    _=_ := henergy

end PrimeSquares
