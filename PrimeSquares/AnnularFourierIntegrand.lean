import PrimeSquares.SourceArcCutoff
import PrimeSquares.RealFourierPhase
import PrimeSquares.AnnularModelSize
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
namespace PrimeSquares

noncomputable def annularFourierIntegrand (β a x ξ t : ℝ) : ℂ :=
  Complex.ofReal (t^(β-1))*realFourierPhase (ξ*(x-t^2))*Complex.ofReal (sourceArcCutoff (a*ξ))

theorem annularFourierIntegrand_continuousOn {N : ℕ} (hN : 1 ≤ N) (β a x : ℝ) :
    ContinuousOn (Function.uncurry (annularFourierIntegrand β a x))
      (Set.Icc (-(1/2) : ℝ) (1/2) ×ˢ Set.Icc ((N : ℝ)/2) N) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : ContinuousOn (fun p : ℝ × ℝ => Complex.ofReal (p.2^(β-1)))
      (Set.Icc (-(1/2) : ℝ) (1/2) ×ˢ Set.Icc ((N : ℝ)/2) N) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((exceptionalDensity_continuousOn β (by positivity : (0 : ℝ) < (N : ℝ)/2)).comp
        continuous_snd.continuousOn (fun p hp => hp.2))
  have hp : Continuous (fun p : ℝ × ℝ => realFourierPhase (p.1*(x-p.2^2))) :=
    realFourierPhase_continuous.comp (by fun_prop)
  have hc : Continuous (fun p : ℝ × ℝ => Complex.ofReal (sourceArcCutoff (a*p.1))) :=
    Complex.continuous_ofReal.comp (sourceArcCutoff_contDiff.continuous.comp (by fun_prop))
  exact (hd.mul hp.continuousOn).mul hc.continuousOn

theorem annularFourierIntegrand_integrable {N : ℕ} (hN : 1 ≤ N) (β a x : ℝ) :
    Integrable (Function.uncurry (annularFourierIntegrand β a x))
      ((volume.restrict (Set.Ioc (-(1/2) : ℝ) (1/2))).prod
        (volume.restrict (Set.Ioc ((N : ℝ)/2) N))) := by
  rw [Measure.prod_restrict]
  exact (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    (annularFourierIntegrand_continuousOn hN β a x)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

end PrimeSquares
