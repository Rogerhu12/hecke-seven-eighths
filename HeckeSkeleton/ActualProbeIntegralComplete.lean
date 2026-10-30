import HeckeSkeleton.ActualProbeIntegralAssembly
import HeckeSkeleton.ActualProbeThetaAbsolute

/-!
# All five original probe integral fields

UNCOMPILED candidate. This constructs the original ProbeIntegralInput for
arbitrary actual ProbeData and Hecke character, with no extra mathematical
premise. It asserts only the five fields of that structure, not a global
theta reflection, Poisson identity, or physical-probe lower bound.
-/

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]

theorem actual_probeIntegralInput (P : ProbeData K S) (ψ : HeckeCharacter K) :
    ProbeIntegralInput K S P ψ :=
  ProbeIntegralInput.of_analytic_inputs K S P ψ
    (ActualThetaAbsoluteDraft.actual_probeTheta_absolute K S P ψ)

end HeckeGeneral.ThetaSkeleton.Physical
