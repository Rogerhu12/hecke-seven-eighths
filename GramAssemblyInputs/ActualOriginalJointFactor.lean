import ActualSIntegerDivisorColumn
import HeckeGeneral.Analysis.SUnitMellinPhase

/-! The original non-cutoff joint factor, extracted without changing its
namespace, arguments or definition from ActualClearedJointPeriodicTransport.
This provider needs no cleared-lattice transport or all-scale estimate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.Analysis.ActualClearedJointPeriodicDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open ActualGramJointChartDraft
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Z" => SFiniteLocalGroup K S

variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)

/-- The literal non-cutoff factor used in the original annular summand. -/
def originalJointFactor (d : NZ) (ν : ℝ) (z₁ z₂ : Z) (φ : SchwartzMap V ℂ)
    (R : {r : ℝ // 0 < r}) (r : ℝ) (m : NZ × NZ) : ℂ :=
  let p := (r⁻¹ • traceEmbedding K ((divisorColumn K S d m.1).val : K),
    r⁻¹ • traceEmbedding K ((divisorColumn K S d m.2).val : K))
  sUnitMellinPhase K S ν z₁ z₂ p * traceJointOrbitalKernel K S φ ψ R p

end HeckeGeneral.Analysis.ActualClearedJointPeriodicDraft
