import HeckeAxiom.ProbeTestChoice
import HeckeAxiom.ProbeNormalization
import HeckeAxiom.LambdaInfinityType
import HeckeAxiom.SexticSymbolDictionary
import HeckeAxiom.GaussCalibration
import HeckeSkeleton.AllowedGeneratorNorm

/-!
# The actual arithmetic choice supplies the physical probe inputs

This module has no dependency on `HeckeSkeleton.Base`.  Its probe uses the
same arithmetic choice and the same `Classical.choose exists_probeTest`
term as Base.  The local measures are the given self-dual measures at
every finite place, so restricting them to the chosen finite set is
definitionally the existing `selfDualProbeMeasures` family.

Allowed generators, arithmetic calibration, the zero Fourier value and
the nonzero residue normalization are proved here from that choice.  No
analytic bound or conclusion of the expansion is a structure field.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.ActualProbeContext

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

/-- The canonical Borel structure used by the self-dual local measure. -/
def localCompletionSpace (p : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (p.adicCompletion K) := borel _

attribute [local instance] localCompletionSpace

def localCompletionBorel (p : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (p.adicCompletion K) := ⟨rfl⟩

attribute [local instance] localCompletionBorel

/-- The same self-dual measure at all finite places; no extension is
chosen independently outside the arithmetic set. -/
def allLocalMeasures (p : HeightOneSpectrum (𝓞 K)) :
    Measure (p.adicCompletion K) :=
  DedekindZetaZeroFree.localNormalizedHaar K p

theorem allLocalMeasures_isAddHaar (p : HeightOneSpectrum (𝓞 K)) :
    (allLocalMeasures K p).IsAddHaarMeasure :=
  DedekindZetaZeroFree.localNormalizedHaar_isAddHaarMeasure K p

attribute [local instance] allLocalMeasures_isAddHaar

/-- The auxiliary finite adelic measure only discharges the proved
Fourier regularity interfaces; the physical kernel uses the local family. -/
def finiteAdeleSpace : MeasurableSpace (FiniteAdeleRing (𝓞 K) K) := borel _

attribute [local instance] finiteAdeleSpace

def finiteAdeleBorel : BorelSpace (FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩

attribute [local instance] finiteAdeleBorel

def finiteAdeleMeasure : Measure (FiniteAdeleRing (𝓞 K) K) := Measure.addHaar

theorem finiteAdeleMeasure_isAddHaar : (finiteAdeleMeasure K).IsAddHaarMeasure := by
  unfold finiteAdeleMeasure
  infer_instance

attribute [local instance] finiteAdeleMeasure_isAddHaar

/-- The full adelic Haar measure is another auxiliary measure for the
proved Poisson identity.  It does not replace the physical local family. -/
def adeleSpace : MeasurableSpace (AdeleRing (𝓞 K) K) := borel _

attribute [local instance] adeleSpace

def adeleBorel : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩

attribute [local instance] adeleBorel

def adeleMeasure : Measure (AdeleRing (𝓞 K) K) := Measure.addHaar

theorem adeleMeasure_isAddHaar : (adeleMeasure K).IsAddHaarMeasure := by
  unfold adeleMeasure
  infer_instance

attribute [local instance] adeleMeasure_isAddHaar

variable {initial : Finset (HeightOneSpectrum (𝓞 K))} {root12 : K} {embedding : K →+* ℂ}
variable (X : HeckeAxiom.ArithmeticChoice K initial root12 embedding)

/-- This is definitionally Base's probe for its existing arithmetic
choice, including its one fixed additive test. -/
def selectedProbe : ProbeData K (X.places : Set (HeightOneSpectrum (𝓞 K))) where
  arithmetic := X.thetaData
  Lambda := X.Lambda
  G := X.G
  additive := Classical.choose (HeckeAxiom.ProbeTestChoice.exists_probeTest X.A X.hS)
  denominator := HeckeAxiom.denominatorTest DedekindZetaZeroFree.probeRealBumpWeight

local notation "S" => (X.places : Set (HeightOneSpectrum (𝓞 K)))
local notation "P" => selectedProbe K X
local notation "muS" => (fun p : S => allLocalMeasures K (Subtype.val p))

def normOneSpace : MeasurableSpace (sLocalNormOneGroup K S) := borel _

attribute [local instance] normOneSpace

def normOneBorel : BorelSpace (sLocalNormOneGroup K S) := ⟨rfl⟩

attribute [local instance] normOneBorel

/-- Restriction to the chosen places is the original physical measure
family, with the same Borel structures. -/
theorem allLocalMeasures_restrict :
    muS = (HeckeAxiom.selfDualProbeMeasures K S).haar := rfl

include X in
theorem totallyComplex : IsTotallyComplex K :=
  DedekindZetaZeroFree.primitive12_totallyComplex K X.A.zeta12 X.A.primitive_zeta12

include X in
theorem isComplex (v : InfinitePlace K) : v.IsComplex := by
  letI : IsTotallyComplex K := totallyComplex K X
  exact IsTotallyComplex.isComplex v

theorem allowedGenerators : AllowedGeneratorInput K S (P).arithmetic :=
  AllowedGeneratorInput.of_multiplicative_reciprocity K S X.thetaData
    X.thetaData_multiplicative X.idealSymbol_reciprocity

theorem arithmeticCalibration : ThetaCalibrationInput K S (P).arithmetic (P).Lambda (P).G where
  lambda_unramified := X.Lambda_unramified
  G_unramified := X.G_unramified
  G_finite_order := X.G_finiteOrder
  lambda_angular := X.Lambda_weight
  lambda_radial_zero := X.Lambda_parameter
  cube_calibration := X.cube_calibration
  mixed_calibration := X.mixed_calibration

theorem fourier_zero : additiveFourierAtZero K S muS (P).additive = 0 :=
  (Classical.choose_spec (HeckeAxiom.ProbeTestChoice.exists_probeTest X.A X.hS)).1

theorem mellin_positive :
    (additiveMellin K S muS (P).additive (1 / 6)).im = 0 ∧
      0 < (additiveMellin K S muS (P).additive (1 / 6)).re :=
  (Classical.choose_spec (HeckeAxiom.ProbeTestChoice.exists_probeTest X.A X.hS)).2

theorem normalizer_positive :
    (physicalResidueNormalizer K S muS P).im = 0 ∧
      0 < (physicalResidueNormalizer K S muS P).re :=
  HeckeAxiom.ProbeNormalization.physicalResidueNormalizer_pos S muS P
    DedekindZetaZeroFree.probeRealBumpWeight rfl (mellin_positive K X).1
    (mellin_positive K X).2

theorem normalizer_ne_zero : physicalResidueNormalizer K S muS P ≠ 0 :=
  Complex.ne_zero_of_re_pos (normalizer_positive K X).2

end Expansion.ActualProbeContext

#print axioms Expansion.ActualProbeContext.selectedProbe
#print axioms Expansion.ActualProbeContext.allowedGenerators
#print axioms Expansion.ActualProbeContext.arithmeticCalibration
#print axioms Expansion.ActualProbeContext.fourier_zero
#print axioms Expansion.ActualProbeContext.normalizer_ne_zero
