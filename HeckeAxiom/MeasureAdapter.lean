import HeckeGeneral.Analysis.TIPSources
import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalDifferentNormalization

/-!
# Self-dual local Haar measures as the skeleton's probe measures

The skeleton's `ProbeMeasures` asks for Borel structures on the norm-one group
and on the local completions, and an additive Haar measure at each place of
`S`. Axiom's `localNormalizedHaar` is the Borel Haar measure giving the local
integers volume `N(𝔇_v)^(-1/2)`: the measure self-dual for the standard local
trace character, which is the skeleton's `psiLocal` by the trace character
dictionary.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.ThetaSkeleton.TIP

variable (K : Type) [Field K] [NumberField K]

/-- Borel structures and the self-dual local Haar measures on the places of `S`. -/
def selfDualProbeMeasures (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] :
    ProbeMeasures K S where
  normOneSpace := borel _
  normOneBorel := @BorelSpace.mk _ _ (borel _) rfl
  localSpace _ := borel _
  localBorel _ := @BorelSpace.mk _ _ (borel _) rfl
  haar p := DedekindZetaZeroFree.localNormalizedHaar K p.val
  haar_isAddHaar p := DedekindZetaZeroFree.localNormalizedHaar_isAddHaarMeasure K p.val

/-- The local integers have volume `N(𝔇_v)^(-1/2)`. -/
theorem selfDualProbeMeasures_integers (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (p : S) :
    (selfDualProbeMeasures K S).haar p (p.val.adicCompletionIntegers K : Set (p.val.adicCompletion K)) =
      ENNReal.ofReal (DedekindZetaZeroFree.localHalfDifferentFactor K p.val) :=
  DedekindZetaZeroFree.localNormalizedHaar_integerRing K p.val

end HeckeAxiom
