import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExtraction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFixedPhases

set_option linter.unusedSectionVars false

/-!
# The actual fixed source phase enters every original arithmetic atom

The fixed first divisor phase, amplifier phase and chosen empty-mask
unit phase are represented by their actual generated elements. This
file transports any such original element through every plain and
prime occurrence. Its genuine singleton moving character and complete
coprimality mask are computed; ramified background zeros are preserved.

The source support, norm profiles, comparison scales and extra Gauss
scales are unchanged. The complete centered coefficient acquires the
original residue factor by a proved finite product identity.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {k : ℕ}

namespace FixedChildCharacters

variable (T : FixedChildCharacters K k)

/-- This is a fixed moving factor, not an additional theta character.
The original finite-ray dictionary is retained verbatim. -/
def movingSingleton (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    FixedChildCharacters K k :=
  { T with
    plain := T.plain * (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).character
    slot := fun j => T.slot j *
      (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).character
    mask := T.mask * CanonicalOriginalPhaseCalibration.originalCoprimeMask
      (exteriorMomentIdeal I) }

theorem movingSingleton_plain
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) (hJ : IsCoprime J.val A.cS) :
    sourcePlainCoefficient (T.movingSingleton P R I a ha).plain
        (T.movingSingleton P R I a ha).plainTwist (T.movingSingleton P R I a ha).mask J =
      sourcePlainCoefficient T.plain T.plainTwist T.mask J *
        actualIdealResidue (A := A) (σ := σ) J.val a := by
  sorry

theorem movingSingleton_prime
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (j : Fin k) (p : HeightOneSpectrum (𝓞 K)) (hp : IsCoprime p.asIdeal A.cS) :
    sourcePrimeCoefficient ((T.movingSingleton P R I a ha).slot j)
        ((T.movingSingleton P R I a ha).slotTwist j)
        (T.movingSingleton P R I a ha).mask p =
      sourcePrimeCoefficient (T.slot j) (T.slotTwist j) T.mask p *
        actualIdealResidue (A := A) (σ := σ) p.asIdeal a := by
  sorry

/-- Multiplicativity is applied to the actual complete ideal product.
The exterior condition at that product proves the required condition at
each of its original occurrences. -/
theorem movingSingleton_bare
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) (J : A.Exterior)
    (hJ : J.val = allocationColumnIdeal i) :
    rawBareSourceCoefficient (T.movingSingleton P R I a ha)
        N₁ N₂ Z length w₁ w₂ w i =
      rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w i *
        actualIdealResidue (A := A) (σ := σ) J.val a := by
  sorry

@[simp] theorem movingSingleton_restrictSlots
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) (keep : Finset (Fin k)) :
    (T.movingSingleton P R I a ha).restrictSlots keep =
      (T.restrictSlots keep).movingSingleton P R I a ha := rfl

end FixedChildCharacters

namespace CanonicalLiteralRectangles.Atoms

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)

def movingSingleton (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    CanonicalLiteralRectangles.Atoms (K := K) k :=
  { d with characters := d.characters.movingSingleton P R I a ha }

theorem movingSingleton_term
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (r : Bool) (i : AllocationColumn K k) (J : A.Exterior)
    (hJ : J.val = allocationColumnIdeal i) :
    (d.movingSingleton P R I a ha).term r i =
      d.term r i * actualIdealResidue (A := A) (σ := σ) J.val a := by
  sorry

theorem movingSingleton_whole
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (i : AllocationColumn K k) (J : A.Exterior)
    (hJ : J.val = allocationColumnIdeal i) :
    (d.movingSingleton P R I a ha).whole i =
      d.whole i * actualIdealResidue (A := A) (σ := σ) J.val a := by
  sorry

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FixedChildCharacters.movingSingleton_bare
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.movingSingleton_whole
