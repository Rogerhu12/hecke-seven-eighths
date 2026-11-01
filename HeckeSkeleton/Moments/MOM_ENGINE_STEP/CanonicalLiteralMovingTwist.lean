import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExtraction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFixedPhases

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
  have hout := (CanonicalOriginalPhaseCalibration.outside_iff_coprime J).mpr hJ
  have he := CanonicalLiteralFirstPhase.multiply_singleton_residue
    P R hroot hemb I a ha T.plain J
  simp only [hout, true_and] at he
  change heckeIdealCoefficient K _ J * heckeIdealCoefficient K T.plainTwist J *
      (T.mask J.val * (if IsCoprime J.val I.val then 1 else 0)) =
    (heckeIdealCoefficient K T.plain J * heckeIdealCoefficient K T.plainTwist J *
      T.mask J.val) * actualIdealResidue (A := A) (σ := σ) J.val a
  calc
    _ = (heckeIdealCoefficient K _ J * (if IsCoprime J.val I.val then 1 else 0)) *
        heckeIdealCoefficient K T.plainTwist J * T.mask J.val := by ring
    _ = _ := by rw [← he]; ring

theorem movingSingleton_prime
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (j : Fin k) (p : HeightOneSpectrum (𝓞 K)) (hp : IsCoprime p.asIdeal A.cS) :
    sourcePrimeCoefficient ((T.movingSingleton P R I a ha).slot j)
        ((T.movingSingleton P R I a ha).slotTwist j)
        (T.movingSingleton P R I a ha).mask p =
      sourcePrimeCoefficient (T.slot j) (T.slotTwist j) T.mask p *
        actualIdealResidue (A := A) (σ := σ) p.asIdeal a := by
  have hout := (CanonicalOriginalPhaseCalibration.outside_iff_coprime
    (CanonicalOriginalPhaseCalibration.primeIdeal p)).mpr hp
  have he := CanonicalLiteralFirstPhase.multiply_singleton_residue
    P R hroot hemb I a ha (T.slot j) (CanonicalOriginalPhaseCalibration.primeIdeal p)
  simp only [CanonicalOriginalPhaseCalibration.coefficient_prime, hout, true_and] at he
  change primeCoefficient K _ p * primeCoefficient K (T.slotTwist j) p *
      (T.mask p.asIdeal * (if IsCoprime p.asIdeal I.val then 1 else 0)) =
    (primeCoefficient K (T.slot j) p * primeCoefficient K (T.slotTwist j) p *
      T.mask p.asIdeal) * actualIdealResidue (A := A) (σ := σ) p.asIdeal a
  calc
    _ = (primeCoefficient K _ p * (if IsCoprime p.asIdeal I.val then 1 else 0)) *
        primeCoefficient K (T.slotTwist j) p * T.mask p.asIdeal := by ring
    _ = _ := by rw [← he]; ring

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
  have hn : allocationColumnIdeal i ≠ 0 := hJ ▸ J.property.1
  have h₁ : i.1.1 ≠ 0 := by
    intro hz
    apply hn
    simp only [allocationColumnIdeal, hz, zero_mul]
  have h₂ : i.1.2 ≠ 0 := by
    intro hz
    apply hn
    simp only [allocationColumnIdeal, hz, mul_zero, zero_mul]
  have hc : IsCoprime (allocationColumnIdeal i) A.cS :=
    hJ ▸ Ideal.isCoprime_iff_sup_eq.mpr J.property.2
  have hparts : (IsCoprime i.1.1 A.cS ∧ IsCoprime i.1.2 A.cS) ∧
      ∀ j, IsCoprime (i.2 j).asIdeal A.cS := by
    simpa only [allocationColumnIdeal, IsCoprime.mul_left_iff,
      IsCoprime.prod_left_iff, Finset.mem_univ, forall_const] using hc
  have hp₁ := T.movingSingleton_plain P R hroot hemb I a ha
    (sourceMomentIdeal i.1.1) (by
      simpa only [sourceMomentIdeal_val_of_ne_zero _ h₁] using hparts.1.1)
  have hp₂ := T.movingSingleton_plain P R hroot hemb I a ha
    (sourceMomentIdeal i.1.2) (by
      simpa only [sourceMomentIdeal_val_of_ne_zero _ h₂] using hparts.1.2)
  have hs (j : Fin k) := T.movingSingleton_prime P R hroot hemb I a ha j (i.2 j) (hparts.2 j)
  simp only [rawBareSourceCoefficient, FixedChildCharacters.bareCoefficient,
    childCartesianCoefficient, hp₁, hp₂]
  simp_rw [hs]
  simp only [sourceMomentIdeal_val_of_ne_zero _ h₁,
    sourceMomentIdeal_val_of_ne_zero _ h₂, hJ, allocationColumnIdeal,
    actualIdealResidue_ideal_mul, actualIdealResidue_prod, Finset.prod_mul_distrib]
  ring

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
  change d.normalizer *
      rawBareSourceCoefficient (d.characters.movingSingleton P R I a ha)
        (d.scale₁ r) (d.scale₂ r) d.base d.length
        (d.rectangleLeftWeight r) (d.rightWeight r) d.slotWeight i = _
  rw [d.characters.movingSingleton_bare P R hroot hemb I a ha
    (d.scale₁ r) (d.scale₂ r) d.base d.length
    (d.rectangleLeftWeight r) (d.rightWeight r) d.slotWeight i J hJ]
  change _ = (d.normalizer * _) * _
  ring

theorem movingSingleton_whole
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (i : AllocationColumn K k) (J : A.Exterior)
    (hJ : J.val = allocationColumnIdeal i) :
    (d.movingSingleton P R I a ha).whole i =
      d.whole i * actualIdealResidue (A := A) (σ := σ) J.val a := by
  unfold whole
  rw [d.movingSingleton_term P R hroot hemb I a ha false i J hJ,
    d.movingSingleton_term P R hroot hemb I a ha true i J hJ]
  ring

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FixedChildCharacters.movingSingleton_bare
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.movingSingleton_whole
