import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PassiveAllocationScalarMass

set_option linter.unusedSectionVars false

/-!
# Passive allocation under the original finite row measure

The original second allocation has a genuine row-dependent frozen
residue.  Its exact polynomial identity is retained first.  Its uniform
single-atom bound is then used inside the weighted finite square norm.
The passive expansion uses weighted Minkowski with the same rows and
Fourier parameter.  No common divisor is imposed on the two sides.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

namespace CanonicalLiteralPassiveEnergy

open CanonicalLiteralPassiveSource CanonicalLiteralPassiveDeletion

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (B : ActualColumnAllocation K k)

def canonicalPoint (firstSign : ℝ) (negative : Bool) :
    AllocationColumn K k → WithLp 2 (ℝ × ℝ) :=
  rawSourceLocation
    (fun I => CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.plain firstSign I))
    (fun I => CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.plain firstSign I))
    (fun i p => CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.prime firstSign i p))

def originalFrozenLocation (firstSign : ℝ) (negative : Bool) : WithLp 2 (ℝ × ℝ) :=
  frozenSourceLocation B.keep B.witness.2
    (fun i p => CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.prime firstSign i p))

private theorem joint_scalar {I V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (columns : Finset I) (z : ℂ) (c : I → ℂ) (x : I → V) (ξ : V) :
    jointFourierColumn columns (fun i => z * c i) x ξ =
      z * jointFourierColumn columns c x ξ := by
  sorry

/-- The old allocation scalar contains its entire actual frequency.
The frozen translation has modulus one but is present in this identity. -/
theorem originalColumn_eq_centered (g h : A.R) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    jointFourierColumn B.columns (d.frequencyWhole (σ := σ) g h)
      (canonicalPoint firstSign negative) ξ =
      B.scalar (σ := σ) d.characters g h d.base d.length d.slotWeight *
        jointPhase ξ (originalFrozenLocation B firstSign negative) *
          centeredColumn (σ := σ) (d := d) B (d.characters.restrictSlots B.keep)
            g h firstSign negative ξ := by
  sorry

theorem originalColumn_norm (g h : A.R) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    ‖jointFourierColumn B.columns (d.frequencyWhole (σ := σ) g h)
      (canonicalPoint firstSign negative) ξ‖ =
      ‖B.scalar (σ := σ) d.characters g h d.base d.length d.slotWeight‖ *
        ‖centeredColumn (σ := σ) (d := d) B (d.characters.restrictSlots B.keep)
          g h firstSign negative ξ‖ := by
  sorry

/-- A row-uniform bound on the actual old frozen scalar is used before
the square root.  It is not treated as a constant complex phase. -/
theorem original_sqrt_le_centered {H : Type*} (rows : Finset H)
    (weight : H → ℂ) (g h : H → A.R) (firstSign : ℝ) (negative : Bool)
    (E : ℝ) (hE : 0 ≤ E)
    (hscalar : ∀ j ∈ rows,
      ‖B.scalar (σ := σ) d.characters (g j) (h j) d.base d.length d.slotWeight‖ ^ 2 ≤ E)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    Real.sqrt (jointColumnEnergy rows B.columns weight
      (fun j => d.frequencyWhole (σ := σ) (g j) (h j))
      (fun _ => canonicalPoint firstSign negative) ξ) ≤
      Real.sqrt E * Real.sqrt
        (∑ j ∈ rows, ‖weight j‖ *
          ‖centeredColumn (σ := σ) (d := d) B (d.characters.restrictSlots B.keep)
            (g j) (h j) firstSign negative ξ‖ ^ 2) := by
  sorry

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The required old scalar bound comes from its actual individual
arithmetic factors and frozen profiles.  The original shared divisor
norm remains in the denominator. -/
theorem original_sqrt_le_of_atoms {H : Type*}
    (C : A.GeneralArithmeticContext σ η hS)
    (rows : Finset H) (weight : H → ℂ) (g h : H → A.R)
    (firstSign : ℝ) (negative : Bool) (annulus profile : Fin k → ℝ)
    (hplain₁ : ‖sourcePlainCoefficient d.characters.plain d.characters.plainTwist
      d.characters.mask (B.plainDivisor 0)‖ ≤ 1)
    (hplain₂ : ‖sourcePlainCoefficient d.characters.plain d.characters.plainTwist
      d.characters.mask (B.plainDivisor (Fin.succ 0))‖ ≤ 1)
    (hprime : ∀ i ∈ Finset.univ \ B.keep,
      ‖sourcePrimeCoefficient (d.characters.slot i) (d.characters.slotTwist i)
        d.characters.mask (B.witness.2 i)‖ ≤ 1)
    (hannulus : ∀ i ∈ Finset.univ \ B.keep,
      (Ideal.absNorm (B.witness.2 i).asIdeal : ℝ) ≤ annulus i * d.base ^ d.length i)
    (hprofile : ∀ i ∈ Finset.univ \ B.keep, ‖d.slotWeight i (B.witness.2 i)‖ ^ 2 ≤ profile i)
    (hA : ∀ i, 0 ≤ annulus i) (hP : ∀ i, 0 ≤ profile i)
    (hsquarefree : Squarefree B.divisor)
    (hselection : B.selection ∈ AllocationMass.idealAllocations B.divisor (k + 2))
    (ξ : WithLp 2 (ℝ × ℝ)) :
    Real.sqrt (jointColumnEnergy rows B.columns weight
      (fun j => d.frequencyWhole (σ := σ) (g j) (h j))
      (fun _ => canonicalPoint firstSign negative) ξ) ≤
      Real.sqrt ((∏ i ∈ Finset.univ \ B.keep, annulus i * profile i) /
        (Ideal.absNorm B.divisor : ℝ)) * Real.sqrt
        (∑ j ∈ rows, ‖weight j‖ *
          ‖centeredColumn (σ := σ) (d := d) B (d.characters.restrictSlots B.keep)
            (g j) (h j) firstSign negative ξ‖ ^ 2) := by
  sorry

section PassiveMinkowski

variable (W : d.ProfileData) (T : FixedChildCharacters K B.keep.card)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)

/-- The fixed live label set is separated inside the original finite
row norm.  Its genuine signs cost at most one; no label count is used. -/
theorem sqrt_passiveColumn_le {H : Type*} (rows : Finset H)
    (weight : H → ℂ) (g h : H → A.R) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    Real.sqrt (∑ j ∈ rows, ‖weight j‖ *
      ‖passiveColumn (σ := σ) W B T M (g j) (h j) firstSign negative ξ‖ ^ 2) ≤
      ∑ a ∈ (CanonicalLiteralPassiveSource.labels W B A M).attach,
        Real.sqrt (jointColumnEnergy rows (branch W B A M a).columns weight
          (fun j => (table W B A T).frequencyWhole (σ := σ) (g j) (h j))
          (fun _ => rawSourceLocation (plainLocation₁ B firstSign negative)
            (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)) ξ) := by
  sorry

end PassiveMinkowski
end CanonicalLiteralPassiveEnergy
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveEnergy.originalColumn_eq_centered
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveEnergy.original_sqrt_le_of_atoms
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveEnergy.sqrt_passiveColumn_le
