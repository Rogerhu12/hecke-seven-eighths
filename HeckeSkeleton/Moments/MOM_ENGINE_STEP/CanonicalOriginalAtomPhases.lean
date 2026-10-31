import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CompleteOriginalArithmeticAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentColumnPhaseBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPhaseCalibration

/-!
# The same original probe supplies every periodic parent atom phase

The independent fixed-twist arithmetic construction is adapted from
commit 9038540ea50cfbba2639780d86981b8543f9c2bb. Its actual phase
dictionary is stated for the original arithmetic data, with only the
literal root and embedding identities. These are reflexive for the
same ArithmeticChoice, by chosenProbe_phase_fields.

Every original quotient element is covered, including the nonunit
zeros. The moving character stays in the fixed arithmetic coefficient;
the complete row and the actual orbital phase are unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}

/-- The original actual orbital evaluation equals the full original
residue phase on every quotient, not only on the row-map image. -/
theorem actualProbeOrbitSexticEvaluation_eq_actualIdealResidue
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ) (I : NonzeroIdeal K)
    (q : ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) :
    actualOrbitSexticEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding I q =
      actualIdealResidue (A := A) (σ := σ) I.val q.out.val := by
  rw [← actualOrbitSexticEvaluation_out]
  exact (CanonicalOriginalPhaseCalibration.residue_eq_probe_evaluation
    P hroot hemb I q.out.val).symm

/-- Original per-ideal and per-prime phase dictionaries, constructed
without a whole-column phase assumption. The fixed moving character
and fixed remaining mask stay in the actual arithmetic coefficients. -/
theorem completeIdealFixedTwistRawAtoms_actual_phase_dictionary
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    {ω ψ : HeckeCharacter K}
    (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    (sector : NonzeroIdeal K → SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (d : MomentData K ω ψ) (remaining : NonzeroIdeal K) (fixed : HeckeCharacter K)
    (hallowed : ∀ u, d.allowedRow u →
      completeIdealIsExterior K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u)
    (hrow : ∀ u, d.allowedRow u → d.rowCharacter u = fixed *
      completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R (sector u) u)
    (hmask : ∀ u I, d.commonMask u I =
      (completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
        decide (IsCoprime I remaining.val)))
    (W : NormProfileRecipe (fun _ : PUnit => d))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) :
    let atoms := completeIdealFixedTwistArithmeticAtoms
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R sector d remaining fixed
      hallowed hrow hmask
    let raw := (atoms.constantAtoms W a Z t).raw Y₁ Y₂
    (∀ I ∈ raw.leftColumns,
      ∀ q : ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
      raw.leftPhase q I = actualIdealResidue (A := A) (σ := σ) I.val q.out.val) ∧
    (∀ I ∈ raw.rightColumns,
      ∀ q : ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
      raw.rightPhase q I = actualIdealResidue (A := A) (σ := σ) I.val q.out.val) ∧
    (∀ i, ∀ p ∈ raw.slotColumns i,
      ∀ q : ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
      raw.primePhase q i p = actualIdealResidue (A := A) (σ := σ) p.asIdeal q.out.val) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro I _ q
    exact actualProbeOrbitSexticEvaluation_eq_actualIdealResidue P hroot hemb I q
  · intro I _ q
    exact actualProbeOrbitSexticEvaluation_eq_actualIdealResidue P hroot hemb I q
  · intro i p _ q
    exact actualProbeOrbitSexticEvaluation_eq_actualIdealResidue P hroot hemb
      (momentPrimeIdeal K p) q

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actualProbeOrbitSexticEvaluation_eq_actualIdealResidue
#print axioms HeckeSkeleton.Moments.EngineStep.completeIdealFixedTwistRawAtoms_actual_phase_dictionary

