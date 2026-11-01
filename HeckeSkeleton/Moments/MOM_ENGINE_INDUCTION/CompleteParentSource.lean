import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourcePrimitive
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalParentSource

/-!
# A genuine canonical parent source for the actual complete rows

The original complete-ideal row map has exactly the original principal
exterior ideal, including its sixth-power amplifier part. The fixed
positive row-ball chart and all centered Gram profiles are then produced
by the canonical constructor at immutable MOM_ENGINE_STEP revision
7c4f4fe7f27d053effef2e107422f4444f53bda8.

The fixed moving character and its finite correction stay in the literal
arithmetic coefficient of each plain and prime atom. The full displayed
support and original remaining ideal retain exactly their common mask.
The additional orbital row-avoidance mask is empty; this does not change
the original commonMask. The row ball uses the original rows_spec bound alone. No bound
on the norm of the remaining ideal, no positive chart, no whole-column
phase identity and no energy estimate is an input to this source bridge.

The final constructor applies this source to the actual frozen and
normalized two-plain Mellin model at every frequency. Its norm recipe
is the proved literal replacement, not a premise on the original root.
The source's Cartesian atlas is the canonical raw.originalAtlas on
these same computed exterior columns.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open scoped Classical BigOperators nonZeroDivisors

universe u

variable {K : Type} [Field K] [NumberField K]

/-- Both actual ideal constructions contract the same principal ideal
of the original orbit representative. This also keeps its complete
sixth-power part, rather than replacing it by the sixth-free ideal. -/
theorem principalExterior_eq_actualOrbitIdeal (A : SArithmeticData K)
    (q : ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) :
    (ProbeOrbitNormSum.principalExterior A q.out).val =
      (actualSIntegerOrbitIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) q).val := by
  let I := ProbeOrbitNormSum.principalExterior A q.out
  have hcontraction :
      sIntegerModulusContraction K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) q.out.val =
        I.val := by
    unfold sIntegerModulusContraction
    rw [(ProbeOrbitNormSum.principalExterior_generates A q.out).2]
    exact SIntegerLocalization.under_map_exterior A.Sf I.val I.property.2
  calc
    _ = sIntegerModulusContraction K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        q.out.val := hcontraction.symm
    _ = _ := congrArg
      (fun r : ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) =>
        (actualSIntegerOrbitIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) r).val)
      (Quotient.out_eq q)

/-- The actual sector map supplies the row-ideal dictionary required
by the canonical positive source. No injectivity premise is needed. -/
theorem completeIdealSectorRowMap_principalExterior
    (A : SArithmeticData K)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (sector : HeckeGeneral.Analysis.NonzeroIdeal K →
      SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (v : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hv : completeIdealIsExterior K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) v) :
    (ProbeOrbitNormSum.principalExterior A
      (completeIdealSectorRowMap (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P sector v).out).val =
      v.val := by
  rw [principalExterior_eq_actualOrbitIdeal]
  have hrow := completeIdealSectorRowMap_exterior
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P sector
    (⟨v, hv⟩ : HeckeGeneral.ThetaSkeleton.ExteriorIdeal K _)
  rw [hrow, decomposedIdealSectorOrbit_ideal]

private theorem actualCompleteSubgroup_power (c : TargetContext K)
    (v : sixthPowerSUnitSubgroup K (places K c)) :
    ∃ w : (axiomChoice K c).A.U, v.val = w ^ 6 := by
  obtain ⟨w, hw⟩ := v.property
  exact ⟨w, hw.symm⟩

/-- This is the original probe's already selected integral generator. -/
private def actualParentColumnGenerator (c : TargetContext K)
    (I : (axiomChoice K c).A.Exterior) : (axiomChoice K c).A.R :=
  (probeData K c).arithmetic.generator (HeckeAxiom.exteriorEquiv (axiomChoice K c).A I)

private theorem actualParentColumnGenerator_generates (c : TargetContext K)
    (I : (axiomChoice K c).A.Exterior) :
    (axiomChoice K c).A.Generates I (actualParentColumnGenerator c I) := by
  refine ⟨(probeData K c).arithmetic.generator_ne_zero _, ?_⟩
  exact (probeData K c).arithmetic.generator_span
    (HeckeAxiom.exteriorEquiv (axiomChoice K c).A I)

namespace CompleteSourceData

variable {c : TargetContext K} {theta : Finset (HeckeCharacter K)}
variable {d : MomentData K c.family.omega (targetCharacter K c)}
variable [MeasurableSpace (sLocalNormOneGroup K (places K c))]
  [BorelSpace (sLocalNormOneGroup K (places K c))]

/-- The original parent source is constructed from the concrete full-row
dictionary and the actual norm recipe. Every original column coefficient,
slot, remaining mask and comparison scale is retained. -/
def canonicalParentSource (D : CompleteSourceData c theta d)
    (W : EngineStep.NormProfileRecipe (fun _ : PUnit => d))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 0 < Z) (centered : Bool) :
    let atoms := D.arithmeticAtoms.constantAtoms W a Z t
    let raw := atoms.raw Y₁ Y₂
    let values := atoms.values Y₁ Y₂
    EngineStep.ParentSourceCalibration centered d a Z t Y₁ Y₂
      (raw.exteriorColumns (A := (axiomChoice K c).A))
      (fun i j =>
        (EngineStep.generatedOriginalColumn (σ := complexEmbedding K c)
          (actualCompleteSubgroup_power c) (raw.columnExterior (A := (axiomChoice K c).A) i)
          (actualParentColumnGenerator c (raw.columnExterior (A := (axiomChoice K c).A) i))
          (actualParentColumnGenerator_generates c
            (raw.columnExterior (A := (axiomChoice K c).A) i))).originalPair
          (EngineStep.generatedOriginalColumn (σ := complexEmbedding K c)
            (actualCompleteSubgroup_power c) (raw.columnExterior (A := (axiomChoice K c).A) j)
            (actualParentColumnGenerator c (raw.columnExterior (A := (axiomChoice K c).A) j))
            (actualParentColumnGenerator_generates c
              (raw.columnExterior (A := (axiomChoice K c).A) j)))
          ((values.coefficient centered i * star (values.coefficient centered j)) •
            EngineStep.CanonicalRowBall.archTest K (axiomChoice K c).A.Sf 1))
      (sIntegerFiniteTestFunction K (axiomChoice K c).A.Sf
        (rowBallFiniteFamily K (axiomChoice K c).A.Sf 1))
      (EngineStep.CanonicalRowBall.parentRadius a Z hZ) ∅ 1 := by
  letI : IsPrincipalIdealRing (axiomChoice K c).A.R := (axiomChoice K c).C.principal
  dsimp only
  let atoms := D.arithmeticAtoms.constantAtoms W a Z t
  let raw := atoms.raw Y₁ Y₂
  have hrow (v : HeckeGeneral.Analysis.NonzeroIdeal K) (hv : v ∈ pairedRows d a Z) :
      (ProbeOrbitNormSum.principalExterior (axiomChoice K c).A (raw.rowMap v).out).val =
        v.val := by
    have hallowed : d.allowedRow v :=
      ((d.rows_spec _ v).mp (Finset.mem_filter.mp hv).1).1
    exact completeIdealSectorRowMap_principalExterior (axiomChoice K c).A
      (probeData K c) D.recipe.sector v (D.recipe.exterior PUnit.unit v hallowed)
  have hmask (v : HeckeGeneral.Analysis.NonzeroIdeal K) (_hv : v ∈ pairedRows d a Z) :
      sIntegerOrbitAvoidanceMask K (places K c)
        (sixthPowerSUnitSubgroup K (places K c)) ∅ (raw.rowMap v) = 1 := by
    simp [sIntegerOrbitAvoidanceMask]
  have phases := D.phase_dictionary W a Z t Y₁ Y₂
  exact (atoms.values Y₁ Y₂).canonicalParentSource (A := (axiomChoice K c).A)
    (σ := complexEmbedding K c)
    (actualCompleteSubgroup_power c) hZ ∅ hrow hmask
    phases.1 phases.2.1 phases.2.2 centered
    (fun v => actualParentColumnGenerator c (raw.columnExterior (A := (axiomChoice K c).A) v))
    (fun v => actualParentColumnGenerator_generates c
      (raw.columnExterior (A := (axiomChoice K c).A) v))

/-- At every actual common Mellin frequency the original frozen parent
now has the canonical positive source and the whole centered calibration.
No source calibration, norm-profile recipe, or Gram hypothesis is added
to the input of this specialization. -/
def mellinStrictParentSource {Ω : Type u} [MeasurableSpace Ω]
    (n : Node K c.family.omega (targetCharacter K c))
    (D : CompleteSourceData c theta n.data)
    (cap J : ℕ) (A lower upper : ℝ) (hA : 0 ≤ A) (hlower : 0 < lower)
    (hinterval : lower ≤ upper) (P : ℝ) (hP : 1 ≤ P) (frequency : ℝ × ℝ)
    (Z t Y₁ Y₂ : ℝ) (hZ : 0 < Z) (centered : Bool) :=
  let model := D.mellinStrictModel (Ω := Ω) n cap J A lower upper
    hA hlower hinterval P hP frequency
  model.canonicalParentSource
    ((n.mellinStrictModel_normProfileRecipe (Ω := Ω)
      cap J A lower upper hA hlower hinterval P hP).at frequency)
    n.parameters Z t Y₁ Y₂ hZ centered

end CompleteSourceData

end HeckeSkeleton.Moments.EngineInduction
