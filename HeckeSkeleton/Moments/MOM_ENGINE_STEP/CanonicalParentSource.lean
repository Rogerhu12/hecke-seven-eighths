import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalRowBallChart
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentOriginalAtlas

/-!
# The actual parent source from its original arithmetic atoms

The positive test and its four Gram profiles are constructed from the
fixed row-ball bump. The complete phase follows from the two individual
plain phases and every original prime occurrence. The exterior column
carrier and its Cartesian atlas are computed from these same original
supports, including an empty slot family.

The remaining dictionaries refer only to original row ideals, the
original avoidance mask, and individual arithmetic phases. No positive
profile chart, whole-column identity, source bound, or terminal estimate
is an input to this constructor.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}

local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

namespace ParentRawAtoms

variable {raw : ParentRawAtoms (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂}

/-- A genuine parent calibration with its fixed positive test, complete
centered coefficient, computed exterior carrier and unit row fibres.
The source atlas for this exact carrier is `raw.originalAtlas`.
Both values of `centered` and every original slot count use this one
construction. -/
def ConstantValues.canonicalParentSource (values : raw.ConstantValues)
    (hZ : 0 < Z) (mask : Finset (HeightOneSpectrum A.R))
    (hideal : ∀ u ∈ pairedRows d a Z,
      (ProbeOrbitNormSum.principalExterior A (raw.rowMap u).out).val = u.val)
    (hmask : ∀ u ∈ pairedRows d a Z,
      sIntegerOrbitAvoidanceMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
        mask (raw.rowMap u) = 1)
    (left : ∀ I ∈ raw.leftColumns, ∀ q : Q,
      raw.leftPhase q I = actualIdealResidue (A := A) (σ := σ) I.val q.out.val)
    (right : ∀ I ∈ raw.rightColumns, ∀ q : Q,
      raw.rightPhase q I = actualIdealResidue (A := A) (σ := σ) I.val q.out.val)
    (prime : ∀ i, ∀ p ∈ raw.slotColumns i, ∀ q : Q,
      raw.primePhase q i p = actualIdealResidue (A := A) (σ := σ) p.asIdeal q.out.val)
    (centered : Bool) (generator : raw.Column → A.R)
    (generates : ∀ v, A.Generates (raw.columnExterior v) (generator v)) :
    ParentSourceCalibration centered d a Z t Y₁ Y₂ raw.exteriorColumns
      (fun i j =>
        (generatedOriginalColumn (σ := σ) hΓ (raw.columnExterior i)
          (generator i) (generates i)).originalPair
          (generatedOriginalColumn (σ := σ) hΓ (raw.columnExterior j)
            (generator j) (generates j))
          ((values.coefficient centered i * star (values.coefficient centered j)) •
            CanonicalRowBall.archTest K A.Sf 1))
      (sIntegerFiniteTestFunction K A.Sf (rowBallFiniteFamily K A.Sf 1))
      (CanonicalRowBall.parentRadius a Z hZ) mask 1 :=
  values.actualExteriorCalibrationOfAtomPhases (raw := raw) (σ := σ) hΓ left right prime
    (CanonicalRowBall.parent_chart hZ raw.rowMap mask hideal hmask)
    (continuous_sIntegerFiniteTestFunction K A.Sf _
      (rowBallFiniteFamily_locallyConstant K A.Sf 1))
    (hasCompactSupport_sIntegerFiniteTestFunction K A.Sf _
      (rowBallFiniteFamily_compactSupport K A.Sf 1))
    centered generator generates

end ParentRawAtoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.ConstantValues.canonicalParentSource
