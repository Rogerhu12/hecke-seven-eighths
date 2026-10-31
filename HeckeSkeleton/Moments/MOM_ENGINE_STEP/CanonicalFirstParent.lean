import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalParentSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstGaussData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualDirectFirstSource

/-!
# Constructing the actual first parent source

The parent row-ball test, its whole centered Gram matrix, every common
block, the first logarithmic chart, and both actual Gauss row dictionaries
are constructed from the original single-atom data. The original exterior
Cartesian atlas is retained definitionally. There is no supplied mixed
profile, first profile chart, parent comparison, or Gauss-block record.

The direct source is independent of a prime pool. Attaching an earlier
pool below preserves this exact source and uses only individual original
row, frozen ideal and column norm windows.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}

section Direct

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

namespace ParentRawAtoms.ConstantValues

variable {raw : ParentRawAtoms Q d a Z t Y₁ Y₂}

/-- A genuine original first source constructed uniformly in all slot
counts and in both the ordinary and centered parent coefficient. -/
def canonicalDirectFirstSource
    (C : A.GeneralArithmeticContext σ η hS) (values : raw.ConstantValues)
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
    (centered : Bool) (X : ℝ) (hX : 1 ≤ X)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ActualDirectFirstSource (E := ℝ) hΓ μv C Z
      (rowBallFiniteFamily K A.Sf 1) centered d a t Y₁ Y₂ X hX where
  Column := raw.Column
  columns := raw.exteriorColumns
  ideal := raw.columnExterior
  generator i := engineAllowedGenerator C (raw.columnExterior i)
  generates i := engineAllowedGenerator_generates C (raw.columnExterior i)
  profiles i j := (values.coefficient centered i * star (values.coefficient centered j)) •
    CanonicalRowBall.archTest K A.Sf 1
  radius := CanonicalRowBall.parentRadius a Z hZ
  mask := mask
  fiber := 1
  charts DE D := FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν
    (canonicalFirstCommonBlock C raw.exteriorColumns raw.exteriorColumns
      raw.columnExterior raw.columnExterior DE.val DE.property)
    C raw.exteriorColumns raw.exteriorColumns (CanonicalRowBall.archTest K A.Sf 1)
    (values.coefficient centered) (values.coefficient centered)
    (rowBallFiniteFamily K A.Sf 1)
    (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1)
    (CanonicalRowBall.parentRadius a Z hZ) D.val δ hδ hδ1
  pieces DE D := canonicalFirstDirectLogBlock hΓ μv ν C
    raw.exteriorColumns raw.exteriorColumns raw.columnExterior raw.columnExterior
    DE.val DE.property (CanonicalRowBall.archTest K A.Sf 1)
    (values.coefficient centered) (values.coefficient centered)
    (rowBallFiniteFamily K A.Sf 1)
    (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1)
    (CanonicalRowBall.parentRadius a Z hZ) D.val mask X hX δ hδ hδ1
  calibration := values.canonicalParentSource hΓ hZ mask hideal hmask left right prime
    centered (fun i => engineAllowedGenerator C (raw.columnExterior i))
    (fun i => engineAllowedGenerator_generates C (raw.columnExterior i))

end ParentRawAtoms.ConstantValues
end Direct

section Pool

variable {hΓ μv}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {centered : Bool} {X : ℝ} {hX : 1 ≤ X}

namespace ActualDirectFirstSource

variable (s : ActualDirectFirstSource (E := E) hΓ μv C Z
  finiteTest centered d a t Y₁ Y₂ X hX)

/-- The original physical rows and columns supply a pooled entrance
without replacing the actual first chart or its complete parent source.
The positive density for these individual exponent windows follows from
`uniform_pool_density_and_mass` at the earlier fixed threshold. -/
def withOriginalPool
    {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
    (P : PowerScaleExteriorPool A bad Z ell eps)
    (frozenLeft frozenRight : Ideal (𝓞 K))
    (hfrozenLeft : frozenLeft ≠ 0) (hfrozenRight : frozenRight ≠ 0)
    (rowLeft rowRight boundLeft boundRight divisorBound : ℝ)
    (hrowLeft : 0 ≤ rowLeft) (hrowRight : 0 ≤ rowRight)
    (hdivisor : 0 ≤ divisorBound)
    (hrowsLeft : ∀ v D, ∀ h ∈ (s.pieces v D).leftData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ rowLeft)
    (hrowsRight : ∀ v D, ∀ h ∈ (s.pieces v D).rightData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ rowRight)
    (hfrozenNormLeft : (Ideal.absNorm frozenLeft : ℝ) ≤ Z ^ boundLeft)
    (hfrozenNormRight : (Ideal.absNorm frozenRight : ℝ) ≤ Z ^ boundRight)
    (hcolumns : ∀ j ∈ s.columns, (Ideal.absNorm (s.ideal j).val : ℝ) ≤ Z ^ divisorBound)
    (hdensityLeft : 0 < P.rowDensity rowLeft (boundLeft + divisorBound))
    (hdensityRight : 0 < P.rowDensity rowRight (boundRight + divisorBound)) :
    ActualFirstSource (E := E) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX where
  Column := s.Column
  columns := s.columns
  ideal := s.ideal
  generator := s.generator
  generates := s.generates
  profiles := s.profiles
  radius := s.radius
  mask := s.mask
  fiber := s.fiber
  charts := s.charts
  pools v D := (s.pieces v D).withOriginalPool P frozenLeft frozenRight
    hfrozenLeft hfrozenRight rowLeft rowRight boundLeft boundRight divisorBound
    hrowLeft hrowRight hdivisor (hrowsLeft v D) (hrowsRight v D)
    hfrozenNormLeft hfrozenNormRight hcolumns hdensityLeft hdensityRight
  calibration := s.calibration

end ActualDirectFirstSource
end Pool

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.ConstantValues.canonicalDirectFirstSource
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.withOriginalPool
