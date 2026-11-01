import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstParent
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstMaskWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstRowGeometry

/-!
# The original first source at its actual row radius

The radius is supplied together with its bound on the original parent
rows.  The positive row-ball test and unit fibres are constructed from
that bound and the original ideal identity.  The original Cartesian
columns, coefficients, atom phases and centered polynomial are retained.

For an empty initial mask, the actual first principal-prime mask remains
in every block.  Its norm and the actual pair modulus are bounded from
the original full columns.  Consequently both dictionaries of this
same constructed source satisfy a uniform arithmetic row window.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Bridge
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
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
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

variable {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}

namespace ParentRawAtoms.ConstantValues

variable {raw : ParentRawAtoms (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂}

/-- The actual original source at an explicit radius.  Its only row
bound concerns the same original row map; the positive profile, fibre
bound and whole parent calibration are proved internally. -/
def canonicalRadiusDirectFirstSource
    (C : A.GeneralArithmeticContext σ η hS) (values : raw.ConstantValues)
    (radius : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
    (hideal : ∀ u ∈ pairedRows d a Z,
      (ProbeOrbitNormSum.principalExterior A (raw.rowMap u).out).val = u.val)
    (hnorm : ∀ u ∈ pairedRows d a Z,
      radius.val * (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        Γ (raw.rowMap u)).val ≤ 1)
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
  radius := radius
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
    radius D.val δ hδ hδ1
  pieces DE D := canonicalFirstDirectLogBlock hΓ μv ν C
    raw.exteriorColumns raw.exteriorColumns raw.columnExterior raw.columnExterior
    DE.val DE.property (CanonicalRowBall.archTest K A.Sf 1)
    (values.coefficient centered) (values.coefficient centered)
    (rowBallFiniteFamily K A.Sf 1)
    (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1)
    radius D.val mask X hX δ hδ hδ1
  calibration := values.actualExteriorCalibrationOfAtomPhases (raw := raw) (σ := σ)
    hΓ left right prime
    (CanonicalRowBall.chart (pairedRows d a Z) raw.rowMap radius 1 mask 1 hnorm hmask
      (parent_rowMap_fibres_le_one_of_originalIdeal (pairedRows d a Z) raw.rowMap hideal))
    (continuous_sIntegerFiniteTestFunction K A.Sf _
      (rowBallFiniteFamily_locallyConstant K A.Sf 1))
    (hasCompactSupport_sIntegerFiniteTestFunction K A.Sf _
      (rowBallFiniteFamily_compactSupport K A.Sf 1))
    centered (fun i => engineAllowedGenerator C (raw.columnExterior i))
    (fun i => engineAllowedGenerator_generates C (raw.columnExterior i))

end ParentRawAtoms.ConstantValues

/-- The exact direct logarithmic block has no additional frequency
window input.  Its two literal row dictionaries are images of the same
original physical row set, including the negative right frequencies. -/
theorem canonicalFirstDirectLogBlock_row_windows
    (C : A.GeneralArithmeticContext σ η hS)
    {ι κ : Type*} (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right
      (fun i => (fullI i).val) (fun j => (fullJ j).val))
    (φ : SchwartzMap V ℂ) (c : ι → ℂ) (e : κ → ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (hD : D ∈ ((canonicalFirstCommonBlock C left right fullI fullJ DE hDE).mask ∅).powerset)
    (X : ℝ) (hX : 1 ≤ X) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (Z rowLength cutoffExponent B : ℝ) (hZ : 1 ≤ Z)
    (hcutoff : X ≤ Z ^ cutoffExponent) (hradius : radius.val ≤ Z ^ (-rowLength))
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ B)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ B) :
    let p := canonicalFirstDirectLogBlock hΓ μv ν C left right fullI fullJ DE hDE
      φ c e finiteTest hlc hcs radius D ∅ X hX δ hδ hδ1
    (∀ h ∈ p.leftData.rows, A.exteriorNorm (originalFrequencyIdeal h) ≤
      Z ^ (max 0 (cutoffExponent - rowLength + 3 * B))) ∧
    (∀ h ∈ p.rightData.rows, A.exteriorNorm (originalFrequencyIdeal h) ≤
      Z ^ (max 0 (cutoffExponent - rowLength + 3 * B))) := by
  let b := canonicalFirstCommonBlock C left right fullI fullJ DE hDE
  let profiles := fun i j => (c i * star (e j)) • φ
  let s := b.finiteSource hΓ C left right profiles ∅ radius X hX
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  obtain ⟨hmask, hmodulus⟩ :=
    b.original_mask_modulus_windows C hΓ left right profiles hDE Z B hZpos hleft hright
  have hphysical : s.physicalCutoff ≤ Z ^ (cutoffExponent - rowLength + 3 * B) := by
    have h := s.physicalCutoff_le_original_windows
      Z cutoffExponent (-rowLength) B (2 * B) hZpos hcutoff hradius hmask hmodulus
    convert h using 1 <;> congr 1 <;> ring
  have hdivisor : s.divisorPhysicalCutoff D ≤ s.physicalCutoff :=
    s.divisorPhysicalCutoff_le_supported D s.inverseRadiusBound
      s.inverseRadiusBound_nonneg
      (fun _ hi _ hj hp => s.inverseRadius_le hi hj hD hp)
  exact canonicalFirstGaussData_divisor_row_windows C left right fullI fullJ DE hDE s D
    (Z ^ (max 0 (cutoffExponent - rowLength + 3 * B)))
    (hdivisor.trans (hphysical.trans
      (Real.rpow_le_rpow_of_exponent_le hZ (le_max_right _ _))))

namespace ParentRawAtoms.ConstantValues

variable {raw : ParentRawAtoms (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂}

/-- Both row windows of the exact explicit-radius source follow from
the original full-column norm window.  These are the fields consumed
by `ActualDirectFirstSource.withOriginalPool`; no transformed window
or extra mask/modulus estimate is a premise. -/
theorem canonicalRadiusDirectFirstSource_row_windows
    (C : A.GeneralArithmeticContext σ η hS) (values : raw.ConstantValues)
    (radius : {r : ℝ // 0 < r})
    (hideal : ∀ u ∈ pairedRows d a Z,
      (ProbeOrbitNormSum.principalExterior A (raw.rowMap u).out).val = u.val)
    (hnorm : ∀ u ∈ pairedRows d a Z,
      radius.val * (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        Γ (raw.rowMap u)).val ≤ 1)
    (hmask : ∀ u ∈ pairedRows d a Z,
      sIntegerOrbitAvoidanceMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
        ∅ (raw.rowMap u) = 1)
    (left : ∀ I ∈ raw.leftColumns, ∀ q : Q,
      raw.leftPhase q I = actualIdealResidue (A := A) (σ := σ) I.val q.out.val)
    (right : ∀ I ∈ raw.rightColumns, ∀ q : Q,
      raw.rightPhase q I = actualIdealResidue (A := A) (σ := σ) I.val q.out.val)
    (prime : ∀ i, ∀ p ∈ raw.slotColumns i, ∀ q : Q,
      raw.primePhase q i p = actualIdealResidue (A := A) (σ := σ) p.asIdeal q.out.val)
    (centered : Bool) (X : ℝ) (hX : 1 ≤ X)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (rowLength cutoffExponent B : ℝ) (hZ : 1 ≤ Z)
    (hcutoff : X ≤ Z ^ cutoffExponent) (hradius : radius.val ≤ Z ^ (-rowLength))
    (hcolumns : ∀ i ∈ raw.exteriorColumns, A.exteriorNorm (raw.columnExterior i) ≤ Z ^ B) :
    let s := values.canonicalRadiusDirectFirstSource hΓ μv ν C radius ∅
      hideal hnorm hmask left right prime centered X hX δ hδ hδ1
    (∀ DE D, ∀ h ∈ (s.pieces DE D).leftData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤
        Z ^ (max 0 (cutoffExponent - rowLength + 3 * B))) ∧
    (∀ DE D, ∀ h ∈ (s.pieces DE D).rightData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤
        Z ^ (max 0 (cutoffExponent - rowLength + 3 * B))) := by
  have hw
      (DE : commonSupportPool raw.exteriorColumns raw.exteriorColumns
        (fun i => (raw.columnExterior i).val) (fun j => (raw.columnExterior j).val))
      (D : ((canonicalFirstCommonBlock C raw.exteriorColumns raw.exteriorColumns
        raw.columnExterior raw.columnExterior DE.val DE.property).mask ∅).powerset) :=
    canonicalFirstDirectLogBlock_row_windows hΓ μv ν C
      raw.exteriorColumns raw.exteriorColumns raw.columnExterior raw.columnExterior
      DE.val DE.property (CanonicalRowBall.archTest K A.Sf 1)
      (values.coefficient centered) (values.coefficient centered)
      (rowBallFiniteFamily K A.Sf 1)
      (rowBallFiniteFamily_locallyConstant K A.Sf 1)
      (rowBallFiniteFamily_compactSupport K A.Sf 1)
      radius D.val D.property X hX δ hδ hδ1 Z rowLength cutoffExponent B hZ
      hcutoff hradius hcolumns hcolumns
  exact ⟨fun DE D => (hw DE D).1, fun DE D => (hw DE D).2⟩

end ParentRawAtoms.ConstantValues
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.ConstantValues.canonicalRadiusDirectFirstSource
#print axioms HeckeSkeleton.Moments.EngineStep.canonicalFirstDirectLogBlock_row_windows
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.ConstantValues.canonicalRadiusDirectFirstSource_row_windows
