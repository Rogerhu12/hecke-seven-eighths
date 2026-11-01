import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalMovingParentSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.RemainingMaskRadical
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCommonNormalization

/-!
# The actual first source uses the full original joint row budget

The old row-ball constructor sees only the coarse width `m+q`. The
original full-support budget gives the stronger radius
`Norm(effectiveFullSupport)/Z^(m+q)`. This file constructs that actual
chart and first source on precisely the same original rows, arithmetic
atoms, complete centered coefficients, columns and Gram test.

The additional full support remains in the original column coefficients.
It is not an extra avoidance condition on the varying row. The row mask
is empty, while the full column mask and its actual norm charge remain.
Both a direct entrance and an attached original pool can use this source.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Bridge
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
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
variable {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}

namespace ParentRawAtoms.ConstantValues

variable {raw : ParentRawAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂}

/-- Install an original positive chart at its actual radius. The same
coefficient, first common blocks, logarithmic profiles and Gauss data are
constructed internally, uniformly for all original slot counts. -/
def canonicalDirectFirstSourceOfChart
    (C : A.GeneralArithmeticContext σ η hS) (values : raw.ConstantValues)
    (radius : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
    (chart : GaussEnergyChart (pairedRows d a Z) raw.rowMap (fun _ => 1)
      (CanonicalRowBall.archTest K A.Sf 1)
      (sIntegerFiniteTestFunction K A.Sf (rowBallFiniteFamily K A.Sf 1)) radius mask 1)
    (left : ∀ I ∈ raw.leftColumns, ∀ q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ,
      raw.leftPhase q I = actualIdealResidue (A := A) (σ := σ) I.val q.out.val)
    (right : ∀ I ∈ raw.rightColumns, ∀ q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ,
      raw.rightPhase q I = actualIdealResidue (A := A) (σ := σ) I.val q.out.val)
    (prime : ∀ i, ∀ p ∈ raw.slotColumns i, ∀ q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ,
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
    (radius) D.val δ hδ hδ1
  pieces DE D := canonicalFirstDirectLogBlock hΓ μv ν C
    raw.exteriorColumns raw.exteriorColumns raw.columnExterior raw.columnExterior
    DE.val DE.property (CanonicalRowBall.archTest K A.Sf 1)
    (values.coefficient centered) (values.coefficient centered)
    (rowBallFiniteFamily K A.Sf 1)
    (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius) D.val mask X hX δ hδ hδ1
  calibration := values.actualExteriorCalibrationOfAtomPhases (raw := raw) (σ := σ)
    hΓ left right prime chart
    (continuous_sIntegerFiniteTestFunction K A.Sf _
      (rowBallFiniteFamily_locallyConstant K A.Sf 1))
    (hasCompactSupport_sIntegerFiniteTestFunction K A.Sf _
      (rowBallFiniteFamily_compactSupport K A.Sf 1))
    centered (fun i => engineAllowedGenerator C (raw.columnExterior i))
    (fun i => engineAllowedGenerator_generates C (raw.columnExterior i))

end ParentRawAtoms.ConstantValues

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- This radius charges the effective full deletion support, including
the original remaining ideal after its exact Boolean radical reduction. -/
def fullSupportRadius (Z width : ℝ) (hZ : 0 < Z) : {r : ℝ // 0 < r} :=
  ⟨A.exteriorNorm (Q.moving.effectiveFullSupport Q.remaining) / Z ^ width,
    div_pos (A.exteriorNorm_pos _) (Real.rpow_pos_of_pos hZ _)⟩

/-- The sharp inverse radius used by the first pure-dual zero. -/
theorem fullSupportRadius_inverse (Z width : ℝ) (hZ : 1 < Z) :
    (Q.fullSupportRadius Z width (zero_lt_one.trans hZ)).val⁻¹ =
      Z ^ (width - idealLogLength Z (Q.moving.effectiveFullSupport Q.remaining).val) := by
  change ((Ideal.absNorm (Q.moving.effectiveFullSupport Q.remaining).val : ℝ) / Z ^ width)⁻¹ = _
  rw [inv_div, Real.rpow_sub (zero_lt_one.trans hZ),
    rpow_idealLogLength Z hZ _ (Q.moving.effectiveFullSupport Q.remaining).property.1]

/-- Every original row satisfies the actual tighter window; the proof
uses the original complete joint budget, not a displayed-support bound. -/
theorem fullSupportRadius_row_window
    (Z width : ℝ) (hZ : 0 < Z) (hbudget : Q.FullJointBudget Z width)
    (ξ : X) (a : RealParameters)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : u ∈ pairedRows (data ξ) a Z) :
    (Q.fullSupportRadius Z width hZ).val *
      (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
        ((Q.arithmeticAtoms ξ).rowMap u)).val ≤ 1 := by
  have hallowed := (((data ξ).rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1
  have hb := Q.effectiveMovingMaskRecipe_jointBudget Z width hbudget ξ u hallowed
  rw [parent_orbit_norm_of_originalIdeal _ u (Q.arithmeticAtoms_originalIdeal ξ u hallowed)]
  change (A.exteriorNorm (Q.moving.effectiveFullSupport Q.remaining) / Z ^ width) *
    idealNorm K u ≤ 1
  calc
    _ = (idealNorm K u * A.exteriorNorm (Q.moving.effectiveFullSupport Q.remaining)) /
        Z ^ width := by ring
    _ ≤ 1 := (div_le_iff₀ (Real.rpow_pos_of_pos hZ width)).mpr (by simpa only [one_mul] using hb)

/-- The original moving-row recipe constructs the actual first source
at the full-support radius. Its arithmetic coefficient and all of its
original deletion zeros are unchanged; no final source bound is an input. -/
def canonicalFullSupportDirectFirstSource
    (C : A.GeneralArithmeticContext σ η hS)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (W : NormProfileRecipe data) (ξ : X)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 0 < Z)
    (hbudget : Q.FullJointBudget Z (a.m + a.q))
    (centered : Bool) (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ActualDirectFirstSource
      (Γ := sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (E := ℝ) (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv C Z (rowBallFiniteFamily K A.Sf 1)
      centered (data ξ) a t Y₁ Y₂ cutoff hcutoff := by
  let atoms := (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t
  let raw := atoms.raw Y₁ Y₂
  let radius := Q.fullSupportRadius Z (a.m + a.q) hZ
  have hideal (u) (hu : u ∈ pairedRows (data ξ) a Z) :
      (ProbeOrbitNormSum.principalExterior A (raw.rowMap u).out).val = u.val :=
    Q.arithmeticAtoms_originalIdeal ξ u
      (((data ξ).rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1
  have chart := CanonicalRowBall.chart (pairedRows (data ξ) a Z) raw.rowMap radius 1 ∅ 1
    (fun u hu => Q.fullSupportRadius_row_window Z (a.m + a.q) hZ hbudget ξ a u hu)
    (fun _ _ => by simp [sIntegerOrbitAvoidanceMask])
    (parent_rowMap_fibres_le_one_of_originalIdeal (pairedRows (data ξ) a Z) raw.rowMap hideal)
  exact (atoms.values Y₁ Y₂).canonicalDirectFirstSourceOfChart
    (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (μv := μv) (ν := ν) C radius ∅ chart
    (fun I _ q => Q.arithmeticAtoms_leftPhase hroot hemb ξ q I)
    (fun I _ q => Q.arithmeticAtoms_rightPhase hroot hemb ξ q I)
    (fun i p _ q => Q.arithmeticAtoms_primePhase hroot hemb ξ q i p)
    centered cutoff hcutoff δ hδ hδhalf

@[simp] theorem canonicalFullSupportDirectFirstSource_radius
    (C : A.GeneralArithmeticContext σ η hS)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (W : NormProfileRecipe data) (ξ : X)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 0 < Z)
    (hbudget : Q.FullJointBudget Z (a.m + a.q))
    (centered : Bool) (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    (Q.canonicalFullSupportDirectFirstSource μv ν C hroot hemb W ξ a Z t Y₁ Y₂ hZ hbudget
      centered cutoff hcutoff δ hδ hδhalf).radius = Q.fullSupportRadius Z (a.m + a.q) hZ := rfl

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.ConstantValues.canonicalDirectFirstSourceOfChart
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.fullSupportRadius_row_window
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.fullSupportRadius_inverse
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalFullSupportDirectFirstSource
