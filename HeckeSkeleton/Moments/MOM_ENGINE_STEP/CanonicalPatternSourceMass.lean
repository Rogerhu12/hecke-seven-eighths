import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExteriorChildBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualChildCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSupportedRowMass

/-!
# Actual child row windows and unchanged arithmetic fibre mass

Pattern and unit-sector subtypes inject into the original live rows.
They introduce no additional ideal fibre and no new row weight. The
physical original chart produces the child's complete allowed-row and
cutoff bounds, including the original remaining support and complete
sixth-root deletion.

The Fourier profile update keeps all arithmetic fields literal, so a
common original ordinary/exceptional row predicate is fixed before both
Fourier modes. This file does not choose a different predicate or add
a new source/calibration record.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPatternSourceMass

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

section ActualFibres

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS)
variable {kLeft kRight : ℕ} (mass : ActualSecondRowMass rows C kLeft kRight)
variable (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
local notation "Index" => CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector

/-- The actual correlation remains in the row weight exactly once. -/
theorem row_bound (q : Index) :
    ‖rows.weight q.val.val.val * rows.correlation q.val.val.val‖ ≤ mass.rowBound :=
  mass.row_bound q.val.val.val (Finset.mem_filter.mp q.val.val.property).1

/-- Two genuine subtype injections preserve the original ideal-fibre
bound. The finite carrier can be the whole pattern source or its one
common ordinary restriction. -/
theorem extracted_fibers (carrier : Finset Index) (I : NonzeroIdeal K) :
    (carrier.filter (fun q => (rows.extractedRow C q.val.val).momentIdeal = I)).card ≤
      mass.originalFiber := by
  let T := carrier.filter (fun q => (rows.extractedRow C q.val.val).momentIdeal = I)
  have hinj : Function.Injective (fun q : Index => q.val.val) :=
    Subtype.val_injective.comp Subtype.val_injective
  have hsub : T.image (fun q => q.val.val) ⊆
      (Finset.univ : Finset rows.live).filter
        (fun h => (rows.extractedRow C h).momentIdeal = I) := by
    intro h hh
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩
  calc
    _ = (T.image (fun q => q.val.val)).card :=
      (Finset.card_image_of_injective T hinj).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ mass.originalFiber := mass.extracted_fibers I

end ActualFibres

section SameModes

variable {ω ψ : HeckeCharacter K}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable (D : CanonicalLogProfiles.OriginalLogProfiles K ω ψ V)

theorem rowCharacter_same (ξ ζ : V) (u : NonzeroIdeal K) :
    (D.moving ξ).rowCharacter u = (D.moving ζ).rowCharacter u := rfl

theorem allowed_same (ξ ζ : V) (u : NonzeroIdeal K) :
    (D.moving ξ).allowedRow u ↔ (D.moving ζ).allowedRow u := Iff.rfl

theorem ordinary_character_same (ξ ζ : V) (u : NonzeroIdeal K) :
    (D.moving ξ).rowCharacter u ∉ (D.moving ξ).theta ↔
      (D.moving ζ).rowCharacter u ∉ (D.moving ζ).theta := Iff.rfl

/-- Apply this to the existing common row predicate. It proves its
arithmetic truth value independent of both modes, without replacing the
original paired exceptional partition. -/
theorem ordinary_condition_same (z : ℝ) (ξ ζ : V) (u : NonzeroIdeal K) :
    (if z = 0 then (D.moving ξ).plainBackground * (D.moving ξ).rowCharacter u ≠ 1
      else (D.moving ξ).rowCharacter u ∉ (D.moving ξ).theta) ↔
    (if z = 0 then (D.moving ζ).plainBackground * (D.moving ζ).rowCharacter u ≠ 1
      else (D.moving ζ).rowCharacter u ∉ (D.moving ζ).theta) := Iff.rfl

end SameModes

section ActualPatternWindows

open MeasureTheory

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {D : (∅ : Finset (HeightOneSpectrum A.R)).powerset}

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D.val)

/-- Multiply the actual extracted-row window by its proved factor.
This is the precise original-frequency numerical interface needed by
the same arithmetic child, with no completed child budget as input. -/
theorem source_full_mask_window
    (hclass : chart.NonunitLabelStable)
    (oldMoving : OriginalMovingFactors A P Rchar)
    (remaining : NonzeroIdeal K) (hremaining : IsCoprime remaining.val A.cS)
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ a₀)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ a₀)
    (hold : A.exteriorNorm (oldMoving.effectiveFullSupport remaining) ≤ Z ^ (q + wo))
    (h : (chart.actualRows ∅ X hX label).live) :
    let pattern := chart.originalNonunitPattern ∅ X hX label
    A.exteriorNorm ((chart.actualRows ∅ X hX label).originalIdeal h.val) *
        idealNorm K ((oldMoving.append (secondOriginalMovingFactors P Rchar C b.primes
            b.leftMultiplicity b.rightMultiplicity pattern)).fullMaskSupport
              (remaining * exteriorMomentIdeal
                (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity))) ≤
      (chart.actualRows ∅ X hX label).normFactor C h.val * Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern).val
        (secondPatternNonunitIdeal b.primes pattern).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent) := by
  let row := (chart.actualRows ∅ X hX label).extractedRow C h
  have hw := CanonicalExteriorChildBudget.actualRows_raw_remaining_joint_window chart hclass
    oldMoving remaining hremaining X hX label retainedScale Z g a₀ q wo cutoffExponent
    hscale hZ hradius hcutoff hleft hright hold h
  dsimp only at hw ⊢
  have hp := mul_le_mul_of_nonneg_left hw row.factor_pos.le
  change _ ≤ (chart.actualRows ∅ X hX label).normFactor C h.val * _ at hp
  rw [← mul_assoc] at hp
  change ((chart.actualRows ∅ X hX label).normFactor C h.val *
    A.exteriorNorm row.ideal) * _ ≤ _ at hp
  rw [← row.norm_factor] at hp
  exact hp

/-- The same complete budget proves the actual frequency cutoff after
using the original lower bound one on a nonzero-ideal norm. -/
theorem source_cutoff
    (hclass : chart.NonunitLabelStable)
    (oldMoving : OriginalMovingFactors A P Rchar)
    (remaining : NonzeroIdeal K) (hremaining : IsCoprime remaining.val A.cS)
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ a₀)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ a₀)
    (hold : A.exteriorNorm (oldMoving.effectiveFullSupport remaining) ≤ Z ^ (q + wo))
    (h : (chart.actualRows ∅ X hX label).live) :
    let pattern := chart.originalNonunitPattern ∅ X hX label
    A.exteriorNorm ((chart.actualRows ∅ X hX label).originalIdeal h.val) ≤
      (chart.actualRows ∅ X hX label).normFactor C h.val * Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern).val
        (secondPatternNonunitIdeal b.primes pattern).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent) := by
  let pattern := chart.originalNonunitPattern ∅ X hX label
  let mask := (oldMoving.append (secondOriginalMovingFactors P Rchar C b.primes
            b.leftMultiplicity b.rightMultiplicity pattern)).fullMaskSupport
              (remaining * exteriorMomentIdeal
                (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity))
  let row := (chart.actualRows ∅ X hX label).extractedRow C h
  have hw := CanonicalExteriorChildBudget.actualRows_raw_remaining_joint_window chart hclass
    oldMoving remaining hremaining X hX label retainedScale Z g a₀ q wo cutoffExponent
    hscale hZ hradius hcutoff hleft hright hold h
  have hrow : idealNorm K row.momentIdeal ≤ Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern).val
        (secondPatternNonunitIdeal b.primes pattern).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent) := by
    calc
      idealNorm K row.momentIdeal = idealNorm K row.momentIdeal * 1 := (mul_one _).symm
      _ ≤ idealNorm K row.momentIdeal * idealNorm K mask :=
        mul_le_mul_of_nonneg_left (one_le_idealNorm K mask) (idealNorm_pos K _).le
      _ ≤ _ := hw
  dsimp only
  rw [row.norm_factor]
  exact mul_le_mul_of_nonneg_left hrow row.factor_pos.le

/-- The raw arithmetic constructor is allowed on every actual source
row in this original physical window. Its test profiles may be the
literal bounded Fourier profiles already constructed from that source. -/
theorem child_allowed
    (hclass : chart.NonunitLabelStable)
    (oldMoving : OriginalMovingFactors A P Rchar)
    (remaining : NonzeroIdeal K) (hremaining : IsCoprime remaining.val A.cS)
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ a₀)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ a₀)
    (hold : A.exteriorNorm (oldMoving.effectiveFullSupport remaining) ≤ Z ^ (q + wo))
    (h : (chart.actualRows ∅ X hX label).live)
    {ω ψ : HeckeCharacter K} (parent : MomentData K ω ψ)
    (correction : HeckeCharacter K) (hcorr : correction = 1 ∨ correction ∈ parent.theta)
    (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (inverse leftTest rightTest : IdealTest K) (geometry : SlotGeometry K)
    (index : Fin geometry.slotCount → Fin parent.geometry.slotCount) :
    let pattern := chart.originalNonunitPattern ∅ X hX label
    (CanonicalMovingPhaseCalibration.childData P Rchar parent oldMoving correction hcorr
      C b.primes b.leftMultiplicity b.rightMultiplicity pattern sector remaining
      (Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern).val
        (secondPatternNonunitIdeal b.primes pattern).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent)) inverse leftTest rightTest geometry index).allowedRow
        ((chart.actualRows ∅ X hX label).extractedRow C h).momentIdeal := by
  refine ⟨(HeckeAxiom.exteriorEquiv A
    ((chart.actualRows ∅ X hX label).extractedRow C h).ideal).property, ?_⟩
  exact CanonicalExteriorChildBudget.actualRows_raw_remaining_joint_window chart hclass
    oldMoving remaining hremaining X hX label retainedScale Z g a₀ q wo cutoffExponent
    hscale hZ hradius hcutoff hleft hright hold h

section SupportedMass

variable (hclass : chart.NonunitLabelStable)
variable (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
variable (label : Fin (chart.rowLabelCount + 1))
variable {kLeft kRight : ℕ}
variable (leftAtoms : FrozenSourceAtoms A σ
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
  (chart.actualRows M X hX label).rows kLeft)
variable (rightAtoms : FrozenSourceAtoms A σ
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
  (chart.actualRows M X hX label).rows kRight)
variable (hleft : leftAtoms.ideal = (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hright : rightAtoms.ideal = (primePowerProduct b.primes b.rightMultiplicity).val)
variable (bound : ℝ) (hbound : 0 ≤ bound)
variable (hprofile : ∀ q ∈ (chart.actualRows M X hX label).rows, ‖chart.weight q‖ ≤ bound)
variable (pattern : Fin b.primeCount → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

local notation "supported" =>
  ((chart.actualRows M X hX label).withCommonAtoms leftAtoms rightAtoms).restrictRows
    (fun q => (chart.actualRows M X hX label).correlation q ≠ 0)
local notation "mass" => chart.actualRowsSupportedMass hclass M X hX label
  leftAtoms rightAtoms hleft hright bound hbound hprofile
local notation "Index" =>
  CanonicalOriginalPhaseCalibration.PatternSector P supported C pattern sector

/-- The row weight bound is constructed from this original chart and
its original common atoms, after removing only zero correlations. -/
theorem supported_row_bound (q : Index) :
    ‖supported.weight q.val.val.val * supported.correlation q.val.val.val‖ ≤
      mass.rowBound :=
  row_bound supported C mass pattern sector q

/-- The original orbit index is still the fibre bound on any ordinary
subcarrier of the same actual pattern source. No row-mass record is an
input: the original chart constructs it internally. -/
include hclass hleft hright hbound hprofile in
theorem supported_extracted_fibers (carrier : Finset Index) (I : NonzeroIdeal K) :
    (carrier.filter
      (fun q => (supported.extractedRow C q.val.val).momentIdeal = I)).card ≤ Γ.index := by
  exact extracted_fibers supported C mass pattern sector carrier I

end SupportedMass

end ActualPatternWindows

end HeckeSkeleton.Moments.EngineStep.CanonicalPatternSourceMass

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPatternSourceMass.extracted_fibers
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPatternSourceMass.ordinary_condition_same
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPatternSourceMass.source_full_mask_window
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPatternSourceMass.source_cutoff
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPatternSourceMass.child_allowed
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPatternSourceMass.supported_extracted_fibers
