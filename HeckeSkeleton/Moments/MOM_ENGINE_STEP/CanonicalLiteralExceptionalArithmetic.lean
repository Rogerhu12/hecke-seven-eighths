import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalFactory
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSupportedRowMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalRelativeBudget
import HeckeGeneral.Characters.FiniteRamification
import HeckeAxiom.ArithmeticChoice

/-!
# Arithmetic and original fibres of the literal exceptional class

The finite bad-prime set is computed from the original finite theta
catalogue, before choosing the arithmetic context or any moving source.
Its inclusion in the same arithmetic choice proves unramifiedness.

On the actual correlation-supported theta class, the original chart
constructs the row mass and the original orbit fibre bound.  The literal
atlas branch supplies its common-ideal identity.  Its nonzero frozen
scalar then gives the required coprimality, while the original probe's
proved character laws give a common sixth-free base and the original
frequency valuations.  No classified-row or cardinality estimate is
an input to this construction.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalArithmetic

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

/-- A fixed finite set, depending only on the original catalogue. -/
def thetaBadPrimes (theta : Finset (HeckeCharacter K)) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  theta.biUnion (fun χ => (finite_ramifiedPlaces K χ).toFinset)

theorem theta_unramified {A : SArithmeticData K} (theta : Finset (HeckeCharacter K))
    (hplaces : thetaBadPrimes theta ⊆ A.Sf) (χ : HeckeCharacter K) (hχ : χ ∈ theta)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) : UnramifiedAt K χ p := by
  by_contra hr
  exact hp (hplaces (Finset.mem_biUnion.mpr
    ⟨χ, hχ, (finite_ramifiedPlaces K χ).mem_toFinset.mpr hr⟩))

/-- The original arithmetic choice preserves this fixed exclusion.
It requires no new choice after rows or profiles have been supplied. -/
theorem chosen_theta_unramified (theta : Finset (HeckeCharacter K))
    {initial : Finset (HeightOneSpectrum (𝓞 K))} {root12 : K} {σ : K →+* ℂ}
    (choice : HeckeAxiom.ArithmeticChoice K initial root12 σ)
    (hplaces : thetaBadPrimes theta ⊆ initial) (χ : HeckeCharacter K) (hχ : χ ∈ theta)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∉ (choice.A.Sf : Set (HeightOneSpectrum (𝓞 K)))) :
    UnramifiedAt K χ p :=
  theta_unramified theta (hplaces.trans choice.initial) χ hχ p hp

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
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
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS} {left : Finset α} {right : Finset β}
variable {profiles : α → β → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {D : (∅ : Finset (HeightOneSpectrum A.R)).powerset}
variable (chart : SecondBlockProfileChart (E := ℝ) hΓ μv hDiff b C left right
  profiles finiteTest radius D.val)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (hclass : chart.NonunitLabelStable) (hsector : chart.SectorLabelStable P)
variable (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable {ω ψ : HeckeCharacter K}
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K)

local notation "Orbit" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "rawRows" => chart.actualRows ∅ X hX label
local notation "pattern" => chart.originalNonunitPattern ∅ X hX label
local notation "sector" => chart.originalSector P ∅ X hX label
local notation "characters" => (rawRows).literalFiniteCharacters C P R F oldMoving
  correction pattern sector parent.theta

variable {kCommonL kCommonR : ℕ}
variable (leftAtoms : FrozenSourceAtoms A σ Orbit (rawRows).rows kCommonL)
variable (rightAtoms : FrozenSourceAtoms A σ Orbit (rawRows).rows kCommonR)
variable (thetaPair : parent.theta × parent.theta)

local notation "S" => CanonicalLiteralExceptionalFactory.rows chart P R X hX label
  F parent oldMoving correction leftAtoms rightAtoms thetaPair

section Mass

variable (hleft : leftAtoms.ideal = (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hright : rightAtoms.ideal = (primePowerProduct b.primes b.rightMultiplicity).val)
variable (bound : ℝ) (hbound : 0 ≤ bound)
variable (hprofile : ∀ q ∈ (rawRows).rows, ‖chart.weight q‖ ≤ bound)

include hclass hleft hright hbound hprofile

/-- The common atoms and both actual row restrictions are those of the
literal exceptional factory.  The original chart supplies all fields. -/
def actualMass : ActualSecondRowMass S C kCommonL kCommonR :=
  (chart.actualRowsSupportedMass hclass ∅ X hX label leftAtoms rightAtoms
    hleft hright bound hbound hprofile).restrictRows ((characters).thetaClass thetaPair)

local notation "mass" => actualMass chart P R hclass X hX label F parent oldMoving correction
  leftAtoms rightAtoms thetaPair hleft hright bound hbound hprofile

@[simp] theorem actualMass_fiber : (mass).originalFiber = Γ.index := rfl

@[simp] theorem actualMass_radius : (mass).radius = radius := rfl

@[simp] theorem actualMass_mask : (mass).mask = ∅ := by
  change D.val = ∅
  exact Finset.subset_empty.mp (Finset.mem_powerset.mp D.property)

@[simp] theorem actualMass_unit : (mass).unitIdeal =
    secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern := rfl

@[simp] theorem actualMass_nonunit : (mass).nonunitIdeal =
    secondPatternNonunitIdeal b.primes pattern := rfl

@[simp] theorem actualMass_commonEnvelope : (mass).commonEnvelope =
    bound * Real.sqrt leftAtoms.envelope * Real.sqrt rightAtoms.envelope := rfl

theorem original_fibers (I : Ideal (𝓞 K)) :
    ((S).rows.filter (fun h => ((S).originalIdeal h).val = I)).card ≤ Γ.index :=
  (mass).original_fibers I

theorem extracted_fibers (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((Finset.univ : Finset (S).live).filter
      (fun h => ((S).extractedRow C h).momentIdeal = I)).card ≤ Γ.index :=
  (mass).extracted_fibers I

/-- A later exceptional predicate creates no new original ideal
fibres.  This is the real-valued field used by the paid row theorem. -/
theorem exceptional_fibers {theta : Finset (HeckeCharacter K)}
    (Q : PairedFiniteCharacters theta Orbit) (I : Ideal (𝓞 K))
    (hI : I ∈ (Finset.univ : Finset ((S).exceptionalRows Q)).image
      (fun h => ((S).extractedRow C h.val).ideal.val)) :
    (((Finset.univ : Finset ((S).exceptionalRows Q)).filter
      (fun h => ((S).extractedRow C h.val).ideal.val = I)).card : ℝ) ≤ (Γ.index : ℝ) :=
  (mass).exceptional_extracted_fibers Q I hI

end Mass

section Classification

variable {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
variable (atlas : SourceCartesianAtlas columns ideal)
variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable (count : k = atlas.slotCount)
variable (support : Finset (Ideal (𝓞 K)))
variable (branchLabel : atlas.labels support
  (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (recipe : CanonicalLiteralActualCharacters.Recipe P R F parent oldMoving
  correction remaining extra d)
variable (hplaces : thetaBadPrimes parent.theta ⊆ A.Sf)

local notation "branch" => atlas.branch support
  (primePowerProduct b.primes b.leftMultiplicity).val branchLabel
local notation "original" => d.onAtlas atlas count

include hclass hsector hcorr recipe hplaces in
/-- The class is the actual finite theta class of the physical chart.
Both conclusions follow from the original frozen scalar and the
constructed Kummer laws, with the actual atlas product used internally. -/
theorem exists_actual_classification (hscalar : (original).commonScalar branch ≠ 0) :
    ∃ base : HeckeGeneral.Analysis.NonzeroIdeal K, SixthPowerFreeIdeal base ∧
      (∀ h : (S).live, ∃ a : Ideal (𝓞 K),
        ((S).extractedRow C h).ideal.val = base.val * a ^ 6) ∧
      (∀ h : (S).live, ∀ i ∈ multiplicityOneNonunitPrimes C (S).primes
        (S).leftMultiplicity (S).rightMultiplicity ((S).frequency h.val),
        6 ∣ (UniqueFactorizationMonoid.normalizedFactors
          ((S).originalIdeal h.val).val).count ((S).primes i).val.asIdeal) := by
  let rowMap : (S).live → CanonicalOriginalPhaseCalibration.PatternSector P S C pattern sector :=
    CanonicalLiteralExceptionalFactory.originalRow chart P R hclass hsector
      X hX label F parent oldMoving correction leftAtoms rightAtoms thetaPair
  let selected := (Finset.univ : Finset (S).live).image rowMap
  have hmem (h : (S).live) : rowMap h ∈ selected :=
    Finset.mem_image.mpr ⟨h, Finset.mem_univ h, rfl⟩
  have htheta (h : (S).live) :
      (S).literalCharacter C P R F oldMoving correction pattern sector
        (rowMap h).val.val.val = thetaPair.1.val := by
    exact CanonicalLiteralExceptionalFactory.character_on_class chart P R X hX label
      F parent oldMoving correction leftAtoms rightAtoms thetaPair .left h
  have hcommon : frozenSourceIdeal (branch).plainDivisor₁ (branch).plainDivisor₂
      (branch).keep (branch).witness.2 = (primePowerProduct (S).primes (S).leftMultiplicity).val :=
    (branch).frozenSourceIdeal_eq.trans
      (atlas.branch_product support (primePowerProduct b.primes b.leftMultiplicity).val branchLabel)
  obtain ⟨base, hfree, hfactor, hvaluation⟩ :=
    CanonicalLiteralExceptionalClassification.exists_actual_classification P R F
      parent oldMoving correction hcorr remaining extra (recipe.onAtlas atlas count) branch
      C S pattern sector (CanonicalLiteralPrimitiveCharacters.primitiveCharacterLaws P R)
      (theta_unramified parent.theta hplaces) hcommon hscalar selected thetaPair.1
  refine ⟨base, hfree, ?_, ?_⟩
  · intro h
    exact hfactor (rowMap h) (hmem h) (htheta h)
  · intro h
    exact hvaluation (rowMap h) (hmem h) (htheta h)

end Classification

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalArithmetic

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalArithmetic.theta_unramified
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalArithmetic.actualMass
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalArithmetic.exceptional_fibers
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalArithmetic.exists_actual_classification
