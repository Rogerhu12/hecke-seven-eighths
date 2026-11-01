import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalSourceBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRowProfileBound
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFactorFreeAtomCosts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralNormFactorTransport

/-!
# Original common atoms and the actual constant-one row window

The raw original profile controls every prime occurrence after the
first literal atlas, deletion and norm-factor redistribution. The same
original branch supplies each common-atom witness. The original physical
fibre leaf supplies the constant-one row profile window internally.

Consequently the actual common envelope, including its two correlation
and theta restrictions, is bounded by an explicit power of the original
profile amplitude. Neither a completed common-envelope bound nor an
assumed post-transform row-profile bound is an input.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCommonBudget

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support CommonSupportMass

/-- Both actual common products and the same allocated source are paid
from this one original profile amplitude. -/
def profileDegree (cap : ℕ) : ℕ :=
  CanonicalLiteralExceptionalAtomBudget.commonDegree cap +
    CanonicalLiteralExceptionalSourceBudget.profileDegree cap

theorem profileDegree_eq (cap : ℕ) : profileDegree cap = 12 * cap + 10 := by
  unfold profileDegree CanonicalLiteralExceptionalAtomBudget.commonDegree
  rw [CanonicalLiteralExceptionalSourceBudget.profileDegree_eq]
  omega

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {Index : Type*} {data : Index → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (x : Index)
variable (recipe : NormProfileRecipe (fun _ : PUnit => data x))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
variable (phases : CanonicalLiteralPhaseCalibration.FixedPhases A) (power : A.Exterior)
variable (δ₁ δ₂ : ℝ) (extra : HeckeGeneral.Analysis.NonzeroIdeal K)
local notation "seed" => Q.literalOriginalAtoms x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂

section PlacedAtoms

variable {support : Finset (Ideal (𝓞 K))}
variable (first : SupportCartesianBranch (seed).plain₁ (seed).plain₂ (seed).slots support)
local notation "bare" => (seed).secondInput (σ := σ) first P R power phases.firstIdeal
  phases.poolIdeal phases.unitIdeal phases.firstElement phases.poolElement phases.unitElement
  phases.first_generates phases.pool_generates phases.unit_generates δ₁ δ₂
variable {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
variable (atlas : SourceCartesianAtlas columns ideal) (count : first.keep.card = atlas.slotCount)

/-- This is the original table after its actual first atlas, complete
first deletion, and redistribution, before the second common extraction. -/
def placedAtoms : CanonicalLiteralRectangles.Atoms (K := K) atlas.slotCount :=
  (((bare).onAtlas atlas count).deleteMask extra).redistributeNormFactors δ₁ δ₂

local notation "placed" => placedAtoms (σ := σ) Q x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
  phases power δ₁ δ₂ extra first atlas count

/-- All masks are calculated from the original binary mask operations. -/
theorem placedAtoms_mask : (placed).characters.MaskIndicator := by
  have hbase : (bare).characters.MaskIndicator :=
    ((((Q.literalSourceCharacters_maskIndicator x).restrictSlots first.keep).movingSingleton
      P R phases.firstIdeal phases.firstElement phases.first_generates).movingSingleton
      P R phases.poolIdeal phases.poolElement phases.pool_generates).movingSingleton
      P R phases.unitIdeal phases.unitElement phases.unit_generates
  have hplaced : ((bare).onAtlas atlas count).characters.MaskIndicator := by
    cases count
    exact hbase
  exact hplaced.deleteMask extra

variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (original : RawProfileWindow rowDomain heightDomain window orders (data x) amplitude)
variable (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
variable (hprime : ∀ i, Function.support (original.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
variable (hδ : δ₁ + δ₂ ≤ 1 / 2)

include original hzero ht hprime hδ in
/-- The same original prime occurrence is bounded even when its value
vanishes. No carrier is removed to obtain the estimate. -/
theorem placedAtoms_primeCost_le (i : Fin atlas.slotCount) (p : HeightOneSpectrum (𝓞 K)) :
    (placed).primeAtomCost i p ≤ amplitude ^ 2 := by
  change (((bare).onAtlas atlas count).redistributeNormFactors δ₁ δ₂).primeAtomCost i p ≤ _
  rw [← CanonicalLiteralRectangles.Atoms.redistributeNormFactors_onAtlas,
    CanonicalLiteralRectangles.Atoms.primeAtomCost_onAtlas,
    CanonicalLiteralRectangles.Atoms.secondInput_redistributeNormFactors]
  exact Q.literalOriginalAtoms_redistributedSecondInput_primeAtomCost_le x recipe a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ original hzero ht hprime first power phases.firstIdeal phases.poolIdeal
    phases.unitIdeal phases.firstElement phases.poolElement phases.unitElement
    phases.first_generates phases.pool_generates phases.unit_generates δ₁ δ₂ hδ _ p

end PlacedAtoms

section ActualPhysicalSource

variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η htrace}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable {ν : Measure (FiniteAdeleRing (𝓞 K) K)} [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]
variable (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
variable {ι : Type*} (source : ActualGaussSource C ι)
variable (retainedScale g : ℝ) (hscale : 0 < retainedScale)
variable (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (hnorm : ∀ h ∈ source.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable {Θ : Type*} [Fintype Θ] (dimension width : ℕ)
variable (character : ∀ DE : commonSupportPool source.columns source.columns
  (fun i => (source.ideal i).val) (fun j => (source.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ DE : commonSupportPool source.columns source.columns
  (fun i => (source.ideal i).val) (fun j => (source.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))
local notation "stage" => ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν) P δ₂ hδ₂ hδ₂half source
    retainedScale Z g hscale (zero_lt_one.trans hZ) cutoff hcutoff hnorm
      dimension width character dyad
variable {LC RC : SourceCartesianCover source.columns source.ideal}
variable (v : (stage).supported.gated.CoveredClassKey LC RC)
variable (exceptional : (stage).supported.gated.CoverHybridPredicates LC RC)
variable (kernel : SchwartzMap ℝ ℂ) (point : ι → ℝ) (j : v.AllocationKey)
variable (hlive : ((stage).supported.gated.fiberCoveredLeaf LC RC exceptional kernel point ⟨v, j⟩).Live)

include hlive in
/-- The actual fibre multiplier and its live original source prove the
row window. A bare leaf's nonemptiness is never substituted for it. -/
theorem rowProfile_one : ∀ q ∈ (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).rows,
    ‖v.chart.weight q‖ ≤ 1 :=
  ActualGaussStage.canonicalSector_fiberLeaf_rowProfile_one
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    P δ₂ hδ₂ hδ₂half source retainedScale Z g hscale (zero_lt_one.trans hZ)
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional kernel point ⟨v, j⟩ hlive

local notation "hclass" => ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock_nonunitLabelStable
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν) P δ₂ hδ₂ hδ₂half source
    retainedScale Z g hscale (zero_lt_one.trans hZ) cutoff hcutoff hnorm
      dimension width character dyad v.1 v.2.1
local notation "hrow" => rowProfile_one (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  (P := P) Z hZ δ₂ hδ₂ hδ₂half source retainedScale g hscale cutoff hcutoff hnorm
    dimension width character dyad v exceptional kernel point j hlive

variable {supportLeft supportRight : Finset (Ideal (𝓞 K))}
variable (firstLeft : SupportCartesianBranch (seed).plain₁ (seed).plain₂ (seed).slots supportLeft)
variable (firstRight : SupportCartesianBranch (seed).plain₁ (seed).plain₂ (seed).slots supportRight)
local notation "bareLeft" => (seed).secondInput (σ := σ) firstLeft P R power phases.firstIdeal
  phases.poolIdeal phases.unitIdeal phases.firstElement phases.poolElement phases.unitElement
  phases.first_generates phases.pool_generates phases.unit_generates δ₁ δ₂
local notation "bareRight" => (seed).secondInput (σ := σ) firstRight P R power phases.firstIdeal
  phases.poolIdeal phases.unitIdeal phases.firstElement phases.poolElement phases.unitElement
  phases.first_generates phases.pool_generates phases.unit_generates δ₁ δ₂
variable (indexLeft : AllocationColumn K firstLeft.keep.card → ι)
variable (indexRight : AllocationColumn K firstRight.keep.card → ι)
variable (dictionaryLeft : v.literalLeftParent.literalDictionary =
  ⟨firstLeft.keep.card, ((bareLeft).plain₁, (bareLeft).plain₂), (bareLeft).slots, indexLeft⟩)
variable (dictionaryRight : v.literalRightParent.literalDictionary =
  ⟨firstRight.keep.card, ((bareRight).plain₁, (bareRight).plain₂), (bareRight).slots, indexRight⟩)
local notation "leftAtoms" => placedAtoms (σ := σ) Q x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
  phases power δ₁ δ₂ extra firstLeft v.literalLeftParent (congrArg Sigma.fst dictionaryLeft).symm
local notation "rightAtoms" => placedAtoms (σ := σ) Q x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
  phases power δ₁ δ₂ extra firstRight v.literalRightParent (congrArg Sigma.fst dictionaryRight).symm
local notation "leftMask" => placedAtoms_mask (σ := σ) Q x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
  phases power δ₁ δ₂ extra firstLeft v.literalLeftParent (congrArg Sigma.fst dictionaryLeft).symm
local notation "rightMask" => placedAtoms_mask (σ := σ) Q x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
  phases power δ₁ δ₂ extra firstRight v.literalRightParent (congrArg Sigma.fst dictionaryRight).symm

/-- Its row-profile proof and both frozen common dictionaries are
computed from this original source, with no window record as input. -/
def commonMass := v.literalSupportedRowMass leftAtoms rightAtoms leftMask rightMask
  hclass 1 (by norm_num) hrow

variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (original : RawProfileWindow rowDomain heightDomain window orders (data x) amplitude)
variable (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
variable (hprime : ∀ i, Function.support (original.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
variable (hδ : δ₁ + δ₂ ≤ 1 / 2)
variable (cap : ℕ) (hcap : (data x).geometry.slotCount ≤ cap) (hamplitude : 1 ≤ amplitude)

local notation "W" => commonMass (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  Q x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ phases power δ₁ δ₂ extra
    hδ₂ hδ₂half source retainedScale g hscale cutoff hcutoff hnorm dimension width
      character dyad v exceptional kernel point j hlive firstLeft firstRight
        indexLeft indexRight dictionaryLeft dictionaryRight

include original hzero ht hprime hδ hcap hamplitude in
/-- The actual common envelope is paid from the original raw profile.
The first atlas count and both original occurrence maps are retained. -/
theorem commonEnvelope_le :
    (W).commonEnvelope ≤ amplitude ^ CanonicalLiteralExceptionalAtomBudget.commonDegree cap := by
  have hleftCap : (LC.branch v.2.2.1).slotCount ≤ cap := by
    rw [congrArg Sigma.fst dictionaryLeft]
    exact (by simpa only [Fintype.card_fin] using Finset.card_le_univ firstLeft.keep).trans hcap
  have hrightCap : (RC.branch v.2.2.2.1).slotCount ≤ cap := by
    rw [congrArg Sigma.fst dictionaryRight]
    exact (by simpa only [Fintype.card_fin] using Finset.card_le_univ firstRight.keep).trans hcap
  have hB : 1 ≤ amplitude ^ 2 := one_le_pow₀ hamplitude
  have hleft : ∀ i ∈ Finset.univ \ (W).leftAtoms.keep,
      (W).leftAtoms.annulus i * (W).leftAtoms.profile i ≤ amplitude ^ 2 := by
    intro i _
    change (v.literalLeftOriginal leftAtoms).primeAtomCost i (v.literalLeftBranch.witness.2 i) ≤ _
    rw [CanonicalLiteralRectangles.Atoms.primeAtomCost_onAtlas]
    exact placedAtoms_primeCost_le (σ := σ) Q x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      phases power δ₁ δ₂ extra firstLeft v.literalLeftParent (congrArg Sigma.fst dictionaryLeft).symm
      original hzero ht hprime hδ _ _
  have hright : ∀ i ∈ Finset.univ \ (W).rightAtoms.keep,
      (W).rightAtoms.annulus i * (W).rightAtoms.profile i ≤ amplitude ^ 2 := by
    intro i _
    change (v.literalRightOriginal rightAtoms).primeAtomCost i (v.literalRightBranch.witness.2 i) ≤ _
    rw [CanonicalLiteralRectangles.Atoms.primeAtomCost_onAtlas]
    exact placedAtoms_primeCost_le (σ := σ) Q x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      phases power δ₁ δ₂ extra firstRight v.literalRightParent (congrArg Sigma.fst dictionaryRight).symm
      original hzero ht hprime hδ _ _
  have h := (W).commonEnvelope_le_from_atoms cap (amplitude ^ 2) hB hleftCap hrightCap hB hleft hright
  simpa only [← pow_mul, CanonicalLiteralExceptionalAtomBudget.commonDegree,
    Nat.mul_add, Nat.mul_one] using h

include original hzero ht hprime hδ hcap hamplitude in
/-- The actual theta restriction leaves this same numerical envelope. -/
theorem restricted_commonEnvelope_le
    (predicate : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop) :
    ((W).restrictRows predicate).commonEnvelope ≤
      amplitude ^ CanonicalLiteralExceptionalAtomBudget.commonDegree cap :=
  commonEnvelope_le (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    Q x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ phases power δ₁ δ₂ extra
      hδ₂ hδ₂half source retainedScale g hscale cutoff hcutoff hnorm dimension width
        character dyad v exceptional kernel point j hlive firstLeft firstRight
          indexLeft indexRight dictionaryLeft dictionaryRight
            original hzero ht hprime hδ cap hcap hamplitude

include original hzero ht hprime hδ hcap hamplitude in
/-- The actual common envelope is absorbed into the same raw amplitude
as the allocated source. The fixed coefficient and Fourier growth remain
explicit; no transformed amplitude or source estimate is assumed. -/
theorem common_source_coefficient_le
    (annulus coefficient frequency : ℝ) (hannulus : 0 ≤ annulus)
    (hcoefficient : 0 ≤ coefficient) (hfrequency : 0 ≤ frequency) :
    annulus ^ cap * ((W).commonEnvelope * orbitalFieldFactor K) *
        (coefficient * amplitude ^ CanonicalLiteralExceptionalSourceBudget.profileDegree cap *
          frequency) ≤
      (annulus ^ cap * orbitalFieldFactor K * coefficient) *
        amplitude ^ profileDegree cap * frequency := by
  have henv := commonEnvelope_le (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    Q x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ phases power δ₁ δ₂ extra
      hδ₂ hδ₂half source retainedScale g hscale cutoff hcutoff hnorm dimension width
        character dyad v exceptional kernel point j hlive firstLeft firstRight
          indexLeft indexRight dictionaryLeft dictionaryRight
            original hzero ht hprime hδ cap hcap hamplitude
  have hfactor : 0 ≤ annulus ^ cap * orbitalFieldFactor K * coefficient *
      amplitude ^ CanonicalLiteralExceptionalSourceBudget.profileDegree cap * frequency :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hannulus _)
      (orbitalFieldFactor_nonneg K)) hcoefficient)
        (pow_nonneg (le_trans (by norm_num) hamplitude) _)) hfrequency
  calc
    _ = (W).commonEnvelope * (annulus ^ cap * orbitalFieldFactor K * coefficient *
        amplitude ^ CanonicalLiteralExceptionalSourceBudget.profileDegree cap * frequency) := by ring
    _ ≤ amplitude ^ CanonicalLiteralExceptionalAtomBudget.commonDegree cap *
        (annulus ^ cap * orbitalFieldFactor K * coefficient *
          amplitude ^ CanonicalLiteralExceptionalSourceBudget.profileDegree cap * frequency) :=
      mul_le_mul_of_nonneg_right henv hfactor
    _ = _ := by rw [profileDegree, pow_add]; ring

end ActualPhysicalSource

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCommonBudget

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCommonBudget.placedAtoms_primeCost_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCommonBudget.rowProfile_one
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCommonBudget.commonEnvelope_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCommonBudget.common_source_coefficient_le
