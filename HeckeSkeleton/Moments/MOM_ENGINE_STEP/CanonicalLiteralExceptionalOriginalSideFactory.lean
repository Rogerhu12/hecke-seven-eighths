import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPaidSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalProfileWindow
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectFactorFreeComputed
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRedistributedBinding

/-!
# The actual original exceptional side from its two occurrence branches

The original moving-row recipe, raw profile window and two literal
support branches construct the same factor-free table and its profile
model. The complete deletion and redistribution precede the second
common extraction. The first combined scalar is stripped only after
that extraction, using the original identity plain balance.

The final atlas supplies the actual ideal map. Its occurrence identities
transport the original support certificate. The actual allocation label
supplies its divisor and selection. No completed exceptional source,
profile bound, child geometry or normalization certificate is an input.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalOriginalSideFactory

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support
open CanonicalLiteralActualProfiles CanonicalLiteralFullKappaInput

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (recipe : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ}
variable (orders : Finset (ℕ × ℕ)) (amplitude : ℝ) (hamplitude : 0 ≤ amplitude)
variable (original : RawProfileWindow rowDomain heightDomain window
  (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders))
    (data ξ) amplitude)
variable (hreference : reference ∈ rowDomain) (ht : t ∈ heightDomain)
variable (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
variable (hprime : ∀ j, Function.support (original.primeRep j t) ⊆ Set.Ioo (1 : ℝ) 2)

local notation "seed" => Q.literalOriginalAtoms ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
local notation "allowedReference" =>
  (((data ξ).rows_spec _ reference).mp (Finset.mem_filter.mp href).1).1
local notation "seedSupport" => Q.literalOriginalProfileSupport ξ recipe a Z t Y₁ Y₂
  centered hZ hY₁ hY₂ reference href original hreference ht hpositive

variable {firstSupport : Finset (Ideal (𝓞 K))}
variable (first : SupportCartesianBranch (seed).plain₁ (seed).plain₂ (seed).slots firstSupport)
variable (hfirstSupport : ∀ p ∈ firstSupport, Prime p)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A) (power : A.Exterior)
variable (δ₁ δ₂ : ℝ)

local notation "extra" => literalDeletionIdeal firstSupport hfirstSupport
local notation "bare" => (seed).secondInput (σ := σ) first P R power F.firstIdeal F.poolIdeal
  F.unitIdeal F.firstElement F.poolElement F.unitElement F.first_generates F.pool_generates
    F.unit_generates δ₁ δ₂
local notation "actual" => ((bare).deleteMask extra).redistributeNormFactors δ₁ δ₂
local notation "oldScalar" => (seed).secondInputScalar (σ := σ) first power F.firstElement δ₁
local notation "scalar" => oldScalar * (((bare).deleteMask extra).normProfileFactor δ₁ δ₂ : ℂ)
local notation "beforeProfiles" =>
  (((seedSupport).secondInput (σ := σ) first P R hfirstSupport power F.firstIdeal F.poolIdeal
    F.unitIdeal F.firstElement F.poolElement F.unitElement F.first_generates F.pool_generates
      F.unit_generates δ₁ δ₂).deleteMask extra).redistributeNormFactors δ₁ δ₂

variable {secondSupport : Finset (Ideal (𝓞 K))}
variable (second : SupportCartesianBranch (actual).plain₁ (actual).plain₂ (actual).slots secondSupport)
variable (hsecondSupport : ∀ p ∈ secondSupport, Prime p)
variable {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
variable (atlas : SourceCartesianAtlas columns ideal) (count : second.keep.card = atlas.slotCount)
variable (hleft : atlas.reindex.plain₁ = ((actual).extract second).plain₁)
variable (hright : atlas.reindex.plain₂ = ((actual).extract second).plain₂)
variable (hslot : ∀ j, atlas.reindex.slots (Fin.cast count j) = ((actual).extract second).slots j)

local notation "finalAtoms" =>
  (((((actual).extract second).onAtlas atlas count).scale scalar⁻¹).balancePlain (fun _ => 1))
local notation "supported" => ((beforeProfiles).extract second hsecondSupport).onAtlasOfFields
  atlas count hleft hright hslot
local notation "finalProfiles" => ((supported).profiles.scale scalar⁻¹).balancePlain (fun _ => 1)

/-- The existing original computed model, through the actual remaining
extraction and atlas. The combined scalar is not recomputed from the
second quotient scales. -/
def originalComputed : ComputedProfiles finalProfiles window orders amplitude := by
  let initial := Q.literalFactorFreeComputedProfiles ξ recipe a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ reference allowedReference orders amplitude hamplitude original hreference ht
    hcompact hpositive hprime first power F.firstIdeal F.poolIdeal F.unitIdeal
    F.firstElement F.poolElement F.unitElement F.first_generates F.pool_generates
    F.unit_generates δ₁ δ₂
  let deleted := ComputedProfiles.deleteMaskThenRedistributeScale oldScalar δ₁ δ₂ initial extra
  let extracted := ComputedProfiles.extractThenScale scalar⁻¹ deleted second
  cases count
  exact (ComputedProfiles.onAtlasThenScale scalar⁻¹ extracted atlas rfl).balanceOne

/-- Only the numerical certificate is strengthened. Its model is the
same existing model, as the next identity records. -/
def uniformComputed : ComputedProfiles finalProfiles window orders amplitude := by
  let initial := CanonicalLiteralExceptionalProfileWindow.uniformComputedProfiles
    Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference allowedReference
    orders amplitude hamplitude original hreference ht hcompact hpositive hprime first
    power F.firstIdeal F.poolIdeal F.unitIdeal F.firstElement F.poolElement F.unitElement
    F.first_generates F.pool_generates F.unit_generates δ₁ δ₂
  let deleted := ComputedProfiles.deleteMaskThenRedistributeScale oldScalar δ₁ δ₂ initial extra
  let extracted := ComputedProfiles.extractThenScale scalar⁻¹ deleted second
  cases count
  exact (ComputedProfiles.onAtlasThenScale scalar⁻¹ extracted atlas rfl).balanceOne

theorem uniformComputed_model :
    (uniformComputed Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href orders
      amplitude hamplitude original hreference ht hcompact hpositive hprime first hfirstSupport
      F power δ₁ δ₂ second hsecondSupport atlas count hleft hright hslot).model =
    (originalComputed Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href orders
      amplitude hamplitude original hreference ht hcompact hpositive hprime first hfirstSupport
      F power δ₁ δ₂ second hsecondSupport atlas count hleft hright hslot).model := by
  cases count
  rfl

theorem uniformComputed_bound (r : Bool) :
    (uniformComputed Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href orders
      amplitude hamplitude original hreference ht hcompact hpositive hprime first hfirstSupport
      F power δ₁ δ₂ second hsecondSupport atlas count hleft hright hslot).bound r =
      CanonicalLiteralExceptionalProfileWindow.coefficient window hcompact hpositive
        δ₁ δ₂ orders * amplitude := by
  cases count
  rfl

variable (ray : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (firstSign : ℝ) (hfirstSign : |firstSign| ≤ 1)
variable (divisor : Ideal (𝓞 K))
variable (selection : primeSupport divisor → Finset (Fin (atlas.slotCount + 2)))
variable (hne : (pairedAllocatedColumns divisor selection (finalAtoms).plain₁ (finalAtoms).plain₂
  (finalAtoms).slots id id HeightOneSpectrum.asIdeal).Nonempty)
variable (hsquarefree : Squarefree divisor)
variable (hselection : selection ∈ AllocationMass.idealAllocations divisor (atlas.slotCount + 2))

/-- The actual side record. Every analytic representative, character
recipe, support certificate and numerical extraction identity is
constructed from the original inputs above. -/
def side : CanonicalLiteralExceptionalPaidSource.OriginalSide (σ := σ)
    P R F (data ξ) Q.moving Q.correction Q.remaining extra firstSupport secondSupport window Z := by
  let H := CanonicalLiteralExceptionalPaidSource.redistributedHistory (σ := σ)
    P R extra seed first power F.firstIdeal F.poolIdeal F.unitIdeal
    F.firstElement F.poolElement F.unitElement F.first_generates F.pool_generates
    F.unit_generates δ₁ δ₂ second atlas count scalar⁻¹ (fun _ => 1)
  let common := (Q.literalSecondInputRecipe (σ := σ) ξ recipe a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ first F power δ₁ δ₂ extra).redistributeNormFactors δ₁ δ₂
  let finalRecipe := (common.extract second).onAtlas atlas count
  refine
    { count := atlas.slotCount
      atoms := finalAtoms
      history := H
      count_eq := count.symm
      base_eq := ?_
      profiles := finalProfiles
      model := (originalComputed Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
        reference href orders amplitude hamplitude original hreference ht hcompact hpositive
        hprime first hfirstSupport F power δ₁ δ₂ second hsecondSupport atlas count
        hleft hright hslot).model
      recipe := { slots := finalRecipe.slots, characters := finalRecipe.characters }
      commonRecipe := common
      left_scale_eq := ?_
      right_scale_eq := ?_
      gauss_eq := ?_
      original_gauss := ?_
      support := ((supported).support.scale scalar⁻¹).balancePlain (fun _ => 1)
      ray := ray
      ideal := fun i => ideal (atlas.reindex.index i)
      ideal_eq := ?_
      firstSign := firstSign
      firstSign_le := hfirstSign
      divisor := divisor
      selection := selection
      nonempty := hne
      squarefree := hsquarefree
      selection_mem := hselection }
  · cases count
    rfl
  · intro r
    cases count
    change ((seed).scale₁ r / idealNorm K first.plainDivisor₁) /
        idealNorm K second.plainDivisor₁ =
      (seed).scale₁ r / idealNorm K (first.plainDivisor₁ * second.plainDivisor₁)
    rw [CanonicalLiteralProfileData.idealNorm_mul]
    ring
  · intro r
    cases count
    change ((seed).scale₂ r / idealNorm K first.plainDivisor₂) /
        idealNorm K second.plainDivisor₂ =
      (seed).scale₂ r / idealNorm K (first.plainDivisor₂ * second.plainDivisor₂)
    rw [CanonicalLiteralProfileData.idealNorm_mul]
    ring
  · cases count
    change extraGaussScale ((actual).extract second).gauss₁ ((actual).extract second).gauss₂
      ((actual).extract second).gaussSlot =
        extraGaussScale (actual).gauss₁ (actual).gauss₂ (actual).gaussSlot
    exact (actual).extract_gaussScale second
  · change extraGaussScale (1 : ℝ) 1 (fun _ : Fin (data ξ).geometry.slotCount => 1) = 1
    simp only [extraGaussScale, Finset.prod_const_one, one_mul]
  · intro i hi
    exact atlas.reindex.ideal_product i hi

local notation "D" => side Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href
  orders amplitude hamplitude original hreference ht hcompact hpositive hprime first hfirstSupport
  F power δ₁ δ₂ second hsecondSupport atlas count hleft hright hslot
    ray firstSign hfirstSign divisor selection hne hsquarefree hselection

@[simp] theorem side_atoms : (D).atoms = finalAtoms := rfl

@[simp] theorem side_model :
    (D).model = (originalComputed Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      reference href orders amplitude hamplitude original hreference ht hcompact hpositive
      hprime first hfirstSupport F power δ₁ δ₂ second hsecondSupport atlas count
      hleft hright hslot).model := rfl

/-- These bounds are on the same model stored in the actual side.
The ordinary normalization and its original chosen child are not used
or modified by this proof. -/
theorem side_profile_bounds :
    (∀ r, orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) ((D).model.left r) ≤
      CanonicalLiteralExceptionalProfileWindow.coefficient window hcompact hpositive
        δ₁ δ₂ orders * amplitude) ∧
    (∀ r, orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) ((D).model.right r) ≤
      CanonicalLiteralExceptionalProfileWindow.coefficient window hcompact hpositive
        δ₁ δ₂ orders * amplitude) ∧
    (∀ j, orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) ((D).model.slot j) ≤
      CanonicalLiteralExceptionalProfileWindow.coefficient window hcompact hpositive
        δ₁ δ₂ orders * amplitude) := by
  let U := uniformComputed Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href orders
    amplitude hamplitude original hreference ht hcompact hpositive hprime first hfirstSupport
    F power δ₁ δ₂ second hsecondSupport atlas count hleft hright hslot
  have hmodel : U.model = (D).model := uniformComputed_model Q ξ recipe a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ reference href orders amplitude hamplitude original hreference ht
    hcompact hpositive hprime first hfirstSupport F power δ₁ δ₂ second hsecondSupport
    atlas count hleft hright hslot
  have hbound (r : Bool) : U.bound r =
      CanonicalLiteralExceptionalProfileWindow.coefficient window hcompact hpositive
        δ₁ δ₂ orders * amplitude := uniformComputed_bound Q ξ recipe a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ reference href orders amplitude hamplitude original hreference ht
    hcompact hpositive hprime first hfirstSupport F power δ₁ δ₂ second hsecondSupport
    atlas count hleft hright hslot r
  have hmono (φ : 𝓢(ℝ, ℂ)) : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤
      (CanonicalLogProfiles.sourceOrders orders).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ :=
    Seminorm.finset_sup_apply_le (apply_nonneg _ _)
      (fun p hp => Seminorm.le_finset_sup_apply
        (CanonicalLogProfiles.subset_sourceOrders orders hp))
  refine ⟨?_, ?_, ?_⟩
  · intro r
    have h := (hmono (U.model.left r)).trans (U.left_bound r)
    simpa only [hmodel, hbound] using h
  · intro r
    have h := (hmono (U.model.right r)).trans (U.right_bound r)
    simpa only [hmodel, hbound] using h
  · intro j
    have h := (hmono (U.model.slot j)).trans (U.slot_bound false j)
    simpa only [hmodel, hbound] using h

theorem side_samePlainProfiles (hc : centered = true) :
    CanonicalLiteralExceptionalCharts.SamePlainProfiles (D).model := by
  subst centered
  let E := Q.literalOriginalSchwartzModel ξ recipe a Z t Y₁ Y₂ true hZ hY₁ hY₂
    reference allowedReference original hreference ht hpositive hcompact.isClosed
  have hE : CanonicalLiteralExceptionalCharts.SamePlainProfiles E :=
    CanonicalLiteralExceptionalCharts.original_samePlainProfiles Q ξ recipe a Z t Y₁ Y₂
      hZ hY₁ hY₂ reference allowedReference original hreference ht hpositive hcompact.isClosed
  have h := CanonicalLiteralExceptionalCharts.samePlainProfiles_factorFreeSecondInput
    (σ := σ) E first P R power F.firstIdeal F.poolIdeal F.unitIdeal F.firstElement
    F.poolElement F.unitElement F.first_generates F.pool_generates F.unit_generates
    δ₁ δ₂ hE hcompact hpositive
  cases count
  exact h

theorem side_primeNormWindow (B : ℝ) (hp : (seed).PrimeNormWindow B) :
    (D).atoms.PrimeNormWindow B := by
  have hp₁ : (actual).PrimeNormWindow B := hp.extract first
  exact (((hp₁.extract second).onAtlas atlas count hslot).scale scalar⁻¹).balancePlain (fun _ => 1)

/-- A return value on the exact final table. The heterogeneous equality
only transports its occurrence count; it does not discard or reselect
any coefficient or support field. The profile estimate is a conclusion
about the model stored in this same side. -/
def Result {n k : ℕ} (originalAtoms : CanonicalLiteralRectangles.Atoms (K := K) n)
    (firstIdeal secondIdeal : Ideal (𝓞 K)) (commonScalar : ℂ)
    (atoms : CanonicalLiteralRectangles.Atoms (K := K) k)
    (ray : (PUnit.{1} × PUnit.{1}) →* Circle)
    (idealMap : AllocationColumn K k → A.Exterior) (firstSign : ℝ)
    (divisor : Ideal (𝓞 K))
    (selection : primeSupport divisor → Finset (Fin (k + 2))) :=
  { output : CanonicalLiteralExceptionalPaidSource.OriginalSide (σ := σ)
      P R F (data ξ) Q.moving Q.correction Q.remaining extra
        firstSupport secondSupport window Z //
    output.count = k ∧ HEq output.atoms atoms ∧ output.ray = ray ∧ HEq output.ideal idealMap ∧
    output.firstSign = firstSign ∧ output.divisor = divisor ∧ HEq output.selection selection ∧
    output.history.originalCount = n ∧ HEq output.history.original originalAtoms ∧
    output.history.firstIdeal = firstIdeal ∧ output.history.secondIdeal = secondIdeal ∧
    (CanonicalLiteralExceptionalPaidSource.historyActualSecondInput P R extra output.history)
      .commonScalar output.history.second = commonScalar ∧
    (∀ j, Function.support (output.model.slot j) ⊆ Set.Ioo (1 : ℝ) 2) ∧
    (originalAtoms.centered = true →
      CanonicalLiteralExceptionalCharts.SamePlainProfiles output.model) ∧
    (∀ r, orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (output.model.left r) ≤
      CanonicalLiteralExceptionalProfileWindow.coefficient window hcompact hpositive
        δ₁ δ₂ orders * amplitude) ∧
    (∀ r, orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (output.model.right r) ≤
      CanonicalLiteralExceptionalProfileWindow.coefficient window hcompact hpositive
        δ₁ δ₂ orders * amplitude) ∧
    (∀ j, orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (output.model.slot j) ≤
      CanonicalLiteralExceptionalProfileWindow.coefficient window hcompact hpositive
        δ₁ δ₂ orders * amplitude) ∧
    (∀ B, originalAtoms.PrimeNormWindow B → output.atoms.PrimeNormWindow B) }

/-- The original construction already has all fields of this return
value. No additional side or profile is selected here. -/
def result : Result (σ := σ) Q ξ Z orders amplitude hcompact hpositive
    hfirstSupport F δ₁ δ₂ (secondSupport := secondSupport) seed
    (frozenSourceIdeal first.plainDivisor₁ first.plainDivisor₂ first.keep first.witness.2)
    (frozenSourceIdeal second.plainDivisor₁ second.plainDivisor₂ second.keep second.witness.2)
    ((actual).commonScalar second) finalAtoms ray (fun i => ideal (atlas.reindex.index i))
    firstSign divisor selection :=
  let bounds := side_profile_bounds Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href
    orders amplitude hamplitude original hreference ht hcompact hpositive hprime
    first hfirstSupport F power δ₁ δ₂ second hsecondSupport atlas count hleft hright hslot
    ray firstSign hfirstSign divisor selection hne hsquarefree hselection
  ⟨D, rfl, HEq.rfl, rfl, HEq.rfl, rfl, rfl, HEq.rfl,
    rfl, HEq.rfl, rfl, rfl, rfl,
    (originalComputed Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href
      orders amplitude hamplitude original hreference ht hcompact hpositive hprime
      first hfirstSupport F power δ₁ δ₂ second hsecondSupport atlas count hleft hright hslot)
        .prime_window,
    side_samePlainProfiles Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href
      orders amplitude hamplitude original hreference ht hcompact hpositive hprime
      first hfirstSupport F power δ₁ δ₂ second hsecondSupport atlas count hleft hright hslot
      ray firstSign hfirstSign divisor selection hne hsquarefree hselection,
    bounds.1, bounds.2.1, bounds.2.2,
    side_primeNormWindow Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href
      orders amplitude hamplitude original hreference ht hcompact hpositive hprime
      first hfirstSupport F power δ₁ δ₂ second hsecondSupport atlas count hleft hright hslot
      ray firstSign hfirstSign divisor selection hne hsquarefree hselection⟩

section FirstAtlas

/-- The entire remaining original construction, as a dependent
function of the actual first table. This makes the first atlas's
dictionary equality transport both the second branch and every final
allocation field together. -/
private def AfterFirst (head : Σ n : ℕ, CanonicalLiteralRectangles.Atoms (K := K) n) :=
  let placedTable := (head.2.deleteMask extra).redistributeNormFactors δ₁ δ₂
  let combined := oldScalar * ((head.2.deleteMask extra).normProfileFactor δ₁ δ₂ : ℂ)
  ∀ {secondSupport : Finset (Ideal (𝓞 K))}
    (second : SupportCartesianBranch placedTable.plain₁ placedTable.plain₂ placedTable.slots secondSupport)
    (hsecondSupport : ∀ p ∈ secondSupport, Prime p)
    {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (atlas : SourceCartesianAtlas columns ideal) (count : second.keep.card = atlas.slotCount)
    (hleft : atlas.reindex.plain₁ = (placedTable.extract second).plain₁)
    (hright : atlas.reindex.plain₂ = (placedTable.extract second).plain₂)
    (hslot : ∀ j, atlas.reindex.slots (Fin.cast count j) = (placedTable.extract second).slots j)
    (ray : (PUnit.{1} × PUnit.{1}) →* Circle)
    (firstSign : ℝ) (hfirstSign : |firstSign| ≤ 1)
    (divisor : Ideal (𝓞 K))
    (selection : primeSupport divisor → Finset (Fin (atlas.slotCount + 2)))
    (hne : (pairedAllocatedColumns divisor selection
      (((placedTable.extract second).onAtlas atlas count).plain₁)
      (((placedTable.extract second).onAtlas atlas count).plain₂)
      (((placedTable.extract second).onAtlas atlas count).slots)
      id id HeightOneSpectrum.asIdeal).Nonempty)
    (hsquarefree : Squarefree divisor)
    (hselection : selection ∈ AllocationMass.idealAllocations divisor (atlas.slotCount + 2)),
    Result (σ := σ) Q ξ Z orders amplitude hcompact hpositive hfirstSupport F δ₁ δ₂
      (secondSupport := secondSupport) seed
      (frozenSourceIdeal first.plainDivisor₁ first.plainDivisor₂ first.keep first.witness.2)
      (frozenSourceIdeal second.plainDivisor₁ second.plainDivisor₂ second.keep second.witness.2)
      (placedTable.commonScalar second)
      ((((placedTable.extract second).onAtlas atlas count).scale combined⁻¹).balancePlain (fun _ => 1))
      ray (fun i => ideal (atlas.reindex.index i)) firstSign divisor selection

private def afterFirstOriginal : AfterFirst Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    orders amplitude hcompact hpositive first hfirstSupport F power δ₁ δ₂
      ⟨first.keep.card, bare⟩ := by
  intro secondSupport second hsecondSupport ι columns ideal atlas count hleft hright hslot
    ray firstSign hfirstSign divisor selection hne hsquarefree hselection
  exact result Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href
    orders amplitude hamplitude original hreference ht hcompact hpositive hprime
    first hfirstSupport F power δ₁ δ₂ second hsecondSupport atlas count hleft hright hslot
    ray firstSign hfirstSign divisor selection hne hsquarefree hselection

variable {firstIndexType : Type*} {firstColumns : Finset firstIndexType}
variable {firstIdeal : firstIndexType → A.Exterior}
variable (firstAtlas : SourceCartesianAtlas firstColumns firstIdeal)
variable (firstIndex : AllocationColumn K first.keep.card → firstIndexType)
variable (dictionary : firstAtlas.literalDictionary =
  ⟨first.keep.card, ((bare).plain₁, (bare).plain₂), (bare).slots, firstIndex⟩)

/-- The actual first dictionary proves equality of the entire original
table, including all three occurrence carriers. This is stronger than
equality of the two slot counts. -/
private theorem first_table_eq :
    (⟨firstAtlas.slotCount,
      (bare).onAtlas firstAtlas (congrArg Sigma.fst dictionary).symm⟩ :
        Σ n : ℕ, CanonicalLiteralRectangles.Atoms (K := K) n) =
      ⟨first.keep.card, bare⟩ := by
  have he := (bare).onAtlas_eq_cast firstAtlas firstIndex dictionary
  have hc : HEq
      (cast (congrArg (CanonicalLiteralRectangles.Atoms (K := K))
        (congrArg Sigma.fst dictionary).symm) bare) bare := cast_heq _ _
  exact Sigma.ext (congrArg Sigma.fst dictionary) ((heq_of_eq he).trans hc)

/-- The actual first atlas, its actual second branch, and its original
allocation construct an exceptional side on that exact final table.
The first dictionary equality transports the whole dependent function,
so no branch, allocation, profile or child is chosen a second time.

For each of the six production cases, `dictionary` is the existing
`literal*Cover_dictionary` theorem. The final three carrier equalities
are the existing residual-atlas field identities. -/
def firstAtlasResult : AfterFirst Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    orders amplitude hcompact hpositive first hfirstSupport F power δ₁ δ₂
      ⟨firstAtlas.slotCount,
        (bare).onAtlas firstAtlas (congrArg Sigma.fst dictionary).symm⟩ := by
  have h := first_table_eq Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    first F power δ₁ δ₂ firstAtlas firstIndex dictionary
  exact h.symm ▸ afterFirstOriginal Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    reference href orders amplitude hamplitude original hreference ht hcompact hpositive
    hprime first hfirstSupport F power δ₁ δ₂

end FirstAtlas

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalOriginalSideFactory

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalOriginalSideFactory.side
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalOriginalSideFactory.side_profile_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalOriginalSideFactory.side_primeNormWindow
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalOriginalSideFactory.firstAtlasResult
