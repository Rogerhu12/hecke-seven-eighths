import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalThetaRows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalCentralCoefficientBound

/-!
# Actual exceptional families on an original theta class

The physical chart, original common atoms and the original finite theta
class determine the row carrier. Its two restrictions retain the same
arithmetic extraction. The constructor below produces the real centered
comparison and every `ExceptionalAt` chart internally from the literal
table, then proves its atom controls and window fields.

The profiles and their divisor phases are independent of the row. Both
whole-column orientations retain the original pair of Fourier modes.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFactory

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralExceptionalCharts CanonicalLiteralExceptionalWindows

variable {K : Type} [Field K] [NumberField K]

/-- Both original comparison atoms are constructed from the actual
true rectangle; the retained prime dictionary is literally unchanged. -/
def comparison {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
    (phase : PUnit.{1} →* Circle) : SecondCoefficientComparison (d.dictionary phase false) where
  leftAtom := (d.dictionary phase true).leftAtom
  rightAtom := (d.dictionary phase true).rightAtom
  scale₁ := d.scale₁ true
  scale₂ := d.scale₂ true
  leftWeight := d.rectangleLeftWeight true
  rightWeight := d.rightWeight true
  plain₁ I hI := (d.dictionary phase true).plain₁ I hI
  plain₂ I hI := (d.dictionary phase true).plain₂ I hI

@[simp] theorem comparison_dictionary {k : ℕ}
    (d : CanonicalLiteralRectangles.Atoms (K := K) k) (phase : PUnit.{1} →* Circle) :
    (comparison d phase).dictionary = d.dictionary phase true := rfl

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
local notation "Joint" => WithLp 2 (ℝ × ℝ)
local notation "rawRows" => chart.actualRows ∅ X hX label
local notation "pattern" => chart.originalNonunitPattern ∅ X hX label
local notation "sector" => chart.originalSector P ∅ X hX label
local notation "characters" => rawRows.literalFiniteCharacters C P R F oldMoving
  correction pattern sector parent.theta

variable {kCommonL kCommonR : ℕ}
variable (leftAtoms : FrozenSourceAtoms A σ Orbit rawRows.rows kCommonL)
variable (rightAtoms : FrozenSourceAtoms A σ Orbit rawRows.rows kCommonR)
variable (thetaPair : parent.theta × parent.theta)

/-- The actual common-atom row weight is retained before the
correlation support and the original theta class are restricted. -/
def rows : ActualSecondCorrelationRows A σ Orbit (Fin b.primeCount) :=
  ((rawRows.withCommonAtoms leftAtoms rightAtoms).restrictRows
    (fun h => rawRows.correlation h ≠ 0)).restrictRows (characters.thetaClass thetaPair)

local notation "S" => rows chart P R X hX label F parent oldMoving correction
  leftAtoms rightAtoms thetaPair

/-- The displayed class selects an existing catalogue index, without
enlarging theta or requiring subgroup closure. -/
def thetaForSide (side : SecondColumnSide) : parent.theta :=
  match side with
  | .left => thetaPair.1
  | .right => thetaPair.2

include hclass hsector in
def originalRow (h : S.live) :
    CanonicalOriginalPhaseCalibration.PatternSector P S C pattern sector :=
  chart.originalReweightedPatternSector P hclass hsector ∅ X hX label
    (fun q => rawRows.weight q * leftAtoms.value q * star (rightAtoms.value q))
    (fun q => rawRows.correlation q ≠ 0) (characters.thetaClass thetaPair) h

@[simp] theorem originalRow_val_val (h : S.live) :
    (originalRow chart P R hclass hsector X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair h).val.val = h := rfl

theorem character_on_class (side : SecondColumnSide) (h : S.live) :
    S.literalCharacter C P R F oldMoving correction pattern sector h.val =
      (thetaForSide parent thetaPair side).val := by
  have htheta : characters.thetaClass thetaPair h.val := by
    have hm := (Finset.mem_filter.mp h.property).1
    exact (Finset.mem_filter.mp hm).2
  have hraw := rawRows.literalCharacter_reweighted C P R F oldMoving correction
    pattern sector
    (fun q => rawRows.weight q * leftAtoms.value q * star (rightAtoms.value q))
    (fun q => rawRows.correlation q ≠ 0) (characters.thetaClass thetaPair) h
  rw [ActualSecondCorrelationRows.literalCharacter, dif_pos h.property]
  change CanonicalLiteralAllocatedData.rowCharacter P R F oldMoving correction C S.primes
    S.leftMultiplicity S.rightMultiplicity pattern sector
      (S.extractedRow C h).momentIdeal = _
  rw [hraw]
  cases side with
  | left => exact htheta.1
  | right => exact htheta.2

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {W : d.ProfileData} {window : Set ℝ} (E : W.SchwartzModel window)
variable (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (recipe : CanonicalLiteralActualCharacters.Recipe P R F parent oldMoving
  correction remaining extra d)
variable (firstSupport : Finset (Ideal (𝓞 K)))
variable (hfirst : ∀ p ∈ firstSupport, Prime p)
variable (hextra : extra = literalDeletionIdeal firstSupport hfirst)
variable (support : d.SupportData ((primeSupport A.cS ∪ firstSupport) ∪
  primeSupport (primePowerProduct b.primes b.leftMultiplicity).val))
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (L : Ideal (𝓞 K))
variable (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "frame" => (d.factors S side χ ideal hideal firstSign false).frame C L selection hne
local notation "theta" => thetaForSide parent thetaPair side
local notation "entry" => CanonicalLiteralExceptionalCharacters.catalogue ψ parent.theta
  (CanonicalLiteralExceptionalCharacters.selectedIndex parent theta)
local notation "leftProfile" => fun ξ : Joint => profile firstSign
  (orientedMode side.literalNegative ξ) (frame.allocation.plainDivisor 0) (E.left false)
local notation "rightProfile" => fun ξ : Joint => profile firstSign
  (orientedMode side.literalNegative ξ) (frame.allocation.plainDivisor (Fin.succ 0)) (E.right false)
local notation "pairComparison" => comparison d (side.phase PUnit.{1} χ)

include hclass hsector hcorr recipe hfirst hextra support hone hroot hemb in
/-- Every chart in this family is built from the original physical
row, class equality, actual mask and original single-ideal profiles. -/
def centeredFamily (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (ξ : Joint) (h : S.live) :
    frame.source.ExceptionalAt (σ := σ) pairComparison.scale₁ pairComparison.scale₂
      (fun _ => pairComparison.leftWeight) (fun _ => pairComparison.rightWeight)
      entry (leftProfile ξ) (rightProfile ξ) ξ h :=
  CanonicalLiteralExceptionalFrames.centeredAtTheta P R F parent oldMoving correction hcorr
    C S pattern sector remaining extra hone hroot hemb
    (originalRow chart P R hclass hsector X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair h) recipe E firstSupport hfirst hextra
    b.left_positive b.right_positive support side χ ideal hideal firstSign L selection hne
    theta (character_on_class chart P R X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair side h) hc hscale ξ

include hclass hsector hcorr recipe hfirst hextra support hone hroot hemb in
def ordinaryFamily (ξ : Joint) (h : S.live) :
    frame.source.OrdinaryExceptionalAt (σ := σ)
      entry (leftProfile ξ) (rightProfile ξ) ξ h :=
  CanonicalLiteralExceptionalFrames.ordinaryAtTheta P R F parent oldMoving correction hcorr
    C S pattern sector remaining extra hone hroot hemb
    (originalRow chart P R hclass hsector X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair h) recipe E firstSupport hfirst hextra
    b.left_positive b.right_positive support side χ ideal hideal firstSign L selection hne
    theta (character_on_class chart P R X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair side h) ξ

local notation "centered" => centeredFamily chart P R hclass hsector X hX label F
  parent oldMoving correction leftAtoms rightAtoms thetaPair d E hcorr remaining extra
  recipe firstSupport hfirst hextra support hone hroot hemb side χ ideal hideal firstSign
  L selection hne
local notation "ordinary" => ordinaryFamily chart P R hclass hsector X hX label F
  parent oldMoving correction leftAtoms rightAtoms thetaPair d E hcorr remaining extra
  recipe firstSupport hfirst hextra support hone hroot hemb side χ ideal hideal firstSign
  L selection hne

theorem centered_value (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (ξ : Joint) (h : S.live) :
    (centered hc hscale ξ h).source.value =
      frame.source.centeredColumn (σ := σ) pairComparison.scale₁ pairComparison.scale₂
        (fun _ => pairComparison.leftWeight) (fun _ => pairComparison.rightWeight) ξ h :=
  ActualAllocatedSource.ExceptionalAt.value_eq_centeredColumn _

theorem ordinary_value (ξ : Joint) (h : S.live) :
    (ordinary ξ h).source.ordinaryValue = frame.source.ordinaryColumn (σ := σ) ξ h :=
  ActualAllocatedSource.OrdinaryExceptionalAt.value_eq_ordinaryColumn _

theorem centered_mask_ne_zero (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (ξ : Joint) (h : S.live) : (centered hc hscale ξ h).source.mask ≠ 0 :=
  CanonicalLiteralExceptionalWindows.centered_mask_ne_zero P R F parent oldMoving
    correction hcorr C S pattern sector remaining extra hone hroot hemb
    (originalRow chart P R hclass hsector X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair h) recipe E firstSupport hfirst hextra
    b.left_positive b.right_positive support side χ ideal hideal firstSign L selection hne
    theta (character_on_class chart P R X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair side h) hc hscale ξ

theorem ordinary_mask_ne_zero (ξ : Joint) (h : S.live) :
    (ordinary ξ h).source.mask ≠ 0 :=
  CanonicalLiteralExceptionalWindows.ordinary_mask_ne_zero P R F parent oldMoving
    correction hcorr C S pattern sector remaining extra hone hroot hemb
    (originalRow chart P R hclass hsector X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair h) recipe E firstSupport hfirst hextra
    b.left_positive b.right_positive support side χ ideal hideal firstSign L selection hne
    theta (character_on_class chart P R X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair side h) ξ

theorem centered_time_window (hsign : |firstSign| ≤ 1) (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (ξ : Joint) (h : S.live) :
    |(centered hc hscale ξ h).source.time| ≤ fourierHeight ξ :=
  CanonicalLiteralExceptionalWindows.centered_time_window P R F parent oldMoving
    correction hcorr C S pattern sector remaining extra hone hroot hemb
    (originalRow chart P R hclass hsector X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair h) recipe E firstSupport hfirst hextra
    b.left_positive b.right_positive support side χ ideal hideal firstSign L selection hne
    theta (character_on_class chart P R X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair side h) hsign hc hscale ξ

theorem ordinary_time_window (hsign : |firstSign| ≤ 1) (ξ : Joint) (h : S.live) :
    |(ordinary ξ h).source.time| ≤ fourierHeight ξ :=
  CanonicalLiteralExceptionalWindows.ordinary_time_window P R F parent oldMoving
    correction hcorr C S pattern sector remaining extra hone hroot hemb
    (originalRow chart P R hclass hsector X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair h) recipe E firstSupport hfirst hextra
    b.left_positive b.right_positive support side χ ideal hideal firstSign L selection hne
    theta (character_on_class chart P R X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair side h) hsign ξ

/-- The four profile controls in the uniform terminal are precisely
those of the original model, for all rows of the same theta class. -/
theorem profile_seminorms (ξ : Joint) (orders : Finset (ℕ × ℕ)) :
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (leftProfile ξ) =
        orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.left false) ∧
      orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (rightProfile ξ) =
        orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.right false) :=
  ⟨profile_seminorm _ _ _ _ _, profile_seminorm _ _ _ _ _⟩

theorem profile_supports (ξ : Joint) :
    tsupport (leftProfile ξ) ⊆ window ∧ tsupport (rightProfile ξ) ⊆ window :=
  ⟨(profile_support _ _ _ _).trans (E.left_support false),
    (profile_support _ _ _ _).trans (E.right_support false)⟩

variable (annulus amplitude : ℝ) (hannulus : 1 ≤ annulus) (hamplitude : 0 ≤ amplitude)
variable (hprime : d.PrimeNormWindow annulus)
variable (hprofile : ∀ i, SchwartzMap.seminorm ℂ 0 0 (E.slot i) ≤ amplitude)

local notation "scales" => CanonicalLiteralExceptionalAtoms.scales d S C side χ ideal
  hideal firstSign L selection hne annulus amplitude hannulus hamplitude

include hprime hprofile in
/-- The complete atom control is proved from the original one-prime
annulus and the displayed original seminorm, on this same allocation. -/
def centeredAtomicControl (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (ξ : Joint) (h : S.live) :
    (centered hc hscale ξ h).source.AtomicControl d.base scales := by
  have hmask : d.characters.MaskIndicator := by
    rw [recipe.characters]
    exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator
      P R F parent oldMoving correction remaining extra recipe.slots.index
  exact CanonicalLiteralExceptionalAtoms.centeredControl d E S C side χ ideal hideal
    firstSign L selection hne annulus amplitude hannulus hamplitude hmask hprime hprofile
      (centered hc hscale ξ h)

include hprime hprofile in
def ordinaryAtomicControl (ξ : Joint) (h : S.live) :
    (ordinary ξ h).source.AtomicControl d.base scales := by
  have hmask : d.characters.MaskIndicator := by
    rw [recipe.characters]
    exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator
      P R F parent oldMoving correction remaining extra recipe.slots.index
  exact CanonicalLiteralExceptionalAtoms.ordinaryControl d E S C side χ ideal hideal
    firstSign L selection hne annulus amplitude hannulus hamplitude hmask hprime hprofile
      (ordinary ξ h)

section PhysicalWindow

variable (retainedScale g a₀ q wo cutoffExponent : ℝ)
variable (hretained : 0 < retainedScale)
variable (hradius : radius = CanonicalRowBall.gaussRadius retainedScale d.base g hretained
  (zero_lt_one.trans d.base_gt_one))
variable (hcutoff : X ≤ d.base ^ cutoffExponent)
variable (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
  (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ d.base ^ (2 * a₀))
variable (hold : A.exteriorNorm ((F.moving P R oldMoving).effectiveFullSupport
  (remaining * extra)) ≤ d.base ^ (q + wo))

local notation "actualWidth" =>
  secondCommonChildWidth d.base a₀ q wo (Real.log retainedScale / Real.log d.base) g
    (primePowerProduct b.primes b.leftMultiplicity).val
    (primePowerProduct b.primes b.rightMultiplicity).val
    (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern).val
    (secondPatternNonunitIdeal b.primes pattern).val +
      idealLogLength d.base (secondSixthRootIdeal b.primes
        b.leftMultiplicity b.rightMultiplicity).val + cutoffExponent

include hradius hcutoff hproduct hold in
theorem centered_mask_window (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (ξ : Joint) (h : S.live) :
    (Ideal.absNorm (centered hc hscale ξ h).source.mask : ℝ) ≤
      (Ideal.absNorm A.cS : ℝ) * d.base ^ (actualWidth) := by
  rw [(CanonicalLiteralExceptionalWindows.centered_fields P R F parent oldMoving
    correction hcorr C S pattern sector remaining extra hone hroot hemb
    (originalRow chart P R hclass hsector X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair h) recipe E firstSupport hfirst hextra
    b.left_positive b.right_positive support side χ ideal hideal firstSign L selection hne
    theta (character_on_class chart P R X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair side h) hc hscale ξ).1]
  exact actualRestrictedRows_mask_norm_window chart hclass P R F oldMoving
    (remaining * extra) X hX label retainedScale d.base g a₀ q wo cutoffExponent
    hretained d.base_gt_one hradius hcutoff hproduct hold
    (fun q => rawRows.weight q * leftAtoms.value q * star (rightAtoms.value q))
    (fun q => rawRows.correlation q ≠ 0) (characters.thetaClass thetaPair) h

include hradius hcutoff hproduct hold in
theorem ordinary_mask_window (ξ : Joint) (h : S.live) :
    (Ideal.absNorm (ordinary ξ h).source.mask : ℝ) ≤
      (Ideal.absNorm A.cS : ℝ) * d.base ^ (actualWidth) := by
  rw [(CanonicalLiteralExceptionalWindows.ordinary_fields P R F parent oldMoving
    correction hcorr C S pattern sector remaining extra hone hroot hemb
    (originalRow chart P R hclass hsector X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair h) recipe E firstSupport hfirst hextra
    b.left_positive b.right_positive support side χ ideal hideal firstSign L selection hne
    theta (character_on_class chart P R X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair side h) ξ).1]
  exact actualRestrictedRows_mask_norm_window chart hclass P R F oldMoving
    (remaining * extra) X hX label retainedScale d.base g a₀ q wo cutoffExponent
    hretained d.base_gt_one hradius hcutoff hproduct hold
    (fun q => rawRows.weight q * leftAtoms.value q * star (rightAtoms.value q))
    (fun q => rawRows.correlation q ≠ 0) (characters.thetaClass thetaPair) h

end PhysicalWindow

section OriginalScales

variable {a : RealParameters} {Z step Y₁ Y₂ floor padding : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)
variable {ι₁ ι₂ : Type*} {columns₁ : Finset ι₁} {columns₂ : Finset ι₂}
variable {ideal₁ : ι₁ → A.Exterior} {ideal₂ : ι₂ → A.Exterior}
variable (first : SourceCartesianAtlas columns₁ ideal₁)
variable (second : SourceCartesianAtlas columns₂ ideal₂)
variable (support₁ support₂ : Finset (Ideal (𝓞 K)))
variable (label₁ : first.labels support₁ (G.ideals.first * G.tag.extractionIdeal).val)
variable (label₂ : second.labels support₂ G.centeredSecondIdeal.val)

local notation "b₁" => first.branch support₁ (G.ideals.first * G.tag.extractionIdeal).val label₁
local notation "b₂" => second.branch support₂ G.centeredSecondIdeal.val label₂

variable (domain : PairedEngineDomain true parent a Z Y₁ Y₂ floor padding)
variable (left_scale_eq : ∀ r, d.scale₁ r =
  (if r then Y₁ else Z ^ a.n₁) / idealNorm K (b₁.plainDivisor₁ * b₂.plainDivisor₁))
variable (right_scale_eq : ∀ r, d.scale₂ r =
  (if r then Y₂ else Z ^ a.n₂) / idealNorm K (b₁.plainDivisor₂ * b₂.plainDivisor₂))

include domain left_scale_eq right_scale_eq in
/-- The balanced comparison product is a consequence of the original
domain and the two literal quotient identities. The incoming actual
table obtains those identities from `actual_final_left_scale` and
`actual_final_right_scale`, including the pool prime power when present. -/
theorem comparison_product_of_original_scales :
    d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false := by
  rw [left_scale_eq true, right_scale_eq true, left_scale_eq false, right_scale_eq false]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [div_mul_div_comm, div_mul_div_comm, domain.comparison_product_eq_power rfl,
    Real.rpow_add (zero_lt_one.trans domain.scale)]

local notation "originalProduct" => comparison_product_of_original_scales parent d
  G first second support₁ support₂ label₁ label₂ domain left_scale_eq right_scale_eq

include hclass hsector hcorr recipe hfirst hextra support hone hroot hemb
  domain left_scale_eq right_scale_eq in
/-- The original domain chooses the comparison product before any
row or Fourier variable. No completed centered source or final scale
window is supplied. -/
def centeredOriginalFamily (hc : SamePlainProfiles E) (ξ : Joint) (h : S.live) :
    frame.source.ExceptionalAt (σ := σ) pairComparison.scale₁ pairComparison.scale₂
      (fun _ => pairComparison.leftWeight) (fun _ => pairComparison.rightWeight)
      entry (leftProfile ξ) (rightProfile ξ) ξ h :=
  centered hc originalProduct ξ h

local notation "originalCentered" => centeredOriginalFamily chart P R hclass hsector
  X hX label F parent oldMoving correction leftAtoms rightAtoms thetaPair d E hcorr
  remaining extra recipe firstSupport hfirst hextra support hone hroot hemb side χ
  ideal hideal firstSign L selection hne G first second support₁ support₂ label₁ label₂
  domain left_scale_eq right_scale_eq

/-- Both actual pre-divisors divide the same complete common ideal.
The four quotient minimum, including the original final allocation,
is derived internally from those labels and the centered domain. -/
theorem centered_original_minimum (hc : SamePlainProfiles E) (ξ : Joint) (h : S.live) :
    Z ^ ((a.m + a.q) / 4 - G.centeredExtractionLength -
      frame.allocation.rawExtractionLength Z d.length) ≤
        (originalCentered hc ξ h).source.lower :=
  CanonicalLiteralExceptionalWindows.centered_minimum_window P R F parent oldMoving
    correction hcorr C S pattern sector remaining extra hone hroot hemb
    (originalRow chart P R hclass hsector X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair h) recipe E firstSupport hfirst hextra
    b.left_positive b.right_positive support side χ ideal hideal firstSign L selection hne
    theta (character_on_class chart P R X hX label F parent oldMoving correction
      leftAtoms rightAtoms thetaPair side h)
    G first second support₁ support₂ label₁ label₂ domain left_scale_eq right_scale_eq
    hc originalProduct ξ

include hclass hsector hcorr recipe hfirst hextra support hone hroot hemb
  domain left_scale_eq right_scale_eq in
/-- This is the family type consumed directly by the paid uniform
terminal on the original exceptional subtype. Its extra membership
proof does not change the row, the catalogue entry, or any profile. -/
def centeredTerminalFamily (hc : SamePlainProfiles E) (ξ : Joint)
    (h : S.exceptionalRows characters) :
    frame.source.ExceptionalAt (σ := σ) pairComparison.scale₁ pairComparison.scale₂
      (fun _ => pairComparison.leftWeight) (fun _ => pairComparison.rightWeight)
      entry (leftProfile ξ) (rightProfile ξ) ξ h.val :=
  originalCentered hc ξ h.val

end OriginalScales

include hclass hsector hcorr recipe hfirst hextra support hone hroot hemb in
/-- The ordinary branch uses the same source and class, and does not
read either unused comparison scale. -/
def ordinaryTerminalFamily (ξ : Joint) (h : S.exceptionalRows characters) :
    frame.source.OrdinaryExceptionalAt (σ := σ)
      entry (leftProfile ξ) (rightProfile ξ) ξ h.val :=
  ordinary ξ h.val

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFactory

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFactory.character_on_class
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFactory.centeredFamily
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFactory.centeredAtomicControl
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFactory.centered_mask_window
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFactory.comparison_product_of_original_scales
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFactory.centered_original_minimum
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFactory.centeredTerminalFamily
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFactory.ordinaryTerminalFamily
