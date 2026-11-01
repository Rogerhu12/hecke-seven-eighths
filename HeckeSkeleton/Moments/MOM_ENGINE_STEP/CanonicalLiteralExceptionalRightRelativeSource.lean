import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalRelativeSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPaidRightSource

/-!
# Right cancellation at the same original first normalization

The actual source keeps its row class, two frames and two Gauss scales.
Only its smaller right common ideal selects the cancellation window.
The left allocation supplies the remaining divisor and frozen-slot loss.
The original first allowance and actual total-length discrepancy are
preserved throughout the same relative row budget.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalRightRelativeSource

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support CommonSupportMass
open CanonicalLiteralExceptionalPaidSource CanonicalLiteralExceptionalCharts
open CanonicalLiteralExceptionalPaidRightSource

variable {K : Type} [Field K] [NumberField K]

section ActualRightTerminalBounds

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
variable {Dmask : (∅ : Finset (HeightOneSpectrum A.R)).powerset}
variable (chart : SecondBlockProfileChart (E := ℝ) hΓ μv hDiff b C left right
  profiles finiteTest radius Dmask.val)
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
local notation "characters" => (rawRows).literalFiniteCharacters C P R F oldMoving
  correction pattern sector parent.theta

variable {kCommonL kCommonR : ℕ}
variable (leftAtoms : FrozenSourceAtoms A σ Orbit (rawRows).rows kCommonL)
variable (rightAtoms : FrozenSourceAtoms A σ Orbit (rawRows).rows kCommonR)
variable (thetaPair : parent.theta × parent.theta)

local notation "S" => CanonicalLiteralExceptionalFactory.rows chart P R X hX label F
  parent oldMoving correction leftAtoms rightAtoms thetaPair

variable (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (firstSupport : Finset (Ideal (𝓞 K))) (hfirst : ∀ p ∈ firstSupport, Prime p)
variable (hextra : extra = literalDeletionIdeal firstSupport hfirst)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable {window : Set ℝ} {Z : ℝ}

local notation "Input" => OriginalSide (σ := σ) P R F parent oldMoving correction remaining extra
  firstSupport (primeSupport (primePowerProduct b.primes b.leftMultiplicity).val) window Z

variable (annulus amplitude : ℝ) (hannulus : 1 ≤ annulus) (hamplitude : 0 ≤ amplitude)
variable (cap : ℕ)

variable (LD RD : Input)
variable (hleftCommon : leftAtoms.ideal = (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hrightCommon : rightAtoms.ideal = (primePowerProduct b.primes b.rightMultiplicity).val)
variable (rowProfileBound : ℝ) (hrowProfileBound : 0 ≤ rowProfileBound)
variable (hrowProfile : ∀ q ∈ (rawRows).rows, ‖chart.weight q‖ ≤ rowProfileBound)
variable {a : RealParameters} {step : ℝ}
variable (first : OriginalNominalGeometry (K := K) a Z step)
variable (slotLoss firstProfile : ℝ)

local notation "mass" => CanonicalLiteralExceptionalArithmetic.actualMass chart P R hclass
  X hX label F parent oldMoving correction leftAtoms rightAtoms thetaPair
  hleftCommon hrightCommon rowProfileBound hrowProfileBound hrowProfile
local notation "G" => CanonicalLiteralExceptionalNumbers.geometry chart X hX label first
local notation "LF" => LD.frame S C .left
local notation "RF" => RD.frame S C .right
local notation "EL" => LD.comparison S C .left
local notation "ER" => RD.comparison S C .right
local notation "rL" => (LF).allocation.rawExtractionLength Z LD.atoms.length
local notation "rR" => (RF).allocation.rawExtractionLength Z RD.atoms.length
local notation "slotError" => ∑ i ∈ Finset.univ \ (LF).allocation.keep, slotLoss
variable (normalization firstTotal : ℝ)
local notation "n" => (G).exceptionalNumbersAtNormalization mass (G).centeredExtractionLength
  rL rR slotError firstProfile normalization firstTotal

variable (hfirstL : LD.history.firstIdeal = (first.ideals.first * first.tag.extractionIdeal).val)
variable (hfirstR : RD.history.firstIdeal = (first.ideals.first * first.tag.extractionIdeal).val)
variable (hsecondL : LD.history.secondIdeal = (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hsecondR : RD.history.secondIdeal = (primePowerProduct b.primes b.rightMultiplicity).val)
variable (hplaces : CanonicalLiteralExceptionalArithmetic.thetaBadPrimes parent.theta ⊆ A.Sf)
variable (hscalar : (historyActualSecondInput P R extra LD.history).commonScalar
  LD.history.second ≠ 0)

local notation "UL" => LD.paidScales S C .left (G).skeleton.A annulus amplitude cap hannulus hamplitude
local notation "UR" => RD.paidScales S C .right (G).skeleton.A annulus amplitude cap hannulus hamplitude

variable (primitive : VolumePrimitive ψ parent.theta window)
variable (hZ : 1 < Z) (hstep : 0 ≤ step) (hq : 0 ≤ a.q)
variable (herrorPrime : ∀ e p, first.tag = .error e p →
  (Ideal.absNorm p.asIdeal : ℝ) ≤ Z ^ (step / 3))
variable (columnLoss cutoffExponent : ℝ)
variable (hradius : radius = CanonicalRowBall.gaussRadius first.retainedScale Z first.enlargement
  first.retainedScale_pos (zero_lt_one.trans hZ))
variable (hcutoff : X ≤ Z ^ cutoffExponent)
variable (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
  (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤
    Z ^ (2 * (first.skeleton.A - first.skeleton.c - first.skeleton.w + columnLoss)))
variable (hcapL : LD.history.originalCount ≤ cap) (hcapR : RD.history.originalCount ≤ cap)
variable (hprimeOriginalL : LD.history.original.PrimeNormWindow annulus)
variable (hprimeOriginalR : RD.history.original.PrimeNormWindow annulus)
variable (hproductOriginalL : LD.history.original.scaleProduct false = Z ^ (G).skeleton.A)
variable (hproductOriginalR : RD.history.original.scaleProduct false = Z ^ (G).skeleton.A)
variable (hprimeL : LD.atoms.PrimeNormWindow annulus)
variable (hprimeR : RD.atoms.PrimeNormWindow annulus)
variable (hslotL : ∀ i, SchwartzMap.seminorm ℂ 0 0 (LD.model.slot i) ≤ amplitude)
variable (hslotR : ∀ i, SchwartzMap.seminorm ℂ 0 0 (RD.model.slot i) ≤ amplitude)
variable (hamplitudeOne : 1 ≤ amplitude) (hslotLoss : annulus ≤ Z ^ (2 * slotLoss))

local notation "cutoffLoss" =>
  CanonicalLiteralExceptionalGeometry.paidCutoff columnLoss cutoffExponent 0
local notation "childExponent" =>
  (2 * ((n).Aexp - (n).c - (n).w) - (n).K₀ - (n).g - (n).g₂ - (n).V₀) +
    (a.q + (n).R₀ + (n).E₀ + (n).wo + (n).t₂ + (n).V₀) +
    ((n).b₂ - (n).p₂ + (n).w + (n).Bcommon + (n).ell)
local notation "rowFactor" => (mass).originalRowAmplitude * Z ^ ((n).g₂ - (n).t₂) /
  (Real.sqrt (LF).normalizationScale * Real.sqrt (RF).normalizationScale)

variable (hprimeLowerL : ∀ i, ∀ p ∈ LD.history.original.slots i,
  Z ^ LD.history.original.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ))
variable (hprimeLowerR : ∀ i, ∀ p ∈ RD.history.original.slots i,
  Z ^ RD.history.original.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ))
variable (hnormalization : normalization = firstLeftAllowance Z firstTotal
  first.ideals.first.val first.ideals.opposite.val)

local notation "actualWidth" =>
  secondCommonChildWidth Z ((n).Aexp - (n).c - (n).w) (a.q + (n).R₀ + (n).E₀)
    (n).wo (n).K₀ (n).g (mass).leftIdeal (mass).rightIdeal (mass).unitIdeal.val (mass).nonunitIdeal.val +
  secondCommonChildAllowance Z (n).w (n).Bcommon (n).ell (mass).leftIdeal (mass).rightIdeal
local notation "envelope" => annulus ^ cap * ((mass).commonEnvelope * orbitalFieldFactor K)
local notation "radical" => (Ideal.absNorm (commonRadical (mass).leftIdeal (mass).rightIdeal) : ℝ)

section Centered

variable (ε widthMax : ℝ) (hε : 0 < ε)
variable (hwidthMax : 0 ≤ widthMax) (hcolumnLoss : 0 ≤ columnLoss)
variable (hcutoffExponent : 0 ≤ cutoffExponent)
local notation "maskExp" =>
  CanonicalLiteralExceptionalPhysicalBox.maskExponent widthMax columnLoss cutoffExponent
local notation "hmaskExp" => CanonicalLiteralExceptionalPhysicalBox.maskExponent_nonneg
  hwidthMax hcolumnLoss hcutoffExponent
local notation "orders" => rightOrders (A := A) (σ := σ) (η := η) (hS := hS)
  primitive ε maskExp hε hmaskExp
local notation "order" => rightOrder (A := A) (σ := σ) (η := η) (hS := hS)
  primitive ε maskExp hε hmaskExp
local notation "constant" => rightConstant (A := A) (σ := σ) (η := η) (hS := hS)
  primitive ε maskExp hε hmaskExp
variable {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain true parent a Z Y₁ Y₂ floor padding)
variable (hseedLeftL : ∀ r, LD.history.original.scale₁ r = if r then Y₁ else Z ^ a.n₁)
variable (hseedRightL : ∀ r, LD.history.original.scale₂ r = if r then Y₂ else Z ^ a.n₂)
variable (hseedLeftR : ∀ r, RD.history.original.scale₁ r = if r then Y₁ else Z ^ a.n₁)
variable (hseedRightR : ∀ r, RD.history.original.scale₂ r = if r then Y₂ else Z ^ a.n₂)
variable (hcL : SamePlainProfiles LD.model) (hcR : SamePlainProfiles RD.model)
variable (hprofileL₁ : (orders).sup (schwartzSeminormFamily ℂ ℝ ℂ) (LD.model.left false) ≤ amplitude)
variable (hprofileL₂ : (orders).sup (schwartzSeminormFamily ℂ ℝ ℂ) (LD.model.right false) ≤ amplitude)
variable (hprofileR₁ : (orders).sup (schwartzSeminormFamily ℂ ℝ ℂ) (RD.model.left false) ≤ amplitude)
variable (hprofileR₂ : (orders).sup (schwartzSeminormFamily ℂ ℝ ℂ) (RD.model.right false) ≤ amplitude)
variable (horder : idealLogLength Z (primePowerProduct b.primes b.rightMultiplicity).val <
  idealLogLength Z (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hwidth : a.m + a.q ≤ widthMax)
variable (hthreshold : max 2 (Ideal.absNorm A.cS : ℝ) ≤ Z)
variable (hold : A.exteriorNorm ((F.moving P R oldMoving).effectiveFullSupport
  (remaining * extra)) ≤ Z ^ (a.q + (G).skeleton.R + (G).skeleton.E + (G).skeleton.wo + widthMax))

local notation "margin" => max ((n).Aexp - (a.m + a.q)) 0 + 3 * (n).stepσ + 5 * (n).δ / 6 + ε +
      (n).slotError + cutoffLoss / 6
local notation "coefficient" ξ => ((Γ.index : ℝ) * constant * ((UL).constant * (UR).constant)) * amplitude ^ 4 * (1 + fourierHeight ξ) ^ order

include hclass hsector hcorr hfirst hextra hone hroot hemb
  hfirstL hfirstR hsecondL hsecondR hplaces hscalar hZ hstep hq herrorPrime
  hradius hcutoff hproduct hcapL hcapR hprimeOriginalL hprimeOriginalR
  hproductOriginalL hproductOriginalR hprimeL hprimeR hslotL hslotR
  hamplitudeOne hslotLoss hprimeLowerL hprimeLowerR hnormalization domain hseedLeftL hseedRightL hseedLeftR hseedRightR
  hcL hcR hprofileL₁ hprofileL₂ hprofileR₁ hprofileR₂ horder hwidth hthreshold hold in
/-- The same original centered source, with cancellation on its smaller right
common ideal, is divided by its existing first allowance.
The source estimate and the relative row budget are both constructed inside
this theorem. The exact original total-length discrepancy stays in `remaining`. -/
theorem centered_right_relative_bound (ξ : Joint) :
    (LF).exceptionalMagnitude RF EL ER characters ξ / normalization ≤
      envelope * coefficient ξ * Z ^ ((n).remaining + margin) / radical *
        Z ^ (-idealLogLength Z LD.divisor) := by
  have hsource := CanonicalLiteralExceptionalPaidRightSource.centered_right_magnitude_bound
    (chart := chart) (P := P) (R := R) (hclass := hclass) (hsector := hsector) (X := X) (hX := hX)
    (label := label) (F := F) (parent := parent) (oldMoving := oldMoving) (correction := correction)
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms) (thetaPair := thetaPair) (hcorr := hcorr)
    (remaining := remaining) (extra := extra) (firstSupport := firstSupport) (hfirst := hfirst)
    (hextra := hextra) (hone := hone) (hroot := hroot) (hemb := hemb) (annulus := annulus)
    (amplitude := amplitude) (hannulus := hannulus) (hamplitude := hamplitude) (cap := cap) (LD := LD)
    (RD := RD) (hleftCommon := hleftCommon) (hrightCommon := hrightCommon)
    (rowProfileBound := rowProfileBound) (hrowProfileBound := hrowProfileBound)
    (hrowProfile := hrowProfile) (first := first) (slotLoss := slotLoss) (firstProfile := firstProfile)
    (hfirstL := hfirstL) (hfirstR := hfirstR) (hsecondL := hsecondL) (hsecondR := hsecondR)
    (hplaces := hplaces) (hscalar := hscalar) (primitive := primitive) (hZ := hZ) (hstep := hstep)
    (hq := hq) (herrorPrime := herrorPrime) (columnLoss := columnLoss)
    (cutoffExponent := cutoffExponent) (hradius := hradius) (hcutoff := hcutoff) (hproduct := hproduct)
    (hcapL := hcapL) (hcapR := hcapR) (hprimeOriginalL := hprimeOriginalL)
    (hprimeOriginalR := hprimeOriginalR) (hproductOriginalL := hproductOriginalL)
    (hproductOriginalR := hproductOriginalR) (hprimeL := hprimeL) (hprimeR := hprimeR)
    (hslotL := hslotL) (hslotR := hslotR) (hamplitudeOne := hamplitudeOne) (hslotLoss := hslotLoss)
    (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax) (hcolumnLoss := hcolumnLoss)
    (hcutoffExponent := hcutoffExponent) (domain := domain) (hseedLeftL := hseedLeftL)
    (hseedRightL := hseedRightL) (hseedLeftR := hseedLeftR) (hseedRightR := hseedRightR) (hcL := hcL)
    (hcR := hcR) (hprofileL₁ := hprofileL₁) (hprofileL₂ := hprofileL₂) (hprofileR₁ := hprofileR₁)
    (hprofileR₂ := hprofileR₂) (horder := horder) (hwidth := hwidth) (hthreshold := hthreshold)
    (hold := hold) ξ
  have hexponent : max ((n).Aexp - (a.m + a.q)) 0 + 3 * (n).stepσ + 5 * (n).δ / 6 + ε +
        (n).slotError - idealLogLength Z LD.divisor + cutoffLoss / 6 =
      margin - idealLogLength Z LD.divisor := by ring
  rw [hexponent] at hsource
  have hsource' : Z ^ (-actualWidth) * (LF).exceptionalMagnitude RF EL ER characters ξ ≤
      rowFactor * coefficient ξ * Z ^ (margin - idealLogLength Z LD.divisor) := by
    simpa only [secondCommonChildWidth, secondCommonChildAllowance, mul_assoc] using hsource
  have hNpos : 0 < normalization := by
    rw [hnormalization]
    exact firstLeftAllowance_pos Z firstTotal (zero_lt_one.trans hZ) _ _
  have hN := (G).exceptionalNumbersAtNormalization_normalizer mass (G).centeredExtractionLength
    rL rR slotError firstProfile normalization firstTotal hZ hNpos
  have hrow := CanonicalLiteralExceptionalRelativeSource.actual_row_budget chart P R hclass X hX label F parent oldMoving
    correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon rowProfileBound
    hrowProfileBound hrowProfile first LD RD rL rR slotError firstProfile normalization firstTotal
    annulus hannulus cap hcapL hcapR hproductOriginalL hproductOriginalR
    hprimeLowerL hprimeLowerR hfirstL hfirstR hZ hradius hnormalization
  have hrow' : rowFactor * Z ^ actualWidth / Z ^ (n).parentWidth ≤
      envelope * Z ^ (n).remaining / radical := by
    simpa only [hN] using hrow
  have henv : 0 ≤ envelope := mul_nonneg
    (pow_nonneg (zero_le_one.trans hannulus) _)
    (mul_nonneg (mass).commonEnvelope_nonneg (orbitalFieldFactor_nonneg K))
  have hradical : 0 ≤ radical := Nat.cast_nonneg _
  have hC := rightConstant_pos (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExp hε hmaskExp
  have hheight := fourierHeight_nonneg ξ
  have hUL := (UL).constant_nonneg
  have hUR := (UR).constant_nonneg
  have hcoefficient : 0 ≤ coefficient ξ := by positivity
  have hb := CanonicalExceptionalPaidNormalization.relative_of_magnitude
    Z ((LF).exceptionalMagnitude RF EL ER characters ξ) rowFactor envelope radical (coefficient ξ)
    actualWidth actualWidth (n).parentWidth (n).remaining 0 margin
    (idealLogLength Z LD.divisor) hZ.le hcoefficient henv hradical
    hsource' hrow' (by simp)
  simpa only [hN, add_zero] using hb

include hclass hsector hcorr hfirst hextra hone hroot hemb
  hfirstL hfirstR hsecondL hsecondR hplaces hscalar hZ hstep hq herrorPrime
  hradius hcutoff hproduct hcapL hcapR hprimeOriginalL hprimeOriginalR
  hproductOriginalL hproductOriginalR hprimeL hprimeR hslotL hslotR
  hamplitudeOne hslotLoss hprimeLowerL hprimeLowerR hnormalization domain hseedLeftL hseedRightL hseedLeftR hseedRightR
  hcL hcR hprofileL₁ hprofileL₂ hprofileR₁ hprofileR₂ horder hwidth hthreshold hold firstProfile in
/-- The original total length cancels its exact normalization discrepancy.
The fixed support, profile-slot and physical cutoff payments then yield
this source's final loss without a terminal remainder hypothesis. -/
theorem centered_right_small_loss_bound
    (htotal : firstTotal = first.skeleton.A +
      (first.skeleton.q + first.skeleton.R + first.skeleton.E))
    (hpadding : 0 ≤ padding)
    (loss : ℝ) (hloss : 0 ≤ loss) (hsupport : first.supportError ≤ loss / 16)
    (hvolume : ε ≤ loss / 16)
    (hslots : slotError ≤ loss / 16) (hcutoffPaid : cutoffLoss / 6 ≤ loss / 16)
    (ξ : Joint) :
    (LF).exceptionalMagnitude RF EL ER characters ξ / normalization ≤
      envelope * coefficient ξ * Z ^ ((padding + 3 * step + loss / 2) + (G).tag.exceptionalMovingLength Z step) /
        radical * Z ^ (-idealLogLength Z LD.divisor) := by
  have hb := centered_right_relative_bound
    (chart := chart) (P := P) (R := R) (hclass := hclass) (hsector := hsector) (X := X) (hX := hX)
    (label := label) (F := F) (parent := parent) (oldMoving := oldMoving) (correction := correction)
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms) (thetaPair := thetaPair) (hcorr := hcorr)
    (remaining := remaining) (extra := extra) (firstSupport := firstSupport) (hfirst := hfirst)
    (hextra := hextra) (hone := hone) (hroot := hroot) (hemb := hemb) (annulus := annulus)
    (amplitude := amplitude) (hannulus := hannulus) (hamplitude := hamplitude) (cap := cap) (LD := LD)
    (RD := RD) (hleftCommon := hleftCommon) (hrightCommon := hrightCommon)
    (rowProfileBound := rowProfileBound) (hrowProfileBound := hrowProfileBound)
    (hrowProfile := hrowProfile) (first := first) (slotLoss := slotLoss) (firstProfile := firstProfile)
    (hfirstL := hfirstL) (hfirstR := hfirstR) (hsecondL := hsecondL) (hsecondR := hsecondR)
    (hplaces := hplaces) (hscalar := hscalar) (primitive := primitive) (hZ := hZ) (hstep := hstep)
    (hq := hq) (herrorPrime := herrorPrime) (columnLoss := columnLoss)
    (cutoffExponent := cutoffExponent) (hradius := hradius) (hcutoff := hcutoff) (hproduct := hproduct)
    (hcapL := hcapL) (hcapR := hcapR) (hprimeOriginalL := hprimeOriginalL)
    (hprimeOriginalR := hprimeOriginalR) (hproductOriginalL := hproductOriginalL)
    (hproductOriginalR := hproductOriginalR) (hprimeL := hprimeL) (hprimeR := hprimeR)
    (hslotL := hslotL) (hslotR := hslotR) (hamplitudeOne := hamplitudeOne) (hslotLoss := hslotLoss)
    (normalization := normalization) (firstTotal := firstTotal) (hprimeLowerL := hprimeLowerL)
    (hprimeLowerR := hprimeLowerR) (hnormalization := hnormalization) (ε := ε) (widthMax := widthMax)
    (hε := hε) (hwidthMax := hwidthMax) (hcolumnLoss := hcolumnLoss)
    (hcutoffExponent := hcutoffExponent) (domain := domain) (hseedLeftL := hseedLeftL)
    (hseedRightL := hseedRightL) (hseedLeftR := hseedLeftR) (hseedRightR := hseedRightR) (hcL := hcL)
    (hcR := hcR) (hprofileL₁ := hprofileL₁) (hprofileL₂ := hprofileL₂) (hprofileR₁ := hprofileR₁)
    (hprofileR₂ := hprofileR₂) (horder := horder) (hwidth := hwidth) (hthreshold := hthreshold)
    (hold := hold) ξ
  have hr := CanonicalLiteralExceptionalGeometry.centered_remainder_at_normalization
    G mass (G).centeredExtractionLength rL rR slotError firstProfile normalization firstTotal
    hZ hnormalization htotal domain hpadding loss ε cutoffLoss hloss hsupport hvolume
    hslots hcutoffPaid
  have hexponent : (n).remaining + margin ≤
      (padding + 3 * step + loss / 2) + (G).tag.exceptionalMovingLength Z step := by
    simpa only [OriginalNominalGeometry.exceptionalNumbersAtNormalization,
      OriginalNominalGeometry.exceptionalNumbers, add_zero] using hr
  have hC := rightConstant_pos (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExp hε hmaskExp
  have hheight := fourierHeight_nonneg ξ
  have hUL := (UL).constant_nonneg
  have hUR := (UR).constant_nonneg
  have hcoefficient : 0 ≤ coefficient ξ := by positivity
  have henv : 0 ≤ envelope := mul_nonneg
    (pow_nonneg (zero_le_one.trans hannulus) _)
    (mul_nonneg (mass).commonEnvelope_nonneg (orbitalFieldFactor_nonneg K))
  have hp := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ.le hexponent) (mul_nonneg henv hcoefficient)
  have hd := div_le_div_of_nonneg_right hp (show 0 ≤ radical from Nat.cast_nonneg _)
  exact hb.trans (mul_le_mul_of_nonneg_right hd
    (Real.rpow_nonneg (zero_le_one.trans hZ.le) _))

end Centered

end ActualRightTerminalBounds

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalRightRelativeSource

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalRightRelativeSource.centered_right_relative_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalRightRelativeSource.centered_right_small_loss_bound
