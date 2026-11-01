import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPaidSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalRightTerminal

/-!
# The actual right cancellation window on the same literal rows

The original physical rows, common atoms, two frames and their paired
magnitude are unchanged. When the right common ideal is strictly smaller,
its actual four quotient scales supply the centered cancellation window.
The left allocation pays the remaining divisor loss. Neither a swapped
row classifier nor a replacement source is constructed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidRightSource

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralExceptionalCharts CanonicalLiteralExceptionalWindows
open CanonicalLiteralExceptionalPaidSource

variable {K : Type} [Field K] [NumberField K]

section UniformVolume

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ψ : HeckeCharacter K} {theta : Finset (HeckeCharacter K)} {window : Set ℝ}
variable (primitive : VolumePrimitive ψ theta window)
variable (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent)

include A σ η hS

private def rightExistence :=
  CanonicalExceptionalTerminal.exists_original_magnitude_terminal_with_right_cutoff
    (A := A) (σ := σ) (η := η) (hS := hS) (V := WithLp 2 (ℝ × ℝ))
    (characterCatalogue ψ theta) primitive.density primitive.remainder
    primitive.continuous primitive.volume window primitive.compact primitive.positive
    ε maskExponent hε hmask

def rightOrders : Finset (ℕ × ℕ) :=
  (rightExistence (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask).choose

def rightOrder : ℕ :=
  (rightExistence (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask).choose_spec.2.choose

def rightConstant : ℝ :=
  (rightExistence (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask).choose_spec.2.choose_spec.choose

theorem rightOrders_zero :
    (0, 0) ∈ rightOrders (A := A) (σ := σ) (η := η) (hS := hS)
      primitive ε maskExponent hε hmask :=
  (rightExistence (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask).choose_spec.1

theorem rightConstant_pos :
    0 < rightConstant (A := A) (σ := σ) (η := η) (hS := hS)
      primitive ε maskExponent hε hmask :=
  (rightExistence (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask).choose_spec.2.choose_spec.choose_spec.1

private def rightEstimate :=
  (rightExistence (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask).choose_spec.2.choose_spec.choose_spec.2

end UniformVolume

section ActualRows

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
local notation "characters" => rawRows.literalFiniteCharacters C P R F oldMoving
  correction pattern sector parent.theta

variable {kCommonL kCommonR : ℕ}
variable (leftAtoms : FrozenSourceAtoms A σ Orbit rawRows.rows kCommonL)
variable (rightAtoms : FrozenSourceAtoms A σ Orbit rawRows.rows kCommonR)
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

section Pair

variable (LD RD : Input)
variable (hleftCommon : leftAtoms.ideal = (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hrightCommon : rightAtoms.ideal = (primePowerProduct b.primes b.rightMultiplicity).val)
variable (rowProfileBound : ℝ) (hrowProfileBound : 0 ≤ rowProfileBound)
variable (hrowProfile : ∀ q ∈ rawRows.rows, ‖chart.weight q‖ ≤ rowProfileBound)
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
local notation "rL" => LF.allocation.rawExtractionLength Z LD.atoms.length
local notation "rR" => RF.allocation.rawExtractionLength Z RD.atoms.length
local notation "slotError" => ∑ i ∈ Finset.univ \ LF.allocation.keep, slotLoss
local notation "n" => CanonicalLiteralExceptionalNumbers.numbers chart P R hclass X hX label F
  parent oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
  rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile

variable (hfirstL : LD.history.firstIdeal = (first.ideals.first * first.tag.extractionIdeal).val)
variable (hfirstR : RD.history.firstIdeal = (first.ideals.first * first.tag.extractionIdeal).val)
variable (hsecondL : LD.history.secondIdeal = (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hsecondR : RD.history.secondIdeal = (primePowerProduct b.primes b.rightMultiplicity).val)
variable (hplaces : CanonicalLiteralExceptionalArithmetic.thetaBadPrimes parent.theta ⊆ A.Sf)
variable (hscalar : (historyActualSecondInput P R extra LD.history).commonScalar
  LD.history.second ≠ 0)

local notation "UL" => LD.paidScales S C .left G.skeleton.A annulus amplitude cap hannulus hamplitude
local notation "UR" => RD.paidScales S C .right G.skeleton.A annulus amplitude cap hannulus hamplitude

section CenteredWindows

variable {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain true parent a Z Y₁ Y₂ floor padding)
variable (hseedLeftR : ∀ r, RD.history.original.scale₁ r = if r then Y₁ else Z ^ a.n₁)
variable (hseedRightR : ∀ r, RD.history.original.scale₂ r = if r then Y₂ else Z ^ a.n₂)
variable (hcR : SamePlainProfiles RD.model)

local notation "prodR" => RD.comparison_product domain hseedLeftR hseedRightR
local notation "TR" => OriginalSide.actualCentered chart P R hclass hsector X hX label
  F parent oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
  firstSupport hfirst hextra hone hroot hemb RD .right hcR prodR

variable (horder : idealLogLength Z (primePowerProduct b.primes b.rightMultiplicity).val <
  idealLogLength Z (primePowerProduct b.primes b.leftMultiplicity).val)

include hfirstR hsecondR horder in
/-- The actual two pre-divisors belong to the smaller original
common ideal. The centered quarter-width minimum then follows from
the original domain, including the final allocated divisors. -/
theorem centered_right_minimum (ξ : Joint) (h : S.exceptionalRows characters) :
    Z ^ ((a.m + a.q) / 4 - G.centeredExtractionLength - rR) ≤ (TR ξ h).source.lower := by
  have hchoose : G.centeredSecondIdeal = G.ideals.secondOpposite := by
    apply if_neg
    exact not_le_of_gt horder
  have hcommon : RD.history.firstIdeal * RD.history.secondIdeal =
      G.centeredCommonIdeal.val := by
    rw [hfirstR, hsecondR]
    change _ = (G.ideals.first * G.tag.extractionIdeal * G.centeredSecondIdeal).val
    rw [hchoose]
    rfl
  have hp := RD.preDivisors_dvd
  rw [hcommon] at hp
  have hmin := G.fourPlain_minimum_window_of_domain RF.allocation domain
    (RD.history.first.plainDivisor₁ * RD.history.second.plainDivisor₁)
    (RD.history.first.plainDivisor₂ * RD.history.second.plainDivisor₂)
    hp.1 hp.2 RD.atoms.length (fun i => (RD.atoms.length_pos i).le)
  have hf := CanonicalLiteralExceptionalWindows.centered_fields P R F parent oldMoving
    correction hcorr C S pattern sector remaining extra hone hroot hemb
    (CanonicalLiteralExceptionalFactory.originalRow chart P R hclass hsector X hX label
      F parent oldMoving correction leftAtoms rightAtoms thetaPair h.val)
    RD.recipe RD.model firstSupport hfirst hextra b.left_positive b.right_positive RD.support
    .right RD.ray RD.ideal RD.ideal_eq RD.firstSign RD.divisor RD.selection RD.nonempty
    thetaPair.2 (CanonicalLiteralExceptionalFactory.character_on_class chart P R X hX
      label F parent oldMoving correction leftAtoms rightAtoms thetaPair .right h.val)
    hcR prodR ξ
  rw [hf.2.2, RD.left_scale_eq false, RD.right_scale_eq false,
    RD.left_scale_eq true, RD.right_scale_eq true, hseedLeftR false, hseedRightR false,
    hseedLeftR true, hseedRightR true]
  simpa only [Bool.false_eq_true, if_false, if_true] using hmin

variable (columnLoss cutoffExponent widthMax : ℝ)
variable (hZ : 1 < Z) (hstep : 0 ≤ step)
variable (hwidth : a.m + a.q ≤ widthMax)
variable (hthreshold : max 2 (Ideal.absNorm A.cS : ℝ) ≤ Z)
variable (hradius : radius = CanonicalRowBall.gaussRadius first.retainedScale Z first.enlargement
  first.retainedScale_pos (zero_lt_one.trans hZ))
variable (hcutoff : X ≤ Z ^ cutoffExponent)
variable (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
  (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤
    Z ^ (2 * (first.skeleton.A - first.skeleton.c - first.skeleton.w + columnLoss)))
variable (hold : A.exteriorNorm ((F.moving P R oldMoving).effectiveFullSupport
  (remaining * extra)) ≤ Z ^ (a.q + G.skeleton.R + G.skeleton.E + G.skeleton.wo))

include hstep hwidth hthreshold hradius hcutoff hproduct hold in
/-- A fixed parent box bounds the actual complete mask. Its initial
bad-prime ideal costs one fixed threshold and one exponent, while the
original physical cutoff cost remains explicit. -/
theorem centered_right_mask (ξ : Joint) (h : S.exceptionalRows characters) :
    (Ideal.absNorm (TR ξ h).source.mask : ℝ) ≤
      Z ^ CanonicalLiteralExceptionalPhysicalBox.maskExponent
        widthMax columnLoss cutoffExponent := by
  have hradius' : radius = CanonicalRowBall.gaussRadius first.retainedScale
      RD.atoms.base first.enlargement first.retainedScale_pos
        (zero_lt_one.trans RD.atoms.base_gt_one) := by
    simpa only [RD.base_eq] using hradius
  have hcutoff' : X ≤ RD.atoms.base ^ cutoffExponent := by
    simpa only [RD.base_eq] using hcutoff
  have hproduct' : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤
        RD.atoms.base ^ (2 * (G.skeleton.A - G.skeleton.c - G.skeleton.w + columnLoss)) := by
    simpa only [RD.base_eq] using hproduct
  have hold' : A.exteriorNorm ((F.moving P R oldMoving).effectiveFullSupport
      (remaining * extra)) ≤
      RD.atoms.base ^ ((a.q + G.skeleton.R + G.skeleton.E) + G.skeleton.wo) := by
    simpa only [RD.base_eq] using hold
  have hm := CanonicalLiteralExceptionalFactory.centered_mask_window chart P R hclass hsector
    X hX label F parent oldMoving correction leftAtoms rightAtoms thetaPair RD.atoms RD.model
    hcorr remaining extra RD.recipe firstSupport hfirst hextra RD.support hone hroot hemb
    .right RD.ray RD.ideal RD.ideal_eq RD.firstSign RD.divisor RD.selection RD.nonempty
    first.retainedScale first.enlargement
    (G.skeleton.A - G.skeleton.c - G.skeleton.w + columnLoss)
    (a.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo cutoffExponent
    first.retainedScale_pos hradius' hcutoff' hproduct' hold' hcR prodR ξ h.val
  have hm' : (Ideal.absNorm (TR ξ h).source.mask : ℝ) ≤
      (Ideal.absNorm A.cS : ℝ) *
        Z ^ CanonicalLiteralExceptionalPhysicalBox.physicalWidth G b.primes
          b.leftMultiplicity b.rightMultiplicity pattern columnLoss cutoffExponent := by
    simpa only [RD.base_eq] using hm
  exact hm'.trans ((fixed_mask_threshold Z _ hthreshold).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le
      (CanonicalLiteralExceptionalPhysicalBox.physicalWidth_add_one_le G b.primes
        b.leftMultiplicity b.rightMultiplicity b.left_positive b.right_positive pattern
        widthMax columnLoss cutoffExponent hZ hstep hwidth)))

end CenteredWindows

section Terminal

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
variable (hproductOriginalL : LD.history.original.scaleProduct false = Z ^ G.skeleton.A)
variable (hproductOriginalR : RD.history.original.scaleProduct false = Z ^ G.skeleton.A)
variable (hprimeL : LD.atoms.PrimeNormWindow annulus)
variable (hprimeR : RD.atoms.PrimeNormWindow annulus)
variable (hslotL : ∀ i, SchwartzMap.seminorm ℂ 0 0 (LD.model.slot i) ≤ amplitude)
variable (hslotR : ∀ i, SchwartzMap.seminorm ℂ 0 0 (RD.model.slot i) ≤ amplitude)
variable (hamplitudeOne : 1 ≤ amplitude) (hslotLoss : annulus ≤ Z ^ (2 * slotLoss))

local notation "cutoffLoss" =>
  CanonicalLiteralExceptionalGeometry.paidCutoff columnLoss cutoffExponent 0
local notation "childExponent" =>
  (2 * (n.Aexp - n.c - n.w) - n.K₀ - n.g - n.g₂ - n.V₀) +
    (a.q + n.R₀ + n.E₀ + n.wo + n.t₂ + n.V₀) +
    (n.b₂ - n.p₂ + n.w + n.Bcommon + n.ell)
local notation "rowFactor" => mass.originalRowAmplitude * Z ^ (n.g₂ - n.t₂) /
  (Real.sqrt LF.normalizationScale * Real.sqrt RF.normalizationScale)

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
variable (hprofileL₁ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (LD.model.left false) ≤ amplitude)
variable (hprofileL₂ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (LD.model.right false) ≤ amplitude)
variable (hprofileR₁ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (RD.model.left false) ≤ amplitude)
variable (hprofileR₂ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (RD.model.right false) ≤ amplitude)
variable (horder : idealLogLength Z (primePowerProduct b.primes b.rightMultiplicity).val <
  idealLogLength Z (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hwidth : a.m + a.q ≤ widthMax)
variable (hthreshold : max 2 (Ideal.absNorm A.cS : ℝ) ≤ Z)
variable (hold : A.exteriorNorm ((F.moving P R oldMoving).effectiveFullSupport
  (remaining * extra)) ≤ Z ^ (a.q + G.skeleton.R + G.skeleton.E + G.skeleton.wo))

local notation "prodL" => LD.comparison_product domain hseedLeftL hseedRightL
local notation "prodR" => RD.comparison_product domain hseedLeftR hseedRightR
local notation "TL" => OriginalSide.actualCentered chart P R hclass hsector X hX label
  F parent oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
  firstSupport hfirst hextra hone hroot hemb LD .left hcL prodL
local notation "TR" => OriginalSide.actualCentered chart P R hclass hsector X hX label
  F parent oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
  firstSupport hfirst hextra hone hroot hemb RD .right hcR prodR

include hclass hsector hcorr hfirst hextra hone hroot hemb
  hfirstL hfirstR hsecondL hsecondR hplaces hscalar hZ hstep hq herrorPrime
  hradius hcutoff hproduct hcapL hcapR hprimeOriginalL hprimeOriginalR
  hproductOriginalL hproductOriginalR hprimeL hprimeR hslotL hslotR
  hamplitudeOne hslotLoss domain hseedLeftL hseedRightL hseedLeftR hseedRightR
  hcL hcR hprofileL₁ hprofileL₂ hprofileR₁ hprofileR₂ horder hwidth hthreshold hold in
/-- The smaller actual right common ideal supplies the centered
window, on precisely the same physical row class and paired magnitude.
The remaining divisor loss is paid by the original left allocation. -/
theorem centered_right_magnitude_bound (ξ : Joint) :
    Z ^ (-childExponent) * LF.exceptionalMagnitude RF EL ER characters ξ ≤
      rowFactor * ((Γ.index : ℝ) * constant * (UL.constant * UR.constant)) * amplitude ^ 4 *
        (1 + fourierHeight ξ) ^ order *
        Z ^ (max (n.Aexp - (a.m + a.q)) 0 + 3 * n.stepσ + 5 * n.δ / 6 + ε +
          n.slotError - idealLogLength Z LD.divisor + cutoffLoss / 6) := by
  have hC := rightConstant_pos (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExp hε hmaskExp
  have hrow0 := mass.originalRowAmplitude_nonneg
  have hUL := UL.constant_nonneg
  have hUR := UR.constant_nonneg
  by_cases hlive : Nonempty S.live
  · let row : S.live := Classical.choice hlive
    obtain ⟨base, hfactor, hvaluation⟩ := actual_classification
      chart P R hclass hsector X hX label F parent oldMoving correction leftAtoms rightAtoms
      thetaPair hcorr remaining extra firstSupport LD hsecondL hplaces hscalar
    have hPL := LD.profile_supports S C .left ξ
    have hPR := RD.profile_supports S C .right ξ
    have hSL := LD.profile_seminorms S C .left ξ orders
    have hSR := RD.profile_seminorms S C .right ξ orders
    have hAL (h : S.exceptionalRows characters) : (TL ξ h).source.AtomicControl Z UL :=
      OriginalSide.actualCenteredPaidAtoms chart P R hclass hsector X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
        firstSupport hfirst hextra hone hroot hemb LD .left annulus amplitude hannulus
        hamplitude hprimeL hslotL G.skeleton.A cap hcapL hprimeOriginalL hproductOriginalL
        hZ hcL prodL ξ h
    have hAR (h : S.exceptionalRows characters) : (TR ξ h).source.AtomicControl Z UR :=
      OriginalSide.actualCenteredPaidAtoms chart P R hclass hsector X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
        firstSupport hfirst hextra hone hroot hemb RD .right annulus amplitude hannulus
        hamplitude hprimeR hslotR G.skeleton.A cap hcapR hprimeOriginalR hproductOriginalR
        hZ hcR prodR ξ h
    have hmin (h : S.exceptionalRows characters) :
        Z ^ ((a.m + a.q) / 4 - n.vStar - n.r₂) ≤ (TR ξ h).source.lower :=
      centered_right_minimum (chart := chart) (P := P) (R := R) (hclass := hclass)
        (hsector := hsector) (F := F) (parent := parent) (oldMoving := oldMoving)
        (correction := correction) (hcorr := hcorr) (leftAtoms := leftAtoms)
        (rightAtoms := rightAtoms) (thetaPair := thetaPair) (remaining := remaining)
        (extra := extra) (firstSupport := firstSupport) (hfirst := hfirst) (hextra := hextra)
        (hone := hone) (hroot := hroot) (hemb := hemb) (RD := RD) (first := first)
        (hfirstR := hfirstR) (hsecondR := hsecondR) (domain := domain)
        (hseedLeftR := hseedLeftR) (hseedRightR := hseedRightR) (hcR := hcR)
        (horder := horder) ξ h
    have hmask (h : S.exceptionalRows characters) :
        (Ideal.absNorm (TR ξ h).source.mask : ℝ) ≤ Z ^ maskExp :=
      centered_right_mask (chart := chart) (P := P) (R := R) (hclass := hclass)
        (hsector := hsector) (F := F) (parent := parent) (oldMoving := oldMoving)
        (correction := correction) (hcorr := hcorr) (leftAtoms := leftAtoms)
        (rightAtoms := rightAtoms) (thetaPair := thetaPair) (remaining := remaining)
        (extra := extra) (firstSupport := firstSupport) (hfirst := hfirst) (hextra := hextra)
        (hone := hone) (hroot := hroot) (hemb := hemb) (RD := RD) (first := first)
        (domain := domain) (hseedLeftR := hseedLeftR) (hseedRightR := hseedRightR)
        (hcR := hcR) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
        (widthMax := widthMax) (hZ := hZ) (hstep := hstep) (hwidth := hwidth)
        (hthreshold := hthreshold) (hradius := hradius) (hcutoff := hcutoff)
        (hproduct := hproduct) (hold := hold) ξ h
    have hb := rightEstimate (A := A) (σ := σ) (η := η) (hS := hS)
      primitive ε maskExp hε hmaskExp
      (CanonicalLiteralExceptionalCharacters.selectedIndex parent thetaPair.1)
      (CanonicalLiteralExceptionalCharacters.selectedIndex parent thetaPair.2)
      (LD.leftProfile S C .left ξ) (LD.rightProfile S C .left ξ)
      (RD.leftProfile S C .right ξ) (RD.rightProfile S C .right ξ)
      hPL.1 hPL.2 hPR.1 hPR.2 amplitude hamplitudeOne
      (hSL.1.le.trans hprofileL₁) (hSL.2.le.trans hprofileL₂)
      (hSR.1.le.trans hprofileR₁) (hSR.2.le.trans hprofileR₂)
      C S LF RF EL ER characters ξ (TL ξ) (TR ξ) UL UR
      Z n.Aexp a.m a.q n.c n.d n.R₀ n.E₀ n.K₀ n.w n.wo n.Bcommon n.g n.ell
      n.b₂ n.p₂ n.g₂ n.t₂ n.V₀ n.v n.vStar n.r₁ n.r₂ (idealLogLength Z LD.divisor)
      n.slotError cutoffLoss (Γ.index : ℝ) (fourierHeight ξ) n.stepσ n.δ mass.originalRowAmplitude
      hZ.le
      (CanonicalLiteralExceptionalNumbers.v_nonneg chart P R hclass X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
        rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile hZ)
      (RF.allocation.rawExtractionLength_nonneg Z hZ RD.atoms.length
        (fun i => (RD.atoms.length_pos i).le))
      (LD.divisor_window S C .left annulus slotLoss hZ hprimeL hslotLoss)
      (Nat.cast_nonneg Γ.index) (fourierHeight_nonneg ξ) hrow0 hAL hAR
      (paid_atom_exponent chart P R hclass X hX label F parent oldMoving correction
        leftAtoms rightAtoms thetaPair remaining extra firstSupport annulus amplitude
        hannulus hamplitude cap LD RD hleftCommon hrightCommon rowProfileBound
        hrowProfileBound hrowProfile first slotLoss firstProfile hfirstL hfirstR hsecondL hsecondR)
      b.left_positive
      (CanonicalLiteralExceptionalNumbers.gcd_window chart P R hclass X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
        rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile hZ)
      (fun h hh => CanonicalLiteralExceptionalNumbers.unit_window chart P R hclass X hX
        label F parent oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon
        hrightCommon rowProfileBound hrowProfileBound hrowProfile first rL rR slotError
        firstProfile hZ h (Finset.mem_filter.mp hh).1)
      (fun h hh => mass.original_row_weight_bound h (Finset.mem_filter.mp hh).1)
      base.val (fun h => hvaluation h.val) (fun h => hfactor h.val)
      (fun h => CanonicalLiteralExceptionalNumbers.radical_window chart P R hclass X hX
        label F parent oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon
        hrightCommon rowProfileBound hrowProfileBound hrowProfile first rL rR slotError
        firstProfile hZ h.val.val (Finset.mem_filter.mp h.val.property).1)
      (fun h => CanonicalLiteralExceptionalNumbers.cutoff_window chart P R hclass X hX
        label F parent oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon
        hrightCommon rowProfileBound hrowProfileBound hrowProfile first rL rR slotError
        firstProfile columnLoss cutoffExponent hZ hradius hcutoff hproduct h.val)
      (CanonicalLiteralExceptionalArithmetic.exceptional_fibers chart P R hclass X hX
        label F parent oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon
        hrightCommon rowProfileBound hrowProfileBound hrowProfile characters)
      (CanonicalLiteralExceptionalNumbers.first_saving chart P R hclass X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
        rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile
        hZ hstep hq herrorPrime)
      (CanonicalLiteralExceptionalNumbers.second_saving chart P R hclass X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
        rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile hZ row)
      (CanonicalLiteralExceptionalNumbers.v_sum chart P R hclass X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
        rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile)
      (fun h => CanonicalLiteralExceptionalFactory.centered_mask_ne_zero chart P R hclass
        hsector X hX label F parent oldMoving correction leftAtoms rightAtoms thetaPair
        RD.atoms RD.model hcorr remaining extra RD.recipe firstSupport hfirst hextra
        RD.support hone hroot hemb .right RD.ray RD.ideal RD.ideal_eq RD.firstSign
        RD.divisor RD.selection RD.nonempty hcR prodR ξ h.val)
      hmask
      (fun h => by simpa only [Real.norm_eq_abs] using
        CanonicalLiteralExceptionalFactory.centered_time_window chart P R hclass hsector
          X hX label F parent oldMoving correction leftAtoms rightAtoms thetaPair
          RD.atoms RD.model hcorr remaining extra RD.recipe firstSupport hfirst hextra
          RD.support hone hroot hemb .right RD.ray RD.ideal RD.ideal_eq RD.firstSign
          RD.divisor RD.selection RD.nonempty RD.firstSign_le hcR prodR ξ h.val)
      hmin
    exact hb
  · have hempty : S.exceptionalRows characters = ∅ :=
      Finset.eq_empty_of_forall_not_mem (fun h _ => hlive ⟨h⟩)
    simp only [SecondSideFrame.exceptionalMagnitude, jointColumnPairMagnitude,
      hempty, Finset.sum_empty, mul_zero]
    positivity

end Centered

end Terminal
end Pair
end ActualRows

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidRightSource

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidRightSource.rightConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidRightSource.centered_right_minimum
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidRightSource.centered_right_mask
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidRightSource.centered_right_magnitude_bound
