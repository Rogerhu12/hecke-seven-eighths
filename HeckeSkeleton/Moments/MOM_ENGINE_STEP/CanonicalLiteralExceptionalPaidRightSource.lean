import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPaidSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalRightTerminal

set_option linter.unusedSectionVars false
set_option quotPrecheck false

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
  CanonicalExceptionalTerminal.exists_original_magnitude_terminal_with_right_cutoff.{0, 0, 0, 0, 0}
    (A := A) (σ := σ) (η := η) (hS := hS) (V := WithLp 2 (ℝ × ℝ))
    (characterCatalogue ψ theta) primitive.density primitive.remainder
    primitive.continuous window primitive.volume primitive.compact primitive.positive
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
      primitive ε maskExponent hε hmask := by
  sorry

theorem rightConstant_pos :
    0 < rightConstant (A := A) (σ := σ) (η := η) (hS := hS)
      primitive ε maskExponent hε hmask := by
  sorry

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

section Pair

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

local notation "UL" => LD.paidScales S C .left (G).skeleton.A annulus amplitude cap hannulus hamplitude
local notation "UR" => RD.paidScales S C .right (G).skeleton.A annulus amplitude cap hannulus hamplitude

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
theorem centered_right_minimum (ξ : Joint) (h : (S).exceptionalRows characters) :
    Z ^ ((a.m + a.q) / 4 - (G).centeredExtractionLength - rR) ≤ (TR ξ h).source.lower := by
  sorry

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
  (remaining * extra)) ≤
    Z ^ (a.q + (G).skeleton.R + (G).skeleton.E + (G).skeleton.wo + widthMax))

include hstep hwidth hthreshold hradius hcutoff hproduct hold in
/-- A fixed parent box bounds the actual complete mask. Its initial
bad-prime ideal costs one fixed threshold and one exponent, while the
original physical cutoff cost remains explicit. The full first deletion
is charged to the additional fixed width, including its passive primes. -/
theorem centered_right_mask (ξ : Joint) (h : (S).exceptionalRows characters) :
    (Ideal.absNorm (TR ξ h).source.mask : ℝ) ≤
      Z ^ CanonicalLiteralExceptionalPhysicalBox.maskExponent
        widthMax columnLoss cutoffExponent := by
  sorry

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
  (remaining * extra)) ≤
    Z ^ (a.q + (G).skeleton.R + (G).skeleton.E + (G).skeleton.wo + widthMax))

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
    Z ^ (-childExponent) * (LF).exceptionalMagnitude RF EL ER characters ξ ≤
      rowFactor * ((Γ.index : ℝ) * constant * ((UL).constant * (UR).constant)) * amplitude ^ 4 *
        (1 + fourierHeight ξ) ^ order *
        Z ^ (max ((n).Aexp - (a.m + a.q)) 0 + 3 * (n).stepσ + 5 * (n).δ / 6 + ε +
          (n).slotError - idealLogLength Z LD.divisor + cutoffLoss / 6) := by
  sorry

end Centered

end Terminal
end Pair
end ActualRows

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidRightSource

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidRightSource.rightConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidRightSource.centered_right_minimum
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidRightSource.centered_right_mask
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidRightSource.centered_right_magnitude_bound
