import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalOriginalSideFactory
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalUnifiedChoice
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalRelativeSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalRightRelativeSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPaidAtomBudget

/-!
# One actual pair at its original exceptional source budget

The two actual side constructors return the original tables, the same
allocation divisor, and the uniform bounds for their factor-free models.
This file consumes those return values. It obtains the original prime
windows from the raw profile window, transports them through both actual
extractions, and pays each removed slot from the original annulus.

The left cancellation, right cancellation and ordinary absolute branches
use one fixed union of seminorm orders, one height degree and one constant.
Their source and relative row estimates are proved by their actual terminal
constructors. No completed magnitude, row mass or terminal estimate is an
input. The unchanged common envelope is kept explicit at this boundary.
The fixed volume mask box also pays the full first deletion, including
passive primes whose original phase is a sixth power.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalSourceBudget

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support CommonSupportMass
open CanonicalLiteralExceptionalPaidSource CanonicalLiteralExceptionalCharts

variable {K : Type} [Field K] [NumberField K]

/-- Both actual atomic constants and the four plain volume amplitudes. -/
def profileDegree (cap : ℕ) : ℕ :=
  CanonicalLiteralExceptionalAtomBudget.pairDegree cap + 4

theorem profileDegree_eq (cap : ℕ) : profileDegree cap = 10 * cap + 8 := by
  unfold profileDegree CanonicalLiteralExceptionalAtomBudget.pairDegree
  omega

private theorem scalar_coefficient_le
    (index pair growth profile amplitude bound constant height : ℝ) (degree : ℕ)
    (hi : 0 ≤ index) (hp : 0 ≤ profile) (ha : 0 ≤ amplitude)
    (hb : 0 ≤ bound) (hg : 0 ≤ growth)
    (hpair : pair ≤ bound * (profile * amplitude) ^ degree)
    (hgrowth : growth ≤ constant * height) :
    index * pair * (profile * amplitude) ^ 4 * growth ≤
      index * (bound * profile ^ (degree + 4) * constant) *
        amplitude ^ (degree + 4) * height := by
  have h := mul_le_mul hpair hgrowth hg
    (mul_nonneg hb (pow_nonneg (mul_nonneg hp ha) _))
  have h' := mul_le_mul_of_nonneg_left h
    (mul_nonneg hi (pow_nonneg (mul_nonneg hp ha) 4))
  calc
    _ = (index * (profile * amplitude) ^ 4) * (pair * growth) := by ring
    _ ≤ (index * (profile * amplitude) ^ 4) *
        ((bound * (profile * amplitude) ^ degree) * (constant * height)) := h'
    _ = index * (bound * constant) *
        ((profile * amplitude) ^ degree * (profile * amplitude) ^ 4) * height := by ring
    _ = _ := by rw [← pow_add, mul_pow]; ring

private theorem coefficient_mono
    (value envelope oldCoefficient newCoefficient power radical divisor : ℝ)
    (henvelope : 0 ≤ envelope) (hpower : 0 ≤ power)
    (hradical : 0 ≤ radical) (hdivisor : 0 ≤ divisor)
    (hvalue : value ≤ envelope * oldCoefficient * power / radical * divisor)
    (hcoefficient : oldCoefficient ≤ newCoefficient) :
    value ≤ envelope * newCoefficient * power / radical * divisor :=
  hvalue.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoefficient henvelope) hpower) hradical) hdivisor)

section FixedCoefficient

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ψ : HeckeCharacter K} {theta : Finset (HeckeCharacter K)} {window : Set ℝ}
variable (primitive : VolumePrimitive ψ theta window)
variable (ε widthMax columnLoss cutoffExponent : ℝ) (hε : 0 < ε)
variable (hwidthMax : 0 ≤ widthMax) (hcolumnLoss : 0 ≤ columnLoss)
variable (hcutoffExponent : 0 ≤ cutoffExponent) (δ₁ δ₂ annulus : ℝ) (cap : ℕ)

/-- Fixed before the moving profile, any source or Fourier mode. -/
def coefficient : ℝ :=
  let M := CanonicalLiteralExceptionalPhysicalBox.maskExponent widthMax columnLoss cutoffExponent
  let hM := CanonicalLiteralExceptionalPhysicalBox.maskExponent_nonneg
    hwidthMax hcolumnLoss hcutoffExponent
  let orders := CanonicalLiteralExceptionalUnifiedChoice.orders
    (A := A) (σ := σ) (η := η) (hS := hS) primitive ε M hε hM
  let profile := CanonicalLiteralExceptionalProfileWindow.coefficient
    window primitive.compact primitive.positive δ₁ δ₂ orders
  CanonicalLiteralExceptionalPaidAtomBudget.pairConstant (K := K) cap annulus *
    profile ^ profileDegree cap * CanonicalLiteralExceptionalUnifiedChoice.constant
      (A := A) (σ := σ) (η := η) (hS := hS) primitive ε M hε hM

theorem coefficient_pos (hannulus : 1 ≤ annulus) :
    0 < coefficient (A := A) (σ := σ) (η := η) (hS := hS)
      primitive ε widthMax columnLoss cutoffExponent hε hwidthMax hcolumnLoss
        hcutoffExponent δ₁ δ₂ annulus cap := by
  unfold coefficient
  exact mul_pos
    (mul_pos (CanonicalLiteralExceptionalPaidAtomBudget.pairConstant_pos cap annulus hannulus)
      (pow_pos (zero_lt_one.trans_le
        (CanonicalLiteralExceptionalProfileWindow.coefficient_one window primitive.compact
          primitive.positive δ₁ δ₂ _)) _))
    (CanonicalLiteralExceptionalUnifiedChoice.constant_pos
      (A := A) (σ := σ) (η := η) (hS := hS) primitive ε _ hε _)

end FixedCoefficient

section ResultProvenance

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {Index : Type*} {data : Index → MomentData K ω ψ}
variable {Q : CompleteMovingRowRecipe A P R data} {x : Index}
variable {Z amplitude δ₁ δ₂ : ℝ} {orders : Finset (ℕ × ℕ)} {window : Set ℝ}
variable {hcompact : IsCompact window} {hpositive : window ⊆ Set.Ioi 0}
variable {firstSupport secondSupport : Finset (Ideal (𝓞 K))}
variable {hfirstSupport : ∀ p ∈ firstSupport, Prime p}
variable {F : CanonicalLiteralPhaseCalibration.FixedPhases A}
variable {n k : ℕ} {seed : CanonicalLiteralRectangles.Atoms (K := K) n}
variable {firstIdeal secondIdeal divisor : Ideal (𝓞 K)} {scalar : ℂ}
variable {atoms : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {ray : (PUnit.{1} × PUnit.{1}) →* Circle}
variable {ideal : AllocationColumn K k → A.Exterior} {sign : ℝ}
variable {selection : primeSupport divisor → Finset (Fin (k + 2))}
variable (result : CanonicalLiteralExceptionalOriginalSideFactory.Result (σ := σ)
  Q x Z orders amplitude hcompact hpositive hfirstSupport F δ₁ δ₂
    (secondSupport := secondSupport) seed firstIdeal secondIdeal scalar atoms ray ideal sign
      divisor selection)

/-- Transport a property of the original table using its stored exact
heterogeneous identity; no table is reconstructed or selected again. -/
theorem result_original_property
    (property : ∀ n, CanonicalLiteralRectangles.Atoms (K := K) n → Prop)
    (h : property n seed) : property result.val.history.originalCount result.val.history.original := by
  have he : (⟨result.val.history.originalCount, result.val.history.original⟩ :
      Σ n : ℕ, CanonicalLiteralRectangles.Atoms (K := K) n) = ⟨n, seed⟩ :=
    Sigma.ext result.property.2.2.2.2.2.2.2.1 result.property.2.2.2.2.2.2.2.2.1
  exact (congrArg (fun q : Σ n : ℕ, CanonicalLiteralRectangles.Atoms (K := K) n =>
    property q.1 q.2) he).mpr h

end ResultProvenance

section ActualPair

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
variable {ω ψ : HeckeCharacter K} {Index : Type*} {data : Index → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (x : Index)
variable (recipe : NormProfileRecipe (fun _ : PUnit => data x))
variable {window : Set ℝ}
variable (primitive : VolumePrimitive ψ (data x).theta window)
variable (ε widthMax columnLoss cutoffExponent : ℝ) (hε : 0 < ε)
variable (hwidthMax : 0 ≤ widthMax) (hcolumnLoss : 0 ≤ columnLoss)
variable (hcutoffExponent : 0 ≤ cutoffExponent)
local notation "maskExp" =>
  CanonicalLiteralExceptionalPhysicalBox.maskExponent widthMax columnLoss cutoffExponent
local notation "hmaskExp" => CanonicalLiteralExceptionalPhysicalBox.maskExponent_nonneg
  hwidthMax hcolumnLoss hcutoffExponent
local notation "orders" => CanonicalLiteralExceptionalUnifiedChoice.orders
  (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
local notation "heightOrder" => CanonicalLiteralExceptionalUnifiedChoice.heightOrder
  (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
local notation "allConstant" => CanonicalLiteralExceptionalUnifiedChoice.constant
  (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp

variable (δ₁ δ₂ rawAmplitude annulus : ℝ) (hrawAmplitude : 1 ≤ rawAmplitude)
variable (hannulus : 1 ≤ annulus)
local notation "profileCoefficient" => CanonicalLiteralExceptionalProfileWindow.coefficient
  window primitive.compact primitive.positive δ₁ δ₂ orders
local notation "amplitude" => profileCoefficient * rawAmplitude
local notation "hprofileCoefficient" => CanonicalLiteralExceptionalProfileWindow.coefficient_one
  window primitive.compact primitive.positive δ₁ δ₂ orders
local notation "hamplitudeOne" =>
  one_le_mul_of_one_le_of_one_le hprofileCoefficient hrawAmplitude
local notation "hamplitude" => zero_le_one.trans hamplitudeOne

variable (a : RealParameters) (Z t Y₁ Y₂ step : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}
variable (original : RawProfileWindow rowDomain heightDomain window
  (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders))
    (data x) rawAmplitude)
variable (ht : t ∈ heightDomain)
variable (hwindowUpper : ∀ y ∈ window, y ≤ annulus)
variable (hwindowLower : window ⊆ Set.Ici annulus⁻¹)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data x) a Z Y₁ Y₂ floor padding)
variable (first : OriginalNominalGeometry (K := K) a Z step)
variable (cap : ℕ) (hcap : (data x).geometry.slotCount ≤ cap)

local notation "seed" => Q.literalOriginalAtoms x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
local notation "Orbit" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "Joint" => WithLp 2 (ℝ × ℝ)
local notation "rawRows" => chart.actualRows ∅ X hX label
local notation "pattern" => chart.originalNonunitPattern ∅ X hX label
local notation "sector" => chart.originalSector P ∅ X hX label
local notation "characters" => (rawRows).literalFiniteCharacters C P R F Q.moving
  Q.correction pattern sector (data x).theta
variable {kCommonL kCommonR : ℕ}
variable (leftAtoms : FrozenSourceAtoms A σ Orbit (rawRows).rows kCommonL)
variable (rightAtoms : FrozenSourceAtoms A σ Orbit (rawRows).rows kCommonR)
variable (thetaPair : (data x).theta × (data x).theta)
local notation "S" => CanonicalLiteralExceptionalFactory.rows chart P R X hX label F
  (data x) Q.moving Q.correction leftAtoms rightAtoms thetaPair

variable (firstSupport : Finset (Ideal (𝓞 K))) (hfirstSupport : ∀ p ∈ firstSupport, Prime p)
local notation "extra" => literalDeletionIdeal firstSupport hfirstSupport
local notation "secondSupport" => primeSupport (primePowerProduct b.primes b.leftMultiplicity).val
variable {k l : ℕ}
variable (finalLeft : CanonicalLiteralRectangles.Atoms (K := K) k)
variable (finalRight : CanonicalLiteralRectangles.Atoms (K := K) l)
variable (rayLeft rayRight : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (idealLeft : AllocationColumn K k → A.Exterior)
variable (idealRight : AllocationColumn K l → A.Exterior)
variable (signLeft signRight : ℝ) (divisor : Ideal (𝓞 K))
variable (selectionLeft : primeSupport divisor → Finset (Fin (k + 2)))
variable (selectionRight : primeSupport divisor → Finset (Fin (l + 2)))
variable (commonScalarLeft commonScalarRight : ℂ)
variable (leftResult : CanonicalLiteralExceptionalOriginalSideFactory.Result (σ := σ)
  Q x Z orders rawAmplitude primitive.compact primitive.positive hfirstSupport F δ₁ δ₂
    («secondSupport» := secondSupport) seed
    (first.ideals.first * first.tag.extractionIdeal).val
    (primePowerProduct b.primes b.leftMultiplicity).val commonScalarLeft finalLeft
    rayLeft idealLeft signLeft divisor selectionLeft)
variable (rightResult : CanonicalLiteralExceptionalOriginalSideFactory.Result (σ := σ)
  Q x Z orders rawAmplitude primitive.compact primitive.positive hfirstSupport F δ₁ δ₂
    («secondSupport» := secondSupport) seed
    (first.ideals.first * first.tag.extractionIdeal).val
    (primePowerProduct b.primes b.rightMultiplicity).val commonScalarRight finalRight
    rayRight idealRight signRight divisor selectionRight)
local notation "LD" => leftResult.val
local notation "RD" => rightResult.val
local notation "LF" => (LD).frame S C .left
local notation "RF" => (RD).frame S C .right
local notation "EL" => (LD).comparison S C .left
local notation "ER" => (RD).comparison S C .right

variable (hleftCommon : leftAtoms.ideal = (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hrightCommon : rightAtoms.ideal = (primePowerProduct b.primes b.rightMultiplicity).val)
variable (rowProfileBound : ℝ) (hrowProfileBound : 0 ≤ rowProfileBound)
variable (hrowProfile : ∀ q ∈ (rawRows).rows, ‖chart.weight q‖ ≤ rowProfileBound)
local notation "mass" => CanonicalLiteralExceptionalArithmetic.actualMass chart P R hclass
  X hX label F (data x) Q.moving Q.correction leftAtoms rightAtoms thetaPair
  hleftCommon hrightCommon rowProfileBound hrowProfileBound hrowProfile
local notation "G" => CanonicalLiteralExceptionalNumbers.geometry chart X hX label first
variable (slotLoss firstProfile normalization firstTotal loss : ℝ)
variable (hone : (1 : HeckeCharacter K) ∈ (data x).theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (hplaces : CanonicalLiteralExceptionalArithmetic.thetaBadPrimes (data x).theta ⊆ A.Sf)
variable (hscalar : commonScalarLeft ≠ 0)
variable (hstep : 0 ≤ step) (hq : 0 ≤ a.q)
variable (herrorPrime : ∀ e p, first.tag = .error e p →
  (Ideal.absNorm p.asIdeal : ℝ) ≤ Z ^ (step / 3))
variable (hradius : radius = CanonicalRowBall.gaussRadius first.retainedScale Z first.enlargement
  first.retainedScale_pos (zero_lt_one.trans hZ))
variable (hcutoff : X ≤ Z ^ cutoffExponent)
variable (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
  (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤
    Z ^ (2 * (first.skeleton.A - first.skeleton.c - first.skeleton.w + columnLoss)))
variable (hslotLoss : annulus ≤ Z ^ (2 * slotLoss))
variable (hslotLossNonneg : 0 ≤ slotLoss)
variable (hslots : (cap : ℝ) * slotLoss ≤ loss / 16)
variable (hnormalization : normalization = firstLeftAllowance Z firstTotal
  first.ideals.first.val first.ideals.opposite.val)
variable (htotal : firstTotal = first.skeleton.A +
  (first.skeleton.q + first.skeleton.R + first.skeleton.E))
variable (hloss : 0 ≤ loss) (hsupport : first.supportError ≤ loss / 16)
variable (hvolume : ε ≤ loss / 16)
local notation "cutoffLoss" => CanonicalLiteralExceptionalGeometry.paidCutoff columnLoss cutoffExponent 0
variable (hcutoffPaid : cutoffLoss / 6 ≤ loss / 16)
local notation "UL" => (LD).paidScales S C .left (G).skeleton.A annulus amplitude cap hannulus hamplitude
local notation "UR" => (RD).paidScales S C .right (G).skeleton.A annulus amplitude cap hannulus hamplitude
local notation "envelope" => annulus ^ cap * ((mass).commonEnvelope * orbitalFieldFactor K)
local notation "radical" => (Ideal.absNorm (commonRadical (mass).leftIdeal (mass).rightIdeal) : ℝ)

local notation "fixedCoefficient" => coefficient (A := A) (σ := σ) (η := η) (hS := hS)
  primitive ε widthMax columnLoss cutoffExponent hε hwidthMax hcolumnLoss hcutoffExponent
    δ₁ δ₂ annulus cap
local notation "uniformCoefficient" ξ =>
  (Γ.index : ℝ) * fixedCoefficient * rawAmplitude ^ profileDegree cap *
    (1 + fourierHeight ξ) ^ heightOrder

include hslotLossNonneg hslots in
private theorem removed_slot_sum_le {n : ℕ} (keep : Finset (Fin n))
    (hn : n ≤ cap) : ∑ i ∈ Finset.univ \ keep, slotLoss ≤ loss / 16 := by
  have hc : (Finset.univ \ keep).card ≤ cap :=
    (by simpa only [Fintype.card_fin] using Finset.card_le_univ (Finset.univ \ keep)).trans hn
  calc
    _ = ((Finset.univ \ keep).card : ℝ) * slotLoss := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (cap : ℝ) * slotLoss :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) hslotLossNonneg
    _ ≤ loss / 16 := hslots

section Centered

variable (hwidth : a.m + a.q ≤ widthMax)
variable (hthreshold : max 2 (Ideal.absNorm A.cS : ℝ) ≤ Z)
variable (hold : A.exteriorNorm ((F.moving P R Q.moving).effectiveFullSupport
  (Q.remaining * extra)) ≤
    Z ^ (a.q + (G).skeleton.R + (G).skeleton.E + (G).skeleton.wo + widthMax))

include hclass hsector hrawAmplitude hannulus firstProfile original ht hwindowUpper hwindowLower domain hcap
  hleftCommon hrightCommon hrowProfileBound hrowProfile hone hroot hemb hplaces hscalar
  hstep hq herrorPrime hradius hcutoff hproduct hslotLoss hslotLossNonneg hslots
  hnormalization htotal hloss hsupport hcutoffPaid hvolume hwidth hthreshold hold in
/-- The same actual pair uses whichever of its two original common
ideals is smaller. Both cancellation directions share the fixed source
coefficient, the original divisor, and the original profile power. -/
theorem centered_small_loss_bound (hc : centered = true) (hpadding : 0 ≤ padding)
    (ξ : Joint) :
    (LF).exceptionalMagnitude RF EL ER characters ξ / normalization ≤
      envelope * uniformCoefficient ξ *
        Z ^ ((padding + 3 * step + loss / 2) + (G).tag.exceptionalMovingLength Z step) /
          radical * Z ^ (-idealLogLength Z divisor) := by
  have hdomain : PairedEngineDomain true (data x) a Z Y₁ Y₂ floor padding := by
    simpa only [hc] using domain
  have hcorrection : Q.correction ∈ (data x).theta := by
    rcases Q.correction_mem x with h | h
    · simpa only [h] using hone
    · exact h
  have hseedPrime : (seed).PrimeNormWindow annulus :=
    Q.literalOriginalAtoms_primeNormWindow x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      original annulus ht hwindowUpper
  have hseedLower : ∀ i, ∀ p ∈ (seed).slots i,
      Z ^ (seed).length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ) :=
    Q.literalOriginalAtoms_primeLowerWindow x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      original annulus (zero_lt_one.trans_le hannulus) ht hwindowLower
  have hseedProduct : (seed).scaleProduct false = Z ^ (G).skeleton.A := by
    change (seed).scaleProduct false = Z ^ (a.n₁ + a.n₂ + a.z)
    simp only [CanonicalLiteralRectangles.Atoms.scaleProduct,
      CompleteMovingRowRecipe.literalOriginalAtoms, Bool.false_eq_true, if_false,
      domain.total_length, SlotGeometry.totalLength,
      Real.rpow_add (zero_lt_one.trans hZ), Real.rpow_sum_of_pos (zero_lt_one.trans hZ)]
  have hcapL : (LD).history.originalCount ≤ cap := by
    rw [leftResult.property.2.2.2.2.2.2.2.1]
    exact hcap
  have hprimeOriginalL : (LD).history.original.PrimeNormWindow annulus :=
    result_original_property (result := leftResult) (fun _ d => d.PrimeNormWindow annulus) hseedPrime
  have hproductOriginalL : (LD).history.original.scaleProduct false = Z ^ (G).skeleton.A :=
    result_original_property (result := leftResult)
      (fun _ d => d.scaleProduct false = Z ^ (G).skeleton.A) hseedProduct
  have hprimeLowerL : ∀ i, ∀ p ∈ (LD).history.original.slots i,
      Z ^ (LD).history.original.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ) :=
    result_original_property (result := leftResult)
      (fun _ d => ∀ i, ∀ p ∈ d.slots i,
        Z ^ d.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ)) hseedLower
  have hprimeL : (LD).atoms.PrimeNormWindow annulus :=
    leftResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 annulus hseedPrime
  have hslotL : ∀ i, SchwartzMap.seminorm ℂ 0 0 ((LD).model.slot i) ≤ amplitude := by
    intro i
    exact CanonicalLiteralExceptionalUnifiedChoice.zero_order_bound
      (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
      ((LD).model.slot i) amplitude (leftResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i)
  have hprofileL₁ := CanonicalLiteralExceptionalUnifiedChoice.profile_bounds
    (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
    ((LD).model.left false) amplitude (leftResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 false)
  have hprofileL₂ := CanonicalLiteralExceptionalUnifiedChoice.profile_bounds
    (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
    ((LD).model.right false) amplitude (leftResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 false)
  have hcL : SamePlainProfiles (LD).model := leftResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc
  have hseedLeftL : ∀ r, (LD).history.original.scale₁ r =
      if r then Y₁ else Z ^ a.n₁ :=
    result_original_property (result := leftResult)
      (fun _ d => ∀ r, d.scale₁ r = if r then Y₁ else Z ^ a.n₁) (fun _ => rfl)
  have hseedRightL : ∀ r, (LD).history.original.scale₂ r =
      if r then Y₂ else Z ^ a.n₂ :=
    result_original_property (result := leftResult)
      (fun _ d => ∀ r, d.scale₂ r = if r then Y₂ else Z ^ a.n₂) (fun _ => rfl)
  have hslotsL : ∑ i ∈ Finset.univ \ (LF).allocation.keep, slotLoss ≤ loss / 16 :=
    removed_slot_sum_le (cap := cap) (slotLoss := slotLoss) (loss := loss)
      (hslotLossNonneg := hslotLossNonneg) (hslots := hslots)
      (LF).allocation.keep ((LD).count_le cap hcapL)
  have hcapR : (RD).history.originalCount ≤ cap := by
    rw [rightResult.property.2.2.2.2.2.2.2.1]
    exact hcap
  have hprimeOriginalR : (RD).history.original.PrimeNormWindow annulus :=
    result_original_property (result := rightResult) (fun _ d => d.PrimeNormWindow annulus) hseedPrime
  have hproductOriginalR : (RD).history.original.scaleProduct false = Z ^ (G).skeleton.A :=
    result_original_property (result := rightResult)
      (fun _ d => d.scaleProduct false = Z ^ (G).skeleton.A) hseedProduct
  have hprimeLowerR : ∀ i, ∀ p ∈ (RD).history.original.slots i,
      Z ^ (RD).history.original.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ) :=
    result_original_property (result := rightResult)
      (fun _ d => ∀ i, ∀ p ∈ d.slots i,
        Z ^ d.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ)) hseedLower
  have hprimeR : (RD).atoms.PrimeNormWindow annulus :=
    rightResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 annulus hseedPrime
  have hslotR : ∀ i, SchwartzMap.seminorm ℂ 0 0 ((RD).model.slot i) ≤ amplitude := by
    intro i
    exact CanonicalLiteralExceptionalUnifiedChoice.zero_order_bound
      (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
      ((RD).model.slot i) amplitude (rightResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i)
  have hprofileR₁ := CanonicalLiteralExceptionalUnifiedChoice.profile_bounds
    (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
    ((RD).model.left false) amplitude (rightResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 false)
  have hprofileR₂ := CanonicalLiteralExceptionalUnifiedChoice.profile_bounds
    (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
    ((RD).model.right false) amplitude (rightResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 false)
  have hcR : SamePlainProfiles (RD).model := rightResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc
  have hseedLeftR : ∀ r, (RD).history.original.scale₁ r =
      if r then Y₁ else Z ^ a.n₁ :=
    result_original_property (result := rightResult)
      (fun _ d => ∀ r, d.scale₁ r = if r then Y₁ else Z ^ a.n₁) (fun _ => rfl)
  have hseedRightR : ∀ r, (RD).history.original.scale₂ r =
      if r then Y₂ else Z ^ a.n₂ :=
    result_original_property (result := rightResult)
      (fun _ d => ∀ r, d.scale₂ r = if r then Y₂ else Z ^ a.n₂) (fun _ => rfl)
  have hslotsR : ∑ i ∈ Finset.univ \ (RF).allocation.keep, slotLoss ≤ loss / 16 :=
    removed_slot_sum_le (cap := cap) (slotLoss := slotLoss) (loss := loss)
      (hslotLossNonneg := hslotLossNonneg) (hslots := hslots)
      (RF).allocation.keep ((RD).count_le cap hcapR)
  have hscalarActual : (historyActualSecondInput P R extra (LD).history).commonScalar
      (LD).history.second ≠ 0 := by
    rw [leftResult.property.2.2.2.2.2.2.2.2.2.2.2.1]
    exact hscalar
  have hpair : (UL).constant * (UR).constant ≤
      CanonicalLiteralExceptionalPaidAtomBudget.pairConstant (K := K) cap annulus *
        amplitude ^ CanonicalLiteralExceptionalAtomBudget.pairDegree cap :=
    CanonicalLiteralExceptionalPaidAtomBudget.original_pair_constant_le cap annulus amplitude
      hannulus hamplitudeOne (LF).allocation (RF).allocation
      Z ((LD).targetTotal (G).skeleton.A) Z ((RD).targetTotal (G).skeleton.A)
      (LD).atoms.length (RD).atoms.length (fun i => ((LD).atoms.length_pos i).le)
      (fun i => ((RD).atoms.length_pos i).le) ((LD).count_le cap hcapL) ((RD).count_le cap hcapR)
  have hgrowth := CanonicalLiteralExceptionalUnifiedChoice.growth_le
    (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
    (fourierHeight ξ) (fourierHeight_nonneg ξ)
  have hcoefficient (c H : ℝ) (hcH : 0 ≤ c * H)
      (hbound : c * H ≤ allConstant * (1 + fourierHeight ξ) ^ heightOrder) :
      ((Γ.index : ℝ) * c * ((UL).constant * (UR).constant)) * amplitude ^ 4 * H ≤
        uniformCoefficient ξ := by
    have h := scalar_coefficient_le (Γ.index : ℝ) ((UL).constant * (UR).constant) (c * H)
      profileCoefficient rawAmplitude
      (CanonicalLiteralExceptionalPaidAtomBudget.pairConstant (K := K) cap annulus)
      allConstant ((1 + fourierHeight ξ) ^ heightOrder)
      (CanonicalLiteralExceptionalAtomBudget.pairDegree cap)
      (Nat.cast_nonneg _) (zero_le_one.trans hprofileCoefficient)
      (zero_le_one.trans hrawAmplitude)
      (CanonicalLiteralExceptionalPaidAtomBudget.pairConstant_pos cap annulus hannulus).le
      hcH hpair hbound
    calc
      _ = (Γ.index : ℝ) * ((UL).constant * (UR).constant) * amplitude ^ 4 * (c * H) := by ring
      _ ≤ _ := h
  have henv : 0 ≤ envelope := mul_nonneg
    (pow_nonneg (zero_le_one.trans hannulus) _)
    (mul_nonneg (mass).commonEnvelope_nonneg (orbitalFieldFactor_nonneg K))
  by_cases horder : idealLogLength Z (primePowerProduct b.primes b.leftMultiplicity).val ≤
      idealLogLength Z (primePowerProduct b.primes b.rightMultiplicity).val
  · have hb := CanonicalLiteralExceptionalRelativeSource.centered_small_loss_bound
      (chart := chart) (P := P) (R := R)
      (hclass := hclass) (hsector := hsector) (X := X)
      (hX := hX) (label := label) (F := F)
      (parent := data x) (oldMoving := Q.moving) (correction := Q.correction)
      (leftAtoms := leftAtoms) (rightAtoms := rightAtoms) (thetaPair := thetaPair)
      (hcorr := hcorrection) (remaining := Q.remaining) («extra» := extra)
      (firstSupport := firstSupport) (hfirst := hfirstSupport) (hextra := rfl)
      (hone := hone) (hroot := hroot) (hemb := hemb)
      (annulus := annulus) («amplitude» := amplitude) (hannulus := hannulus)
      («hamplitude» := hamplitude) (cap := cap) («LD» := LD)
      («RD» := RD) (hleftCommon := hleftCommon) (hrightCommon := hrightCommon)
      (rowProfileBound := rowProfileBound) (hrowProfileBound := hrowProfileBound) (hrowProfile := hrowProfile)
      (first := first) (slotLoss := slotLoss) (firstProfile := firstProfile)
      (hfirstL := leftResult.property.2.2.2.2.2.2.2.2.2.1) (hfirstR := rightResult.property.2.2.2.2.2.2.2.2.2.1) (hsecondL := leftResult.property.2.2.2.2.2.2.2.2.2.2.1)
      (hsecondR := rightResult.property.2.2.2.2.2.2.2.2.2.2.1) (hplaces := hplaces) (hscalar := hscalarActual)
      (primitive := primitive) (hZ := hZ) (hstep := hstep)
      (hq := hq) (herrorPrime := herrorPrime) (columnLoss := columnLoss)
      (cutoffExponent := cutoffExponent) (hradius := hradius) (hcutoff := hcutoff)
      (hproduct := hproduct) (hcapL := hcapL) (hcapR := hcapR)
      (hprimeOriginalL := hprimeOriginalL) (hprimeOriginalR := hprimeOriginalR) (hproductOriginalL := hproductOriginalL)
      (hproductOriginalR := hproductOriginalR) (hprimeL := hprimeL) (hprimeR := hprimeR)
      (hslotL := hslotL) (hslotR := hslotR) («hamplitudeOne» := hamplitudeOne)
      (hslotLoss := hslotLoss) (normalization := normalization) (firstTotal := firstTotal)
      (hprimeLowerL := hprimeLowerL) (hprimeLowerR := hprimeLowerR) (hnormalization := hnormalization)
      (domain := hdomain) (ε := ε) (widthMax := widthMax)
      (hε := hε) (hwidthMax := hwidthMax) (hcolumnLoss := hcolumnLoss)
      (hcutoffExponent := hcutoffExponent) (hseedLeftL := hseedLeftL) (hseedRightL := hseedRightL)
      (hseedLeftR := hseedLeftR) (hseedRightR := hseedRightR) (hcL := hcL)
      (hcR := hcR) (horder := horder) (hwidth := hwidth)
      (hthreshold := hthreshold) (hold := hold) (hprofileL₁ := hprofileL₁.1)
      (hprofileL₂ := hprofileL₂.1) (hprofileR₁ := hprofileR₁.1) (hprofileR₂ := hprofileR₂.1)
      (htotal := htotal) (loss := loss) (hloss := hloss)
      (hsupport := hsupport) (hcutoffPaid := hcutoffPaid) (hpadding := hpadding)
      (hvolume := hvolume) (hslots := hslotsR)
      ξ
    have hpositive := CanonicalLiteralExceptionalPaidSource.centeredConstant_pos
      (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
    have hc := hcoefficient
      (CanonicalLiteralExceptionalPaidSource.centeredConstant (A := A) (σ := σ) (η := η) (hS := hS)
        primitive ε maskExp hε hmaskExp)
      ((1 + fourierHeight ξ) ^ (CanonicalLiteralExceptionalPaidSource.centeredOrder
        (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp))
      (mul_nonneg hpositive.le (by positivity)) hgrowth.1
    apply coefficient_mono (henvelope := henv) (hpower := Real.rpow_nonneg (zero_le_one.trans hZ.le) _)
      (hradical := Nat.cast_nonneg _) (hdivisor := Real.rpow_nonneg (zero_le_one.trans hZ.le) _) (hcoefficient := hc)
    simpa only [rightResult.property.2.2.2.2.2.1] using hb
  · have horder := lt_of_not_ge horder
    have hb := CanonicalLiteralExceptionalRightRelativeSource.centered_right_small_loss_bound
      (chart := chart) (P := P) (R := R)
      (hclass := hclass) (hsector := hsector) (X := X)
      (hX := hX) (label := label) (F := F)
      (parent := data x) (oldMoving := Q.moving) (correction := Q.correction)
      (leftAtoms := leftAtoms) (rightAtoms := rightAtoms) (thetaPair := thetaPair)
      (hcorr := hcorrection) (remaining := Q.remaining) («extra» := extra)
      (firstSupport := firstSupport) (hfirst := hfirstSupport) (hextra := rfl)
      (hone := hone) (hroot := hroot) (hemb := hemb)
      (annulus := annulus) («amplitude» := amplitude) (hannulus := hannulus)
      («hamplitude» := hamplitude) (cap := cap) («LD» := LD)
      («RD» := RD) (hleftCommon := hleftCommon) (hrightCommon := hrightCommon)
      (rowProfileBound := rowProfileBound) (hrowProfileBound := hrowProfileBound) (hrowProfile := hrowProfile)
      (first := first) (slotLoss := slotLoss) (firstProfile := firstProfile)
      (hfirstL := leftResult.property.2.2.2.2.2.2.2.2.2.1) (hfirstR := rightResult.property.2.2.2.2.2.2.2.2.2.1) (hsecondL := leftResult.property.2.2.2.2.2.2.2.2.2.2.1)
      (hsecondR := rightResult.property.2.2.2.2.2.2.2.2.2.2.1) (hplaces := hplaces) (hscalar := hscalarActual)
      (primitive := primitive) (hZ := hZ) (hstep := hstep)
      (hq := hq) (herrorPrime := herrorPrime) (columnLoss := columnLoss)
      (cutoffExponent := cutoffExponent) (hradius := hradius) (hcutoff := hcutoff)
      (hproduct := hproduct) (hcapL := hcapL) (hcapR := hcapR)
      (hprimeOriginalL := hprimeOriginalL) (hprimeOriginalR := hprimeOriginalR) (hproductOriginalL := hproductOriginalL)
      (hproductOriginalR := hproductOriginalR) (hprimeL := hprimeL) (hprimeR := hprimeR)
      (hslotL := hslotL) (hslotR := hslotR) («hamplitudeOne» := hamplitudeOne)
      (hslotLoss := hslotLoss) (normalization := normalization) (firstTotal := firstTotal)
      (hprimeLowerL := hprimeLowerL) (hprimeLowerR := hprimeLowerR) (hnormalization := hnormalization)
      (domain := hdomain) (ε := ε) (widthMax := widthMax)
      (hε := hε) (hwidthMax := hwidthMax) (hcolumnLoss := hcolumnLoss)
      (hcutoffExponent := hcutoffExponent) (hseedLeftL := hseedLeftL) (hseedRightL := hseedRightL)
      (hseedLeftR := hseedLeftR) (hseedRightR := hseedRightR) (hcL := hcL)
      (hcR := hcR) (horder := horder) (hwidth := hwidth)
      (hthreshold := hthreshold) (hold := hold) (hprofileL₁ := hprofileL₁.2.1)
      (hprofileL₂ := hprofileL₂.2.1) (hprofileR₁ := hprofileR₁.2.1) (hprofileR₂ := hprofileR₂.2.1)
      (htotal := htotal) (loss := loss) (hloss := hloss)
      (hsupport := hsupport) (hcutoffPaid := hcutoffPaid) (hpadding := hpadding)
      (hvolume := hvolume) (hslots := hslotsL)
      ξ
    have hpositive := CanonicalLiteralExceptionalPaidRightSource.rightConstant_pos
      (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
    have hc := hcoefficient
      (CanonicalLiteralExceptionalPaidRightSource.rightConstant (A := A) (σ := σ) (η := η) (hS := hS)
        primitive ε maskExp hε hmaskExp)
      ((1 + fourierHeight ξ) ^ (CanonicalLiteralExceptionalPaidRightSource.rightOrder
        (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp))
      (mul_nonneg hpositive.le (by positivity)) hgrowth.2.1
    apply coefficient_mono (henvelope := henv) (hpower := Real.rpow_nonneg (zero_le_one.trans hZ.le) _)
      (hradical := Nat.cast_nonneg _) (hdivisor := Real.rpow_nonneg (zero_le_one.trans hZ.le) _) (hcoefficient := hc)
    simpa only [leftResult.property.2.2.2.2.2.1] using hb
end Centered

include hclass hsector hrawAmplitude hannulus firstProfile original ht hwindowUpper hwindowLower domain hcap
  hleftCommon hrightCommon hrowProfileBound hrowProfile hone hroot hemb hplaces hscalar
  hstep hq herrorPrime hradius hcutoff hproduct hslotLoss hslotLossNonneg hslots
  hnormalization htotal hloss hsupport hcutoffPaid in
/-- The ordinary branch uses the original absolute source bound. It
shares the same fixed coefficient and height degree as the two centered
branches, while retaining its ordinary exponent. -/
theorem ordinary_small_loss_bound (hc : centered = false) (ξ : Joint) :
    (LF).ordinaryExceptionalMagnitude RF characters ξ / normalization ≤
      envelope * uniformCoefficient ξ *
        Z ^ ((3 * step + loss / 2) + (G).tag.exceptionalMovingLength Z step) /
          radical * Z ^ (-idealLogLength Z divisor) := by
  have hdomain : PairedEngineDomain false (data x) a Z Y₁ Y₂ floor padding := by
    simpa only [hc] using domain
  have hcorrection : Q.correction ∈ (data x).theta := by
    rcases Q.correction_mem x with h | h
    · simpa only [h] using hone
    · exact h
  have hseedPrime : (seed).PrimeNormWindow annulus :=
    Q.literalOriginalAtoms_primeNormWindow x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      original annulus ht hwindowUpper
  have hseedLower : ∀ i, ∀ p ∈ (seed).slots i,
      Z ^ (seed).length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ) :=
    Q.literalOriginalAtoms_primeLowerWindow x recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      original annulus (zero_lt_one.trans_le hannulus) ht hwindowLower
  have hseedProduct : (seed).scaleProduct false = Z ^ (G).skeleton.A := by
    change (seed).scaleProduct false = Z ^ (a.n₁ + a.n₂ + a.z)
    simp only [CanonicalLiteralRectangles.Atoms.scaleProduct,
      CompleteMovingRowRecipe.literalOriginalAtoms, Bool.false_eq_true, if_false,
      domain.total_length, SlotGeometry.totalLength,
      Real.rpow_add (zero_lt_one.trans hZ), Real.rpow_sum_of_pos (zero_lt_one.trans hZ)]
  have hcapL : (LD).history.originalCount ≤ cap := by
    rw [leftResult.property.2.2.2.2.2.2.2.1]
    exact hcap
  have hprimeOriginalL : (LD).history.original.PrimeNormWindow annulus :=
    result_original_property (result := leftResult) (fun _ d => d.PrimeNormWindow annulus) hseedPrime
  have hproductOriginalL : (LD).history.original.scaleProduct false = Z ^ (G).skeleton.A :=
    result_original_property (result := leftResult)
      (fun _ d => d.scaleProduct false = Z ^ (G).skeleton.A) hseedProduct
  have hprimeLowerL : ∀ i, ∀ p ∈ (LD).history.original.slots i,
      Z ^ (LD).history.original.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ) :=
    result_original_property (result := leftResult)
      (fun _ d => ∀ i, ∀ p ∈ d.slots i,
        Z ^ d.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ)) hseedLower
  have hprimeL : (LD).atoms.PrimeNormWindow annulus :=
    leftResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 annulus hseedPrime
  have hslotL : ∀ i, SchwartzMap.seminorm ℂ 0 0 ((LD).model.slot i) ≤ amplitude := by
    intro i
    exact CanonicalLiteralExceptionalUnifiedChoice.zero_order_bound
      (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
      ((LD).model.slot i) amplitude (leftResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i)
  have hprofileL₁ := CanonicalLiteralExceptionalUnifiedChoice.profile_bounds
    (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
    ((LD).model.left false) amplitude (leftResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 false)
  have hprofileL₂ := CanonicalLiteralExceptionalUnifiedChoice.profile_bounds
    (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
    ((LD).model.right false) amplitude (leftResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 false)
  have hslotsL : ∑ i ∈ Finset.univ \ (LF).allocation.keep, slotLoss ≤ loss / 16 :=
    removed_slot_sum_le (cap := cap) (slotLoss := slotLoss) (loss := loss)
      (hslotLossNonneg := hslotLossNonneg) (hslots := hslots)
      (LF).allocation.keep ((LD).count_le cap hcapL)
  have hcapR : (RD).history.originalCount ≤ cap := by
    rw [rightResult.property.2.2.2.2.2.2.2.1]
    exact hcap
  have hprimeOriginalR : (RD).history.original.PrimeNormWindow annulus :=
    result_original_property (result := rightResult) (fun _ d => d.PrimeNormWindow annulus) hseedPrime
  have hproductOriginalR : (RD).history.original.scaleProduct false = Z ^ (G).skeleton.A :=
    result_original_property (result := rightResult)
      (fun _ d => d.scaleProduct false = Z ^ (G).skeleton.A) hseedProduct
  have hprimeLowerR : ∀ i, ∀ p ∈ (RD).history.original.slots i,
      Z ^ (RD).history.original.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ) :=
    result_original_property (result := rightResult)
      (fun _ d => ∀ i, ∀ p ∈ d.slots i,
        Z ^ d.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ)) hseedLower
  have hprimeR : (RD).atoms.PrimeNormWindow annulus :=
    rightResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 annulus hseedPrime
  have hslotR : ∀ i, SchwartzMap.seminorm ℂ 0 0 ((RD).model.slot i) ≤ amplitude := by
    intro i
    exact CanonicalLiteralExceptionalUnifiedChoice.zero_order_bound
      (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
      ((RD).model.slot i) amplitude (rightResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i)
  have hprofileR₁ := CanonicalLiteralExceptionalUnifiedChoice.profile_bounds
    (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
    ((RD).model.left false) amplitude (rightResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 false)
  have hprofileR₂ := CanonicalLiteralExceptionalUnifiedChoice.profile_bounds
    (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
    ((RD).model.right false) amplitude (rightResult.property.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 false)
  have hslotsR : ∑ i ∈ Finset.univ \ (RF).allocation.keep, slotLoss ≤ loss / 16 :=
    removed_slot_sum_le (cap := cap) (slotLoss := slotLoss) (loss := loss)
      (hslotLossNonneg := hslotLossNonneg) (hslots := hslots)
      (RF).allocation.keep ((RD).count_le cap hcapR)
  have hscalarActual : (historyActualSecondInput P R extra (LD).history).commonScalar
      (LD).history.second ≠ 0 := by
    rw [leftResult.property.2.2.2.2.2.2.2.2.2.2.2.1]
    exact hscalar
  have hpair : (UL).constant * (UR).constant ≤
      CanonicalLiteralExceptionalPaidAtomBudget.pairConstant (K := K) cap annulus *
        amplitude ^ CanonicalLiteralExceptionalAtomBudget.pairDegree cap :=
    CanonicalLiteralExceptionalPaidAtomBudget.original_pair_constant_le cap annulus amplitude
      hannulus hamplitudeOne (LF).allocation (RF).allocation
      Z ((LD).targetTotal (G).skeleton.A) Z ((RD).targetTotal (G).skeleton.A)
      (LD).atoms.length (RD).atoms.length (fun i => ((LD).atoms.length_pos i).le)
      (fun i => ((RD).atoms.length_pos i).le) ((LD).count_le cap hcapL) ((RD).count_le cap hcapR)
  have hgrowth := CanonicalLiteralExceptionalUnifiedChoice.growth_le
    (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExp hε hmaskExp
    (fourierHeight ξ) (fourierHeight_nonneg ξ)
  have hcoefficient (c H : ℝ) (hcH : 0 ≤ c * H)
      (hbound : c * H ≤ allConstant * (1 + fourierHeight ξ) ^ heightOrder) :
      ((Γ.index : ℝ) * c * ((UL).constant * (UR).constant)) * amplitude ^ 4 * H ≤
        uniformCoefficient ξ := by
    have h := scalar_coefficient_le (Γ.index : ℝ) ((UL).constant * (UR).constant) (c * H)
      profileCoefficient rawAmplitude
      (CanonicalLiteralExceptionalPaidAtomBudget.pairConstant (K := K) cap annulus)
      allConstant ((1 + fourierHeight ξ) ^ heightOrder)
      (CanonicalLiteralExceptionalAtomBudget.pairDegree cap)
      (Nat.cast_nonneg _) (zero_le_one.trans hprofileCoefficient)
      (zero_le_one.trans hrawAmplitude)
      (CanonicalLiteralExceptionalPaidAtomBudget.pairConstant_pos cap annulus hannulus).le
      hcH hpair hbound
    calc
      _ = (Γ.index : ℝ) * ((UL).constant * (UR).constant) * amplitude ^ 4 * (c * H) := by ring
      _ ≤ _ := h
  have henv : 0 ≤ envelope := mul_nonneg
    (pow_nonneg (zero_le_one.trans hannulus) _)
    (mul_nonneg (mass).commonEnvelope_nonneg (orbitalFieldFactor_nonneg K))
  have hb := CanonicalLiteralExceptionalRelativeSource.ordinary_small_loss_bound
    (chart := chart) (P := P) (R := R)
    (hclass := hclass) (hsector := hsector) (X := X)
    (hX := hX) (label := label) (F := F)
    (parent := data x) (oldMoving := Q.moving) (correction := Q.correction)
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms) (thetaPair := thetaPair)
    (hcorr := hcorrection) (remaining := Q.remaining) («extra» := extra)
    (firstSupport := firstSupport) (hfirst := hfirstSupport) (hextra := rfl)
    (hone := hone) (hroot := hroot) (hemb := hemb)
    (annulus := annulus) («amplitude» := amplitude) (hannulus := hannulus)
    («hamplitude» := hamplitude) (cap := cap) («LD» := LD)
    («RD» := RD) (hleftCommon := hleftCommon) (hrightCommon := hrightCommon)
    (rowProfileBound := rowProfileBound) (hrowProfileBound := hrowProfileBound) (hrowProfile := hrowProfile)
    (first := first) (slotLoss := slotLoss) (firstProfile := firstProfile)
    (hfirstL := leftResult.property.2.2.2.2.2.2.2.2.2.1) (hfirstR := rightResult.property.2.2.2.2.2.2.2.2.2.1) (hsecondL := leftResult.property.2.2.2.2.2.2.2.2.2.2.1)
    (hsecondR := rightResult.property.2.2.2.2.2.2.2.2.2.2.1) (hplaces := hplaces) (hscalar := hscalarActual)
    (primitive := primitive) (hZ := hZ) (hstep := hstep)
    (hq := hq) (herrorPrime := herrorPrime) (columnLoss := columnLoss)
    (cutoffExponent := cutoffExponent) (hradius := hradius) (hcutoff := hcutoff)
    (hproduct := hproduct) (hcapL := hcapL) (hcapR := hcapR)
    (hprimeOriginalL := hprimeOriginalL) (hprimeOriginalR := hprimeOriginalR) (hproductOriginalL := hproductOriginalL)
    (hproductOriginalR := hproductOriginalR) (hprimeL := hprimeL) (hprimeR := hprimeR)
    (hslotL := hslotL) (hslotR := hslotR) («hamplitudeOne» := hamplitudeOne)
    (hslotLoss := hslotLoss) (normalization := normalization) (firstTotal := firstTotal)
    (hprimeLowerL := hprimeLowerL) (hprimeLowerR := hprimeLowerR) (hnormalization := hnormalization)
    (domain := hdomain) (hprofileL₁ := hprofileL₁.2.2) (hprofileL₂ := hprofileL₂.2.2)
    (hprofileR₁ := hprofileR₁.2.2) (hprofileR₂ := hprofileR₂.2.2) (htotal := htotal)
    (loss := loss) (hloss := hloss) (hsupport := hsupport)
    (hcutoffPaid := hcutoffPaid) (hslots := hslotsR)
    ξ
  have hpositive := ordinaryConstant_pos (A := A) (σ := σ) (η := η) (hS := hS) primitive
  have hc := hcoefficient
    (ordinaryConstant (A := A) (σ := σ) (η := η) (hS := hS) primitive) 1
    (by simpa only [mul_one] using hpositive.le)
    (by simpa only [mul_one] using hgrowth.2.2)
  simp only [mul_one] at hc
  apply coefficient_mono (henvelope := henv) (hpower := Real.rpow_nonneg (zero_le_one.trans hZ.le) _)
    (hradical := Nat.cast_nonneg _) (hdivisor := Real.rpow_nonneg (zero_le_one.trans hZ.le) _) (hcoefficient := hc)
  simpa only [rightResult.property.2.2.2.2.2.1] using hb

end ActualPair

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalSourceBudget

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalSourceBudget.result_original_property
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalSourceBudget.centered_small_loss_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalSourceBudget.ordinary_small_loss_bound

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalSourceBudget.coefficient_pos
