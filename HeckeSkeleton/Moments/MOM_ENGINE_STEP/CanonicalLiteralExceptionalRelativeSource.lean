import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPaidSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalGauss
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalPaidNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPaidAtomBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPhysicalBox
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantCommonLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafSupport

/-!
# The actual exceptional magnitude at its original first normalization

The same original prime representatives supply the lower annular
window. The actual extraction history then identifies the two frame
Gauss products and proves their compensated central lower bound. The
original common row mass and the original first allowance are retained
when the actual paid terminal is normalized.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

namespace ActualHybridLeaf.ConstantAtomExtraction

variable {H U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {leaf : ActualHybridLeaf K H U V} (X : leaf.ConstantAtomExtraction)

/-- The original live coefficient, before its ordinary/exceptional
partition, proves that its actual extracted common scalar is nonzero. -/
theorem leftScalar_ne_zero_of_live (hlive : leaf.Live) : X.leftScalar ≠ 0 := by
  obtain ⟨h, hh, i, hi, hc⟩ := hlive.2.1
  rw [X.left h hh i hi] at hc
  exact left_ne_zero_of_mul hc

theorem rightScalar_ne_zero_of_live (hlive : leaf.Live) : X.rightScalar ≠ 0 := by
  obtain ⟨h, hh, i, hi, hc⟩ := hlive.2.2
  rw [X.right h hh i hi] at hc
  exact left_ne_zero_of_mul hc

end ActualHybridLeaf.ConstantAtomExtraction

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)

/-- This is a bound on each original prime occurrence, obtained from
its original representative and fixed lower annulus endpoint. -/
theorem literalOriginalAtoms_primeLowerWindow
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window orders (data ξ) amplitude)
    (annulus : ℝ) (hannulus : 0 < annulus) (ht : t ∈ heightDomain)
    (hwindow : window ⊆ Set.Ici annulus⁻¹) :
    ∀ i, ∀ p ∈ (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots i,
      Z ^ (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).length i ≤
        annulus * (Ideal.absNorm p.asIdeal : ℝ) := by
  intro i p hp
  exact profiles.primeScale_le_annulus_mul_norm annulus Z t hannulus
    (zero_lt_one.trans hZ) ht hwindow i p (Finset.mem_filter.mp hp).1

end CompleteMovingRowRecipe

namespace CanonicalLiteralExceptionalPaidSource.OriginalSide

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {F : CanonicalLiteralPhaseCalibration.FixedPhases A}
variable {ω ψ : HeckeCharacter K} {parent : MomentData K ω ψ}
variable {oldMoving : OriginalMovingFactors A P R} {correction : HeckeCharacter K}
variable {remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K}
variable {firstSupport secondSupport : Finset (Ideal (𝓞 K))} {window : Set ℝ} {Z : ℝ}
variable (D : OriginalSide (σ := σ) P R F parent oldMoving correction remaining extra
  firstSupport secondSupport window Z)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (S : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS) (side : SecondColumnSide)

theorem original_base : D.history.original.base = Z :=
  D.history.base_eq.symm.trans D.base_eq

/-- The final source retains the complete first Gauss product. All
second removed occurrences, scalar extractions and balancing are
already present in the literal provenance equality. -/
theorem normalizationScale_eq_original :
    (D.frame S C side).normalizationScale =
      D.history.first.residualGaussScale Z D.history.original.length
        (D.history.original.scale₁ false) (D.history.original.scale₂ false) := by
  change extraGaussScale D.atoms.gauss₁ D.atoms.gauss₂ D.atoms.gaussSlot = _
  rw [D.gauss_eq]
  have h := CanonicalLiteralExceptionalGauss.secondInput_scale D.history.original
    D.history.first P R D.history.power D.history.firstFixed D.history.poolFixed
    D.history.unitFixed D.history.firstElement D.history.poolElement D.history.unitElement
    D.history.first_generates D.history.pool_generates D.history.unit_generates
    D.history.firstTilt D.history.secondTilt (σ := σ)
  change extraGaussScale (historySecondInput P R D.history).gauss₁
    (historySecondInput P R D.history).gauss₂ (historySecondInput P R D.history).gaussSlot =
      extraGaussScale D.history.original.gauss₁ D.history.original.gauss₂
        D.history.original.gaussSlot * _ at h
  rw [h, D.original_gauss, one_mul, D.original_base]

/-- The lower central window is proved from original prime norms and
the original scale-product identity, before the second allocation. -/
theorem normalizationScale_annulus_lower
    (annulus : ℝ) (hannulus : 1 ≤ annulus) (cap : ℕ)
    (hcap : D.history.originalCount ≤ cap) (originalTotal : ℝ)
    (hproduct : D.history.original.scaleProduct false = Z ^ originalTotal)
    (hprime : ∀ i, ∀ p ∈ D.history.original.slots i,
      Z ^ D.history.original.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ)) :
    Z ^ (originalTotal - idealLogLength Z D.history.firstIdeal) ≤
      annulus ^ cap * (D.frame S C side).normalizationScale := by
  have hZ : 1 < Z := D.base_eq ▸ D.atoms.base_gt_one
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hp := D.history.first.originalScale_le_compensated Z D.history.original.length
    (D.history.original.scale₁ false) (D.history.original.scale₂ false) annulus cap
    hz (D.history.original.scale₁_pos false).le (D.history.original.scale₂_pos false).le
    hannulus hcap (fun i _ => hprime i (D.history.first.witness.2 i)
      (Finset.mem_filter.mp (D.history.first.witness_slots i)).1)
  have hproduct' : D.history.original.scale₁ false * D.history.original.scale₂ false *
      (∏ i, Z ^ D.history.original.length i) = Z ^ originalTotal := by
    simpa only [CanonicalLiteralRectangles.Atoms.scaleProduct, D.original_base] using hproduct
  rw [hproduct'] at hp
  change Z ^ originalTotal ≤ annulus ^ cap *
    (D.history.first.residualGaussScale Z D.history.original.length
      (D.history.original.scale₁ false) (D.history.original.scale₂ false) *
        (Ideal.absNorm D.history.firstIdeal : ℝ)) at hp
  have hnorm : 0 < (Ideal.absNorm D.history.firstIdeal : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h =>
      D.history.firstIdeal_ne_zero (Ideal.absNorm_eq_zero_iff.mp h))
  rw [Real.rpow_sub hz,
    rpow_idealLogLength Z hZ D.history.firstIdeal D.history.firstIdeal_ne_zero]
  apply (div_le_iff₀ hnorm).mpr
  rw [D.normalizationScale_eq_original S C side]
  convert hp using 1 <;> ring

end CanonicalLiteralExceptionalPaidSource.OriginalSide

namespace CanonicalLiteralExceptionalRelativeSource

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {F : CanonicalLiteralPhaseCalibration.FixedPhases A}
variable {ω ψ : HeckeCharacter K} {parent : MomentData K ω ψ}
variable {oldMoving : OriginalMovingFactors A P R} {correction : HeckeCharacter K}
variable {remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K}
variable {firstSupport secondSupport : Finset (Ideal (𝓞 K))} {window : Set ℝ} {Z : ℝ}
variable (left right : CanonicalLiteralExceptionalPaidSource.OriginalSide
  (σ := σ) P R F parent oldMoving correction remaining extra
  firstSupport secondSupport window Z)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (S : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS)

/-- The same actual extracted first ideal determines both Gauss
denominators. The fixed annulus cost appears once after square roots. -/
theorem original_pair_central
    (annulus : ℝ) (hannulus : 1 ≤ annulus) (cap : ℕ)
    (hcapL : left.history.originalCount ≤ cap) (hcapR : right.history.originalCount ≤ cap)
    (originalTotal : ℝ)
    (hproductL : left.history.original.scaleProduct false = Z ^ originalTotal)
    (hproductR : right.history.original.scaleProduct false = Z ^ originalTotal)
    (hprimeL : ∀ i, ∀ p ∈ left.history.original.slots i,
      Z ^ left.history.original.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ))
    (hprimeR : ∀ i, ∀ p ∈ right.history.original.slots i,
      Z ^ right.history.original.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ))
    (hcommon : left.history.firstIdeal = right.history.firstIdeal) :
    Z ^ (originalTotal - idealLogLength Z left.history.firstIdeal) ≤
      annulus ^ cap * (Real.sqrt (left.frame S C .left).normalizationScale *
        Real.sqrt (right.frame S C .right).normalizationScale) := by
  have hZ : 1 < Z := left.base_eq ▸ left.atoms.base_gt_one
  have hl := left.normalizationScale_annulus_lower S C .left annulus hannulus cap
    hcapL originalTotal hproductL hprimeL
  have hr := right.normalizationScale_annulus_lower S C .right annulus hannulus cap
    hcapR originalTotal hproductR hprimeR
  rw [← hcommon] at hr
  have h := second_source_central_scale_lower Z (zero_lt_one.trans hZ)
    (originalTotal - idealLogLength Z left.history.firstIdeal)
    (annulus ^ cap * (left.frame S C .left).normalizationScale)
    (annulus ^ cap * (right.frame S C .right).normalizationScale) hl hr
  have ha : 0 ≤ annulus ^ cap := pow_nonneg (zero_le_one.trans hannulus) _
  apply h.trans_eq
  rw [Real.sqrt_mul ha, Real.sqrt_mul ha]
  calc
    _ = (Real.sqrt (annulus ^ cap) * Real.sqrt (annulus ^ cap)) *
        (Real.sqrt (left.frame S C .left).normalizationScale *
          Real.sqrt (right.frame S C .right).normalizationScale) := by ring
    _ = _ := by rw [← pow_two, Real.sq_sqrt ha]

/-- The complete first ideal includes the original pool valuation.
Its literal norm identity gives the nominal exponent without paying
the same moving factor a second time. -/
theorem original_pair_central_for_geometry
    {a : RealParameters} {step : ℝ} (G : OriginalNominalGeometry (K := K) a Z step)
    (annulus : ℝ) (hannulus : 1 ≤ annulus) (cap : ℕ)
    (hcapL : left.history.originalCount ≤ cap) (hcapR : right.history.originalCount ≤ cap)
    (hproductL : left.history.original.scaleProduct false = Z ^ G.skeleton.A)
    (hproductR : right.history.original.scaleProduct false = Z ^ G.skeleton.A)
    (hprimeL : ∀ i, ∀ p ∈ left.history.original.slots i,
      Z ^ left.history.original.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ))
    (hprimeR : ∀ i, ∀ p ∈ right.history.original.slots i,
      Z ^ right.history.original.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ))
    (hfirstL : left.history.firstIdeal = (G.ideals.first * G.tag.extractionIdeal).val)
    (hfirstR : right.history.firstIdeal = (G.ideals.first * G.tag.extractionIdeal).val) :
    Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤
      annulus ^ cap * (Real.sqrt (left.frame S C .left).normalizationScale *
        Real.sqrt (right.frame S C .right).normalizationScale) := by
  have hfirst : (Ideal.absNorm G.ideals.first.val : ℝ) ≠ 0 :=
    (idealNorm_pos K G.ideals.first).ne'
  have htag : (Ideal.absNorm G.tag.extractionIdeal.val : ℝ) ≠ 0 :=
    (idealNorm_pos K G.tag.extractionIdeal).ne'
  have hlog : idealLogLength Z (G.ideals.first * G.tag.extractionIdeal).val =
      idealLogLength Z G.ideals.first.val + idealLogLength Z G.tag.extractionIdeal.val := by
    change idealLogLength Z (G.ideals.first.val * G.tag.extractionIdeal.val) = _
    simp only [idealLogLength, map_mul, Nat.cast_mul, Real.log_mul hfirst htag]
    ring
  have he : G.skeleton.A - idealLogLength Z left.history.firstIdeal =
      G.skeleton.A - G.skeleton.c - G.skeleton.w := by
    rw [hfirstL, hlog, G.tag.extractionIdeal_length Z]
    dsimp only [OriginalNominalGeometry.skeleton]
    ring
  have hp := original_pair_central left right S C annulus hannulus cap hcapL hcapR
    G.skeleton.A hproductL hproductR hprimeL hprimeR (hfirstL.trans hfirstR.symm)
  rwa [he] at hp

end CanonicalLiteralExceptionalRelativeSource

namespace CanonicalLiteralExceptionalRelativeSource

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
variable {C : A.GeneralArithmeticContext σ η hS} {columnsLeft : Finset α} {columnsRight : Finset β}
variable {pairProfiles : α → β → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {maskLabel : (∅ : Finset (HeightOneSpectrum A.R)).powerset}
variable (chart : SecondBlockProfileChart (E := ℝ) hΓ μv hDiff b C columnsLeft columnsRight
  pairProfiles finiteTest radius maskLabel.val)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (hclass : chart.NonunitLabelStable)
variable (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable {ω ψ : HeckeCharacter K}
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K)

local notation "Orbit" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "rawRows" => chart.actualRows ∅ X hX label

variable {kCommonL kCommonR : ℕ}
variable (leftAtoms : FrozenSourceAtoms A σ Orbit (rawRows).rows kCommonL)
variable (rightAtoms : FrozenSourceAtoms A σ Orbit (rawRows).rows kCommonR)
variable (thetaPair : parent.theta × parent.theta)
variable (hleft : leftAtoms.ideal = (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hright : rightAtoms.ideal = (primePowerProduct b.primes b.rightMultiplicity).val)
variable (bound : ℝ) (hbound : 0 ≤ bound)
variable (hprofile : ∀ q ∈ (rawRows).rows, ‖chart.weight q‖ ≤ bound)

local notation "S" => CanonicalLiteralExceptionalFactory.rows chart P R X hX label
  F parent oldMoving correction leftAtoms rightAtoms thetaPair
local notation "mass" => CanonicalLiteralExceptionalArithmetic.actualMass chart P R
  hclass X hX label F parent oldMoving correction leftAtoms rightAtoms thetaPair
    hleft hright bound hbound hprofile

variable {a : RealParameters} {Z step : ℝ}
variable (first : OriginalNominalGeometry (K := K) a Z step)
local notation "G" => CanonicalLiteralExceptionalNumbers.geometry chart X hX label first

variable {remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K}
variable {firstSupport secondSupport : Finset (Ideal (𝓞 K))} {window : Set ℝ}
variable (LD RD : CanonicalLiteralExceptionalPaidSource.OriginalSide
  (σ := σ) P R F parent oldMoving correction remaining extra
  firstSupport secondSupport window Z)

variable (r₁ r₂ slotError firstProfile normalization firstTotal : ℝ)
local notation "n" => (G).exceptionalNumbersAtNormalization mass (G).centeredExtractionLength
  r₁ r₂ slotError firstProfile normalization firstTotal

/-- The actual original common row mass, canonical physical radius,
computed dyad and original first allowance prove this relative budget.
The first normalizer is unchanged, and the only central compensation
is the fixed annulus cost already established from original atoms. -/
theorem actual_row_budget
    (annulus : ℝ) (hannulus : 1 ≤ annulus) (cap : ℕ)
    (hcapL : LD.history.originalCount ≤ cap) (hcapR : RD.history.originalCount ≤ cap)
    (hproductL : LD.history.original.scaleProduct false = Z ^ first.skeleton.A)
    (hproductR : RD.history.original.scaleProduct false = Z ^ first.skeleton.A)
    (hprimeL : ∀ i, ∀ p ∈ LD.history.original.slots i,
      Z ^ LD.history.original.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ))
    (hprimeR : ∀ i, ∀ p ∈ RD.history.original.slots i,
      Z ^ RD.history.original.length i ≤ annulus * (Ideal.absNorm p.asIdeal : ℝ))
    (hfirstL : LD.history.firstIdeal = (first.ideals.first * first.tag.extractionIdeal).val)
    (hfirstR : RD.history.firstIdeal = (first.ideals.first * first.tag.extractionIdeal).val)
    (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius first.retainedScale Z first.enlargement
      first.retainedScale_pos (zero_lt_one.trans hZ))
    (hnormalization : normalization = firstLeftAllowance Z firstTotal
      first.ideals.first.val first.ideals.opposite.val) :
    ((mass).originalRowAmplitude * Z ^ ((n).g₂ - (n).t₂) /
        (Real.sqrt (LD.frame S C .left).normalizationScale *
          Real.sqrt (RD.frame S C .right).normalizationScale)) *
      Z ^ (secondCommonChildWidth Z ((n).Aexp - (n).c - (n).w) (a.q + (n).R₀ + (n).E₀)
        (n).wo (n).K₀ (n).g (mass).leftIdeal (mass).rightIdeal (mass).unitIdeal.val (mass).nonunitIdeal.val +
        secondCommonChildAllowance Z (n).w (n).Bcommon (n).ell (mass).leftIdeal (mass).rightIdeal) /
        normalization ≤
      annulus ^ cap * ((mass).commonEnvelope * orbitalFieldFactor K) * Z ^ (n).remaining /
        (Ideal.absNorm (commonRadical (mass).leftIdeal (mass).rightIdeal) : ℝ) := by
  have hcentral := original_pair_central_for_geometry LD RD S C G annulus hannulus cap
    hcapL hcapR hproductL hproductR hprimeL hprimeR hfirstL hfirstR
  have hrow := CanonicalLiteralExceptionalNumbers.radius_window chart P R hclass X hX
    label F parent oldMoving correction leftAtoms rightAtoms thetaPair hleft hright
    bound hbound hprofile first r₁ r₂ slotError firstProfile hZ hradius
  have hdyad := (G).exceptionalNumbers_dyad_window mass (G).centeredExtractionLength
    r₁ r₂ slotError firstProfile
  have hremain := (G).exceptionalNumbersAtNormalization_remaining_window mass
    (G).centeredExtractionLength r₁ r₂ slotError firstProfile normalization firstTotal
    hZ hnormalization
  have hcost : 0 < annulus ^ cap := pow_pos (zero_lt_one.trans_le hannulus) _
  have hb := (mass).original_rowFactor_budget_with_centralCost Z hZ
    ((n).Aexp - (n).c - (n).w) (a.q + (n).R₀ + (n).E₀) (n).wo (n).w (n).Bcommon (n).K₀ (n).g (n).ell
    (LD.frame S C .left).normalizationScale (RD.frame S C .right).normalizationScale
    (n).parentWidth (n).remaining (n).g₂ (n).t₂ (n).rowError (annulus ^ cap)
    hcost hrow hcentral hdyad hremain
  have hNpos : 0 < normalization := by
    rw [hnormalization]
    exact firstLeftAllowance_pos Z firstTotal (zero_lt_one.trans hZ) _ _
  have hN := (G).exceptionalNumbersAtNormalization_normalizer mass (G).centeredExtractionLength
    r₁ r₂ slotError firstProfile normalization firstTotal hZ hNpos
  rwa [hN] at hb

end ActualRows

end CanonicalLiteralExceptionalRelativeSource

namespace CanonicalLiteralExceptionalRelativeSource

open CanonicalLiteralExceptionalPaidSource CanonicalLiteralExceptionalCharts

section ActualTerminalBounds

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
local notation "slotError" => ∑ i ∈ Finset.univ \ (RF).allocation.keep, slotLoss
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
local notation "orders" => centeredOrders (A := A) (σ := σ) (η := η) (hS := hS)
  primitive ε maskExp hε hmaskExp
local notation "order" => centeredOrder (A := A) (σ := σ) (η := η) (hS := hS)
  primitive ε maskExp hε hmaskExp
local notation "constant" => centeredConstant (A := A) (σ := σ) (η := η) (hS := hS)
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
variable (horder : idealLogLength Z (primePowerProduct b.primes b.leftMultiplicity).val ≤
  idealLogLength Z (primePowerProduct b.primes b.rightMultiplicity).val)
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
/-- The original centered source is divided by its existing first allowance.
The source estimate and the relative row budget are both constructed inside
this theorem. The exact original total-length discrepancy stays in `remaining`. -/
theorem centered_relative_bound (ξ : Joint) :
    (LF).exceptionalMagnitude RF EL ER characters ξ / normalization ≤
      envelope * coefficient ξ * Z ^ ((n).remaining + margin) / radical *
        Z ^ (-idealLogLength Z RD.divisor) := by
  have hsource := CanonicalLiteralExceptionalPaidSource.centered_magnitude_bound
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
        (n).slotError - idealLogLength Z RD.divisor + cutoffLoss / 6 =
      margin - idealLogLength Z RD.divisor := by ring
  rw [hexponent] at hsource
  have hsource' : Z ^ (-actualWidth) * (LF).exceptionalMagnitude RF EL ER characters ξ ≤
      rowFactor * coefficient ξ * Z ^ (margin - idealLogLength Z RD.divisor) := by
    simpa only [secondCommonChildWidth, secondCommonChildAllowance, mul_assoc] using hsource
  have hNpos : 0 < normalization := by
    rw [hnormalization]
    exact firstLeftAllowance_pos Z firstTotal (zero_lt_one.trans hZ) _ _
  have hN := (G).exceptionalNumbersAtNormalization_normalizer mass (G).centeredExtractionLength
    rL rR slotError firstProfile normalization firstTotal hZ hNpos
  have hrow := actual_row_budget chart P R hclass X hX label F parent oldMoving
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
  have hC := centeredConstant_pos (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExp hε hmaskExp
  have hheight := fourierHeight_nonneg ξ
  have hUL := (UL).constant_nonneg
  have hUR := (UR).constant_nonneg
  have hcoefficient : 0 ≤ coefficient ξ := by positivity
  have hb := CanonicalExceptionalPaidNormalization.relative_of_magnitude
    Z ((LF).exceptionalMagnitude RF EL ER characters ξ) rowFactor envelope radical (coefficient ξ)
    actualWidth actualWidth (n).parentWidth (n).remaining 0 margin
    (idealLogLength Z RD.divisor) hZ.le hcoefficient henv hradical
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
theorem centered_small_loss_bound
    (htotal : firstTotal = first.skeleton.A +
      (first.skeleton.q + first.skeleton.R + first.skeleton.E))
    (hpadding : 0 ≤ padding)
    (loss : ℝ) (hloss : 0 ≤ loss) (hsupport : first.supportError ≤ loss / 16)
    (hvolume : ε ≤ loss / 16)
    (hslots : slotError ≤ loss / 16) (hcutoffPaid : cutoffLoss / 6 ≤ loss / 16)
    (ξ : Joint) :
    (LF).exceptionalMagnitude RF EL ER characters ξ / normalization ≤
      envelope * coefficient ξ * Z ^ ((padding + 3 * step + loss / 2) + (G).tag.exceptionalMovingLength Z step) /
        radical * Z ^ (-idealLogLength Z RD.divisor) := by
  have hb := centered_relative_bound
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
  have hC := centeredConstant_pos (A := A) (σ := σ) (η := η) (hS := hS)
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

section Ordinary

local notation "orders" => ordinaryOrders (A := A) (σ := σ) (η := η) (hS := hS) primitive
local notation "constant" => ordinaryConstant (A := A) (σ := σ) (η := η) (hS := hS) primitive
variable {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain false parent a Z Y₁ Y₂ floor padding)
variable (hprofileL₁ : (orders).sup (schwartzSeminormFamily ℂ ℝ ℂ) (LD.model.left false) ≤ amplitude)
variable (hprofileL₂ : (orders).sup (schwartzSeminormFamily ℂ ℝ ℂ) (LD.model.right false) ≤ amplitude)
variable (hprofileR₁ : (orders).sup (schwartzSeminormFamily ℂ ℝ ℂ) (RD.model.left false) ≤ amplitude)
variable (hprofileR₂ : (orders).sup (schwartzSeminormFamily ℂ ℝ ℂ) (RD.model.right false) ≤ amplitude)

local notation "margin" => 3 * (n).stepσ + 5 * (n).δ / 6 + (n).slotError + cutoffLoss / 6
local notation "coefficient" ξ => ((Γ.index : ℝ) * constant * ((UL).constant * (UR).constant)) * amplitude ^ 4

include hclass hsector hcorr hfirst hextra hone hroot hemb
  hfirstL hfirstR hsecondL hsecondR hplaces hscalar hZ hstep hq herrorPrime
  hradius hcutoff hproduct hcapL hcapR hprimeOriginalL hprimeOriginalR
  hproductOriginalL hproductOriginalR hprimeL hprimeR hslotL hslotR
  hamplitudeOne hslotLoss hprimeLowerL hprimeLowerR hnormalization domain hprofileL₁ hprofileL₂ hprofileR₁ hprofileR₂ in
/-- The same original allowance normalizes the ordinary exceptional source.
Its absolute terminal is called directly; no completed magnitude estimate or
row-factor bound is an input. -/
theorem ordinary_relative_bound (ξ : Joint) :
    (LF).ordinaryExceptionalMagnitude RF characters ξ / normalization ≤
      envelope * coefficient ξ * Z ^ ((n).remaining + margin) / radical *
        Z ^ (-idealLogLength Z RD.divisor) := by
  have hsource := CanonicalLiteralExceptionalPaidSource.ordinary_magnitude_bound
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
    (domain := domain) (hprofileL₁ := hprofileL₁) (hprofileL₂ := hprofileL₂) (hprofileR₁ := hprofileR₁)
    (hprofileR₂ := hprofileR₂) ξ
  have hexponent : 3 * (n).stepσ + 5 * (n).δ / 6 + (n).slotError -
        idealLogLength Z RD.divisor + cutoffLoss / 6 =
      margin - idealLogLength Z RD.divisor := by ring
  rw [hexponent] at hsource
  have hsource' : Z ^ (-actualWidth) * (LF).ordinaryExceptionalMagnitude RF characters ξ ≤
      rowFactor * coefficient ξ * Z ^ (margin - idealLogLength Z RD.divisor) := by
    simpa only [secondCommonChildWidth, secondCommonChildAllowance, mul_assoc] using hsource
  have hNpos : 0 < normalization := by
    rw [hnormalization]
    exact firstLeftAllowance_pos Z firstTotal (zero_lt_one.trans hZ) _ _
  have hN := (G).exceptionalNumbersAtNormalization_normalizer mass (G).centeredExtractionLength
    rL rR slotError firstProfile normalization firstTotal hZ hNpos
  have hrow := actual_row_budget chart P R hclass X hX label F parent oldMoving
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
  have hC := ordinaryConstant_pos (A := A) (σ := σ) (η := η) (hS := hS) primitive
  have hUL := (UL).constant_nonneg
  have hUR := (UR).constant_nonneg
  have hcoefficient : 0 ≤ coefficient ξ := by positivity
  have hb := CanonicalExceptionalPaidNormalization.relative_of_magnitude
    Z ((LF).ordinaryExceptionalMagnitude RF characters ξ) rowFactor envelope radical (coefficient ξ)
    actualWidth actualWidth (n).parentWidth (n).remaining 0 margin
    (idealLogLength Z RD.divisor) hZ.le hcoefficient henv hradical
    hsource' hrow' (by simp)
  simpa only [hN, add_zero] using hb

include hclass hsector hcorr hfirst hextra hone hroot hemb
  hfirstL hfirstR hsecondL hsecondR hplaces hscalar hZ hstep hq herrorPrime
  hradius hcutoff hproduct hcapL hcapR hprimeOriginalL hprimeOriginalR
  hproductOriginalL hproductOriginalR hprimeL hprimeR hslotL hslotR
  hamplitudeOne hslotLoss hprimeLowerL hprimeLowerR hnormalization domain hprofileL₁ hprofileL₂ hprofileR₁ hprofileR₂ firstProfile in
/-- The original total length cancels its exact normalization discrepancy.
The fixed support, profile-slot and physical cutoff payments then yield
this source's final loss without a terminal remainder hypothesis. -/
theorem ordinary_small_loss_bound
    (htotal : firstTotal = first.skeleton.A +
      (first.skeleton.q + first.skeleton.R + first.skeleton.E))

    (loss : ℝ) (hloss : 0 ≤ loss) (hsupport : first.supportError ≤ loss / 16)

    (hslots : slotError ≤ loss / 16) (hcutoffPaid : cutoffLoss / 6 ≤ loss / 16)
    (ξ : Joint) :
    (LF).ordinaryExceptionalMagnitude RF characters ξ / normalization ≤
      envelope * coefficient ξ * Z ^ ((3 * step + loss / 2) + (G).tag.exceptionalMovingLength Z step) /
        radical * Z ^ (-idealLogLength Z RD.divisor) := by
  have hb := ordinary_relative_bound
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
    (hprimeLowerR := hprimeLowerR) (hnormalization := hnormalization) (domain := domain)
    (hprofileL₁ := hprofileL₁) (hprofileL₂ := hprofileL₂) (hprofileR₁ := hprofileR₁)
    (hprofileR₂ := hprofileR₂) ξ
  have hr := CanonicalLiteralExceptionalGeometry.ordinary_remainder_with_cutoff
    G mass (G).centeredExtractionLength rL rR slotError firstProfile loss cutoffLoss
    hloss hsupport hslots hcutoffPaid
  have hn := (G).exceptionalNumbersAtNormalization_eq mass (G).centeredExtractionLength
    rL rR slotError firstProfile normalization firstTotal hZ hnormalization htotal
  have hexponent : (n).remaining + margin ≤
      (3 * step + loss / 2) + (G).tag.exceptionalMovingLength Z step := by
    simpa only [hn, OriginalNominalGeometry.exceptionalNumbers, add_zero] using hr
  have hC := ordinaryConstant_pos (A := A) (σ := σ) (η := η) (hS := hS) primitive
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

end Ordinary

end ActualTerminalBounds

end CanonicalLiteralExceptionalRelativeSource

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalRelativeSource.actual_row_budget
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalRelativeSource.centered_relative_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalRelativeSource.ordinary_relative_bound

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalRelativeSource.centered_small_loss_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalRelativeSource.ordinary_small_loss_bound
