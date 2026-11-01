import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActiveSecondWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalExceptionalPlainWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalOrdinaryExceptionalCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalEngineSmallParameters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalUnmaskedSecondStage

/-!
# The original exceptional geometry keeps its physical cutoff loss

The raw frequency window follows from the actual nonzero pair profiles,
the canonical radius and the original finite cutoff.  Each original
column annulus is paid once, and an actual physical mask contributes its
own exponent.  Reweighting and two literal row restrictions preserve
this window, including after the genuine gcd/nonunit extraction.

The resulting one-sixth cutoff cost is included in the final numerical
remainder.  The original first and second savings, normalizers and child
coordinates are unchanged.  No terminal remainder or row-count estimate
is an input.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalGeometry

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support CommonSupportMass

/-- The two actual column windows, original cutoff and physical mask
remain distinct before their exponents are added. -/
def paidCutoff (columnLoss cutoffExponent maskExponent : ℝ) : ℝ :=
  2 * columnLoss + cutoffExponent + maskExponent

theorem paidCutoff_nonneg {columnLoss cutoffExponent maskExponent : ℝ}
    (hcolumn : 0 ≤ columnLoss) (hcutoff : 0 ≤ cutoffExponent)
    (hmask : 0 ≤ maskExponent) :
    0 ≤ paidCutoff columnLoss cutoffExponent maskExponent := by
  unfold paidCutoff
  positivity

variable {K : Type} [Field K] [NumberField K]

section Remainder

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS} {kLeft kRight : ℕ}
variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)
variable (W : ActualSecondRowMass S C kLeft kRight)
variable (vStar r₁ r₂ slotError firstProfile : ℝ)

/-- The physical cutoff is paid in the same original remainder.  The
sixth-power count uses exactly one sixth of its exponent. -/
theorem centered_remainder_with_cutoff
    {ω ψ : HeckeCharacter K} {centered : Bool} {d : MomentData K ω ψ}
    {Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (hpadding : 0 ≤ padding) (loss volumeLoss cutoffLoss : ℝ) (hloss : 0 ≤ loss)
    (hsupport : G.supportError ≤ loss / 16)
    (hvolume : volumeLoss ≤ loss / 16) (hslot : slotError ≤ loss / 16)
    (hcutoff : cutoffLoss / 6 ≤ loss / 16) :
    let n := G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile
    n.remaining + n.widthError +
      (max (n.Aexp - (a.m + a.q)) 0 + 3 * n.stepσ +
        5 * n.δ / 6 + volumeLoss + n.slotError + cutoffLoss / 6) ≤
      (padding + 3 * step + loss / 2) + G.tag.exceptionalMovingLength Z step := by
  have htotal := domain.original_total_excess_le hpadding
  change max (G.skeleton.A - (a.m + a.q)) 0 ≤ padding at htotal
  dsimp only [OriginalNominalGeometry.exceptionalNumbers]
  linarith

/-- The uncentered branch pays the identical physical cutoff.  It
does not invoke a centered volume saving or introduce parent padding. -/
theorem ordinary_remainder_with_cutoff
    (loss cutoffLoss : ℝ) (hloss : 0 ≤ loss)
    (hsupport : G.supportError ≤ loss / 16) (hslot : slotError ≤ loss / 16)
    (hcutoff : cutoffLoss / 6 ≤ loss / 16) :
    let n := G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile
    n.remaining + n.widthError +
      (3 * n.stepσ + 5 * n.δ / 6 + n.slotError + cutoffLoss / 6) ≤
      (3 * step + loss / 2) + G.tag.exceptionalMovingLength Z step := by
  dsimp only [OriginalNominalGeometry.exceptionalNumbers]
  linarith

/-- Reading the actual first normalizer keeps all of the preceding
fields.  The two identities are the original allowance and original
total length, not a final normalization or remainder inequality. -/
theorem centered_remainder_at_normalization
    (normalization total : ℝ) (hZ : 1 < Z)
    (hN : normalization = firstLeftAllowance Z total G.ideals.first.val G.ideals.opposite.val)
    (htotal : total = G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E))
    {ω ψ : HeckeCharacter K} {centered : Bool} {d : MomentData K ω ψ}
    {Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (hpadding : 0 ≤ padding) (loss volumeLoss cutoffLoss : ℝ) (hloss : 0 ≤ loss)
    (hsupport : G.supportError ≤ loss / 16)
    (hvolume : volumeLoss ≤ loss / 16) (hslot : slotError ≤ loss / 16)
    (hcutoff : cutoffLoss / 6 ≤ loss / 16) :
    let n := G.exceptionalNumbersAtNormalization W vStar r₁ r₂ slotError firstProfile
      normalization total
    n.remaining + n.widthError +
      (max (n.Aexp - (a.m + a.q)) 0 + 3 * n.stepσ +
        5 * n.δ / 6 + volumeLoss + n.slotError + cutoffLoss / 6) ≤
      (padding + 3 * step + loss / 2) + G.tag.exceptionalMovingLength Z step := by
  rw [G.exceptionalNumbersAtNormalization_eq W vStar r₁ r₂ slotError firstProfile
    normalization total hZ hN htotal]
  exact centered_remainder_with_cutoff G W vStar r₁ r₂ slotError firstProfile domain
    hpadding loss volumeLoss cutoffLoss hloss hsupport hvolume hslot hcutoff

end Remainder

/-- The already fixed boundary parameter pays the two original
annuli and the finite cutoff, with no physical mask on the literal
second source.  The choice precedes every source, scale and row. -/
theorem fixed_small_cutoff_budget {step loss : ℝ}
    (hstep : 0 < step) (hloss : 0 < loss) :
    0 ≤ paidCutoff (CanonicalEngineSmallParameters.boundary step loss)
        (CanonicalEngineSmallParameters.boundary step loss) 0 ∧
      paidCutoff (CanonicalEngineSmallParameters.boundary step loss)
        (CanonicalEngineSmallParameters.boundary step loss) 0 / 6 ≤ loss / 16 ∧
      CanonicalEngineSmallParameters.supportError step loss ≤ loss / 16 := by
  have hb := (CanonicalEngineSmallParameters.boundary_pos hstep hloss).le
  have hsmall := CanonicalEngineSmallParameters.boundary_le_loss step loss
  dsimp only [paidCutoff, CanonicalEngineSmallParameters.supportError]
  constructor
  · linarith
  constructor <;> linarith

section PhysicalRows

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS} {left : Finset α} {right : Finset β}
variable {profiles : α → β → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D)
variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)
variable (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
variable (label : Fin (chart.rowLabelCount + 1))
variable (columnLoss cutoffExponent maskExponent : ℝ)
variable (hZ : 1 < Z)
variable (hradius : radius = CanonicalRowBall.gaussRadius G.retainedScale Z G.enlargement
  G.retainedScale_pos (zero_lt_one.trans hZ))
variable (hcutoff : X ≤ Z ^ cutoffExponent)
variable (hmask : ∀ M' ∈ M.powerset,
  (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) M')).val ≤
      Z ^ maskExponent)
variable (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
  (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤
    Z ^ (2 * (G.skeleton.A - G.skeleton.c - G.skeleton.w + columnLoss)))

local notation "Orbit" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "original" => chart.actualRows M X hX label

include hZ hradius hcutoff hmask hproduct in
/-- This is the original physical frequency, before division by any
gcd or nonunit factor.  Dead pair profiles require no column window. -/
theorem original_cutoff (h : Orbit) (hh : h ∈ (original).rows) :
    A.exteriorNorm ((original).originalIdeal h) ≤
      Z ^ (G.frequencyCenter + paidCutoff columnLoss cutoffExponent maskExponent) := by
  have hr : radius.val ≤ Z ^ (-Real.log G.retainedScale / Real.log Z - G.enlargement) := by
    rw [hradius, CanonicalRowBall.gaussRadius_eq_rpow G.retainedScale Z G.enlargement
      G.retainedScale_pos hZ]
  have hp := b.secondPhysicalCutoff_le_active_pair_windows hΓ hDiff C left right
    profiles M radius X hX Z cutoffExponent
      (-Real.log G.retainedScale / Real.log Z - G.enlargement) maskExponent
      (2 * (G.skeleton.A - G.skeleton.c - G.skeleton.w + columnLoss))
      (zero_lt_one.trans hZ) hcutoff hr hmask hproduct
  apply (chart.actualRows_originalNorm_le_physicalCutoff M X hX label h hh).trans
  convert hp using 1 <;>
    dsimp only [OriginalNominalGeometry.frequencyCenter, OriginalNominalGeometry.skeleton,
      OriginalNominalGeometry.retainedLength, paidCutoff] <;> congr 1 <;> ring

variable (weight : Orbit → ℂ) (keep₁ keep₂ : Orbit → Prop)
local notation "rows" =>
  (({ original with weight := weight }).restrictRows keep₁).restrictRows keep₂
variable {kLeft kRight : ℕ} (W : ActualSecondRowMass rows C kLeft kRight)
variable (vStar r₁ r₂ slotError firstProfile : ℝ)

include hZ hradius hcutoff hmask hproduct in
/-- Common-atom reweighting, the nonzero-correlation restriction and
an actual theta class all keep the original frequency.  The actual
fixed nonunit ideal in the row mass supplies the same extracted width. -/
theorem reweighted_restricted_cutoff (h : (rows).live) :
    let n := G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile
    A.exteriorNorm ((rows).originalIdeal h.val) ≤ (rows).normFactor C h.val *
      Z ^ (2 * (n.Aexp - n.c - n.w) - n.K₀ - n.g - n.g₂ - n.V₀ +
        paidCutoff columnLoss cutoffExponent maskExponent) := by
  have hrows : h.val ∈ (rows).rows := (Finset.mem_filter.mp h.property).1
  have horiginal : h.val ∈ (original).rows :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hrows).1).1
  have hp := original_cutoff chart G M X hX label columnLoss cutoffExponent maskExponent
    hZ hradius hcutoff hmask hproduct h.val horiginal
  change A.exteriorNorm ((rows).originalIdeal h.val) ≤
    Z ^ (G.frequencyCenter + paidCutoff columnLoss cutoffExponent maskExponent) at hp
  have he := (rows).original_window_after_extraction C Z hZ
    (G.frequencyCenter + paidCutoff columnLoss cutoffExponent maskExponent) h hp
  rw [W.nonunit_ideal h.val hrows] at he
  have hexponent :
      (G.frequencyCenter + paidCutoff columnLoss cutoffExponent maskExponent) -
        idealLogLength Z (gcd W.leftIdeal W.rightIdeal) -
        idealLogLength Z W.nonunitIdeal.val =
      2 * (G.skeleton.A - G.skeleton.c - G.skeleton.w) - G.skeleton.Krow -
        G.skeleton.g - idealLogLength Z (gcd W.leftIdeal W.rightIdeal) -
        idealLogLength Z W.nonunitIdeal.val +
        paidCutoff columnLoss cutoffExponent maskExponent := by
    unfold OriginalNominalGeometry.frequencyCenter
    ring
  change _ ≤ (rows).normFactor C h.val *
    Z ^ ((G.frequencyCenter + paidCutoff columnLoss cutoffExponent maskExponent) -
      idealLogLength Z (gcd W.leftIdeal W.rightIdeal) -
      idealLogLength Z W.nonunitIdeal.val) at he
  rw [hexponent] at he
  exact he

end PhysicalRows

section OriginalRadius

variable {A : SArithmeticData K} [IsPrincipalIdealRing A.R]
variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

/-- The literal unmasked source retains its actual chosen unit
generator.  Only its norm, which is one, is used here. -/
theorem unmasked_radius_window (hZ : 1 < Z) :
    Z ^ (-G.skeleton.Krow - G.skeleton.g) ≤
      (CanonicalRowBall.gaussRadius G.retainedScale Z G.enlargement
        G.retainedScale_pos (zero_lt_one.trans hZ)).val *
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)).val := by
  rw [empty_mask_generator_norm, mul_one,
    CanonicalRowBall.gaussRadius_eq_rpow G.retainedScale Z G.enlargement
      G.retainedScale_pos hZ]
  apply le_of_eq
  congr 1
  dsimp only [OriginalNominalGeometry.skeleton, OriginalNominalGeometry.retainedLength]
  ring

end OriginalRadius

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalGeometry

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalGeometry.original_cutoff
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalGeometry.reweighted_restricted_cutoff
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalGeometry.centered_remainder_with_cutoff
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalGeometry.fixed_small_cutoff_budget
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalGeometry.unmasked_radius_window
