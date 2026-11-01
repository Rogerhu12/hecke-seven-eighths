import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralScalarNormalForm
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussScaleCompensation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalExceptionalPlainWindows

/-!
# The literal exceptional Gauss scale and its original annulus cost

The first support extraction determines the extra Gauss product.  The
two norm transforms insert this product once.  The second extraction,
atlas transport, constant scaling and plain balancing preserve it.

Its lower bound is proved from the original prime-profile support on
the fixed positive annulus, including the actual frozen occurrences.
The two square roots pay the fixed annulus power once in their product.
No central-normalization inequality is supplied by the caller.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalGauss

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

abbrev scale {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k) : ℝ :=
  extraGaussScale d.gauss₁ d.gauss₂ d.gaussSlot

section LiteralProduct

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

theorem addGauss_scale (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ i, 0 < G i) :
    scale (d.addGauss G₁ G₂ G h₁ h₂ hG) =
      scale d * extraGaussScale G₁ G₂ G := by
  dsimp only [scale, CanonicalLiteralRectangles.Atoms.addGauss, extraGaussScale]
  rw [Finset.prod_mul_distrib]
  ring

variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

theorem extract_scale : scale (d.extract b) = scale d := d.extract_gaussScale b

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- The complete actual first and pool transform inserts only the
post-extraction central scale, once.  Its original scalars and phases
do not alter this positive product. -/
theorem secondInput_scale (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ) :
    scale (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂) =
      scale d * b.residualGaussScale d.base d.length (d.scale₁ false) (d.scale₂ false) := by
  change scale ((d.extract b).addGauss ((d.extract b).scale₁ false)
    ((d.extract b).scale₂ false) (fun i => (d.extract b).base ^ (d.extract b).length i)
    ((d.extract b).scale₁_pos false) ((d.extract b).scale₂_pos false)
    (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans (d.extract b).base_gt_one) _)) = _
  rw [addGauss_scale, extract_scale]
  rfl

end LiteralProduct

section FinalFrame

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {A : SArithmeticData K} {ι : Type*}
variable {columns : Finset ι} {ideal : ι → A.Exterior}
variable (atlas : SourceCartesianAtlas columns ideal)

theorem onAtlas_scale (count : k = atlas.slotCount) :
    scale (d.onAtlas atlas count) = scale d := by
  cases count
  rfl

variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

/-- Every removed second-stage Gauss occurrence remains in the
original product.  The actual scalar and balancing operations are
retained, rather than changing the source to obtain a lower bound. -/
theorem final_scale (count : b.keep.card = atlas.slotCount)
    (scalar : ℂ) (balance : Bool → ℝ) :
    scale ((((d.extract b).onAtlas atlas count).scale scalar).balancePlain balance) =
      scale d := by
  change scale ((d.extract b).onAtlas atlas count) = _
  rw [onAtlas_scale, extract_scale]

variable {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H J : Type*} [Fintype J] [DecidableEq J]
variable (S : ActualSecondCorrelationRows A σ H J)
variable (C : A.GeneralArithmeticContext σ η hS)
variable (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (columnIdeal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (columnIdeal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (L : Ideal (𝓞 K))
variable (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

theorem frame_scale :
    ((d.factors S side χ columnIdeal hideal firstSign false).frame C L selection hne)
      .normalizationScale = scale d := rfl

end FinalFrame

section OriginalAnnulus

variable {A : SArithmeticData K} {Γ : Subgroup A.U} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (raw : ParentRawAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)
variable (annulus : ℝ) (hannulus : 1 ≤ annulus)
variable (hwindow : window ⊆ Set.Ici annulus⁻¹) (ht : t ∈ heightDomain) (hZ : 1 < Z)
variable (cap : ℕ) (hcap : d.geometry.slotCount ≤ cap)
variable (support : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
variable (leftLabel rightLabel : raw.originalAtlas.labels support D)

local notation "left" => raw.originalAtlas.branch support D leftLabel
local notation "right" => raw.originalAtlas.branch support D rightLabel
local notation "length" => fun i => (d.geometry.slots i).length
local notation "NL" => (left).residualGaussScale Z length (Z ^ a.n₁) (Z ^ a.n₂)
local notation "NR" => (right).residualGaussScale Z length (Z ^ a.n₁) (Z ^ a.n₂)

include profiles hannulus hwindow ht hZ hcap in
/-- Two actual original occurrence labels with the same complete
extracted ideal yield this paid central window.  All frozen-prime
lower bounds are proved from the original profile support. -/
theorem original_pair_central :
    Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength - idealLogLength Z D) ≤
      annulus ^ cap * (Real.sqrt NL * Real.sqrt NR) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hp : Z ^ a.n₁ * Z ^ a.n₂ = Z ^ (a.n₁ + a.n₂) :=
    (Real.rpow_add hz _ _).symm
  have hl := raw.original_branch_gaussScale_lower profiles annulus hannulus hwindow ht hZ
    cap hcap support D leftLabel (Z ^ a.n₁) (Z ^ a.n₂) (a.n₁ + a.n₂)
      (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _) hp
  have hr := raw.original_branch_gaussScale_lower profiles annulus hannulus hwindow ht hZ
    cap hcap support D rightLabel (Z ^ a.n₁) (Z ^ a.n₂) (a.n₁ + a.n₂)
      (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _) hp
  have hcentral := second_source_central_scale_lower Z hz
    (a.n₁ + a.n₂ + d.geometry.totalLength - idealLogLength Z D)
    (annulus ^ cap * NL) (annulus ^ cap * NR) hl hr
  have ha : 0 ≤ annulus ^ cap := pow_nonneg (zero_le_one.trans hannulus) _
  apply hcentral.trans_eq
  rw [Real.sqrt_mul ha, Real.sqrt_mul ha]
  calc
    _ = (Real.sqrt (annulus ^ cap) * Real.sqrt (annulus ^ cap)) *
        (Real.sqrt NL * Real.sqrt NR) := by ring
    _ = _ := by rw [← pow_two, Real.sq_sqrt ha]

include profiles hannulus hwindow ht hZ hcap in
/-- The complete original common ideal includes the actual pool
prime power. Its original factorization identifies the displayed
exponent with the nominal A-c-w, without an extra inequality. -/
theorem original_pair_central_for_geometry {step : ℝ}
    (G : OriginalNominalGeometry (K := K) a Z step)
    (hD : D = (G.ideals.first * G.tag.extractionIdeal).val)
    (htotal : a.z = d.geometry.totalLength) :
    Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤
      annulus ^ cap * (Real.sqrt NL * Real.sqrt NR) := by
  have hfirst : (Ideal.absNorm G.ideals.first.val : ℝ) ≠ 0 :=
    (idealNorm_pos K G.ideals.first).ne'
  have htag : (Ideal.absNorm G.tag.extractionIdeal.val : ℝ) ≠ 0 :=
    (idealNorm_pos K G.tag.extractionIdeal).ne'
  have hlog : idealLogLength Z (G.ideals.first * G.tag.extractionIdeal).val =
      idealLogLength Z G.ideals.first.val + idealLogLength Z G.tag.extractionIdeal.val := by
    change idealLogLength Z (G.ideals.first.val * G.tag.extractionIdeal.val) = _
    simp only [idealLogLength, map_mul, Nat.cast_mul, Real.log_mul hfirst htag]
    ring
  have hexponent : a.n₁ + a.n₂ + d.geometry.totalLength - idealLogLength Z D =
      G.skeleton.A - G.skeleton.c - G.skeleton.w := by
    rw [hD, hlog, G.tag.extractionIdeal_length Z, ← htotal]
    dsimp only [OriginalNominalGeometry.skeleton]
    ring
  have h := original_pair_central raw profiles annulus hannulus hwindow ht hZ
    cap hcap support D leftLabel rightLabel
  rwa [hexponent] at h

end OriginalAnnulus

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalGauss

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalGauss.secondInput_scale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalGauss.final_scale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalGauss.frame_scale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalGauss.original_pair_central
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalGauss.original_pair_central_for_geometry
