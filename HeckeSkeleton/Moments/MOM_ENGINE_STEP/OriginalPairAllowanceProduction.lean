import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedOriginalLabelMass
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Original scalar windows produce the actual first-allowance input

The two side windows are constructed from their positive original Gauss
scales. The norm-length dictionaries are read from the same original
nominal geometry and its actual second common ideals. A single fixed
annulus threshold bounds the clipping logarithms before the moving base
is chosen. The final allowance margin then follows from the individual
support, clipping, width, mesh and dyadic errors.

No child weight, branch weight, terminal sum, kernel mass, or allowance
margin is an input. Neither capacity child nor its removed set is chosen
again. The first Cauchy side is a parameter, and all slot counts use the
same construction.
-/

noncomputable section
open HeckeGeneral.Arithmetic
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open CommonSupportMass

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [IsPrincipalIdealRing A.R]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {ω ψ : HeckeCharacter F}

namespace SecondSideFrame

variable {side : SecondColumnSide} {k : ℕ}
variable (f : SecondSideFrame (V := V) C R Ray side k)

/-- All but the first length are the logarithms of their actual positive
scales. The first length is their complement in the original total.
The lower window for the product proves its single-factor inequality.
This also covers an empty prime product. -/
def originalScaleWindowOfProduct (Z a₀ : ℝ) (hZ : 1 < Z)
    (hscale : Z ^ a₀ ≤ f.normalizationScale) : f.OriginalScaleWindow Z a₀ := by
  let r : ℝ := Real.log f.gaussScale₂ / Real.log Z
  let p : Fin k → ℝ := fun i => Real.log (f.gaussSlotScale i) / Real.log Z
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hr : Z ^ r = f.gaussScale₂ :=
    Real.rpow_logb hz (ne_of_gt hZ) f.gaussScale₂_pos
  have hp (i : Fin k) : Z ^ p i = f.gaussSlotScale i :=
    Real.rpow_logb hz (ne_of_gt hZ) (f.gaussSlotScale_pos i)
  have hprod (s : Finset (Fin k)) :
      Z ^ (∑ i ∈ s, p i) = ∏ i ∈ s, f.gaussSlotScale i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, Real.rpow_add hz, hp, ih]
  have hleft : Z ^ (a₀ - r - ∑ i, p i) ≤ f.gaussScale₁ := by
    have hpositive : 0 < f.gaussScale₂ * ∏ i, f.gaussSlotScale i :=
      mul_pos f.gaussScale₂_pos (Finset.prod_pos fun i _ => f.gaussSlotScale_pos i)
    apply (mul_le_mul_iff_left₀ hpositive).mp
    calc
      _ = Z ^ (a₀ - r - ∑ i, p i) * (Z ^ r * Z ^ (∑ i, p i)) := by
        rw [hr, hprod Finset.univ]
      _ = Z ^ a₀ := by
        rw [← Real.rpow_add hz, ← Real.rpow_add hz]
        congr 1
        ring
      _ ≤ f.normalizationScale := hscale
      _ = _ := by
        unfold normalizationScale extraGaussScale
        ring
  exact {
    leftLength := a₀ - r - ∑ i, p i
    rightLength := r
    slotLength := p
    left_lower := hleft
    right_lower := hr.le
    slot_lower := fun i => (hp i).le
    degree := by ring }

end SecondSideFrame

namespace OriginalPairAllowanceProduction

/-- The constant is fixed by the original annulus and a positive error
budget. It does not depend on profiles, Fourier parameters or labels. -/
def annulusThreshold (annulus error : ℝ) : ℝ :=
  max 2 (Real.exp (2 * Real.log annulus / error))

theorem annulusThreshold_gt_one (annulus error : ℝ) :
    1 < annulusThreshold annulus error :=
  lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)

/-- The logarithmic clipping cost is bounded uniformly for both plains
of every actual rectangle, at all bases above the fixed threshold. -/
theorem annulus_error_le (annulus error Z left right : ℝ)
    (herror : 0 < error) (hZ : annulusThreshold annulus error ≤ Z)
    (hleft : 1 ≤ left) (hle : left ≤ annulus)
    (hright : 1 ≤ right) (hre : right ≤ annulus) :
    (Real.log left + Real.log right) / Real.log Z ≤ error := by
  have hZ1 : 1 < Z := (annulusThreshold_gt_one annulus error).trans_le hZ
  have hexp : Real.exp (2 * Real.log annulus / error) ≤ Z :=
    (le_max_right _ _).trans hZ
  have hlog := Real.log_le_log (Real.exp_pos (2 * Real.log annulus / error)) hexp
  rw [Real.log_exp] at hlog
  have hbound : 2 * Real.log annulus ≤ error * Real.log Z := by
    have h := (div_le_iff₀ herror).mp hlog
    nlinarith
  have hl := Real.log_le_log (zero_lt_one.trans_le hleft) hle
  have hr := Real.log_le_log (zero_lt_one.trans_le hright) hre
  apply (div_le_iff₀ (Real.log_pos hZ1)).mpr
  linarith

/-- One choice of the individual error and mesh budgets puts the
remaining scalar loss in the quarter reserved by the image-mass
theorem. The original moving and pool lengths are left explicit for
the actual tag transport. -/
theorem remaining_le_quarter (wo ell error mesh ε : ℝ)
    (herror : error ≤ 3 * ε / 40) (hmesh : mesh ≤ ε / 8) :
    wo + ell + 5 * error / 3 + mesh ≤ ε / 4 + (wo + ell) := by
  linarith

def commonLength (side : SecondColumnSide) (Z : ℝ) (D E : Ideal (𝓞 F)) : ℝ :=
  match side with
  | .left => idealLogLength Z D
  | .right => idealLogLength Z E

def boundary (side : SecondColumnSide) (Z : ℝ) (D E : Ideal (𝓞 F)) : ℝ :=
  match side with
  | .left => firstAllowance (idealLogLength Z D) (idealLogLength Z E)
      (idealLogLength Z (firstActiveRadical D E))
  | .right => firstAllowance (idealLogLength Z E) (idealLogLength Z D)
      (idealLogLength Z (firstActiveRadical D E))

def normalization (side : SecondColumnSide) (Z total : ℝ) (D E : Ideal (𝓞 F)) : ℝ :=
  match side with
  | .left => firstLeftAllowance Z total D E
  | .right => firstRightAllowance Z total D E

theorem normalization_eq (side : SecondColumnSide) (Z a q w : ℝ)
    (D E : Ideal (𝓞 F)) :
    normalization side Z (a + q) D E =
      Z ^ ((a - commonLength side Z D E - w) + q + w + boundary side Z D E) := by
  cases side with
  | left => exact firstLeftAllowance_second_exponent Z a q w D E
  | right => exact firstRightAllowance_second_exponent Z a q w D E

end OriginalPairAllowanceProduction

namespace ActualCapacityNormLengths

variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {cal : s.Calibration (σ := σ) ω ψ} (input : cal.CapacityInput)

/-- Read the arithmetic lengths from one original nominal geometry.
The chosen second side changes only c₂, which has no effect on the
shared row/support or the two common norms in this dictionary. -/
def ofOriginalLabels (geometry : NominalChildGeometry) (sideCommon Z ell : ℝ)
    (D E U N : Ideal (𝓞 F))
    (hbase : s.base = Z)
    (hgeometry : input.skeleton = { geometry with c₂ := sideCommon })
    (hgcd : geometry.g₂ = idealLogLength Z (gcd D E))
    (hunit : geometry.t₂ = idealLogLength Z U)
    (hnonunit : geometry.V = idealLogLength Z N)
    (hcommon : input.b₂ = (idealLogLength Z D + idealLogLength Z E) / 2)
    (hradical : input.p₂ = idealLogLength Z (commonRadical D E))
    (hpool : input.ell = ell) :
    ActualCapacityNormLengths input Z (geometry.A - geometry.c - geometry.w)
      (geometry.q + geometry.R + geometry.E) geometry.wo geometry.w
      geometry.Krow geometry.g ell D E U N where
  base_eq := hbase
  degree_eq := by rw [hgeometry]
  support_eq := by rw [hgeometry]
  moving_eq := by rw [hgeometry]
  removed_eq := by rw [hgeometry]
  row_eq := by rw [hgeometry]
  enlargement_eq := by rw [hgeometry]
  gcd_eq := by simpa only [hgeometry] using hgcd
  unit_eq := by simpa only [hgeometry] using hunit
  nonunit_eq := by simpa only [hgeometry] using hnonunit
  common_eq := hcommon
  radical_eq := hradical
  pool_eq := hpool

end ActualCapacityNormLengths

namespace ActualAllocatedSource.Calibration.CapacityInput

variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {cal : s.Calibration (σ := σ) ω ψ} (input : cal.CapacityInput)

/-- Individual original error windows. These are bounds on raw
capacity fields, before deletion; there is no combined allowance or
mass inequality in this input. -/
structure OriginalErrorWindows (annulus error meshBound : ℝ) : Prop where
  left_annulus : input.leftAnnulus ≤ annulus
  right_annulus : input.rightAnnulus ≤ annulus
  support : input.supportError ≤ error
  raw_clip : input.rawClipError ≤ error
  width : input.widthError ≤ error
  dyadic : input.delta ≤ error
  kappa : cal.parameters.κ ≤ 1
  mesh : input.mesh ≤ meshBound

end ActualAllocatedSource.Calibration.CapacityInput

namespace ActualCapacityNormLengths

variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {cal : s.Calibration (σ := σ) ω ψ} {input : cal.CapacityInput}
variable {Z a₀ q wo w krow g ell : ℝ} {D E U N : Ideal (𝓞 F)}
variable (lengths : ActualCapacityNormLengths input Z a₀ q wo w krow g ell D E U N)

/-- The four actual errors and the one-slot mesh overshoot pay the
computed slack. The annulus logarithm uses the same preselected base
threshold on both sides. -/
theorem slack_le_of_original_windows (annulus error mesh boundary : ℝ)
    (herror : 0 < error)
    (hZ : OriginalPairAllowanceProduction.annulusThreshold annulus error ≤ Z)
    (windows : input.OriginalErrorWindows annulus error mesh)
    (hboundary : input.boundary = boundary) :
    lengths.slack ≤ boundary + 5 * error / 3 + mesh := by
  have hannulus := OriginalPairAllowanceProduction.annulus_error_le
    annulus error Z input.leftAnnulus input.rightAnnulus herror hZ
    input.leftAnnulus_one windows.left_annulus input.rightAnnulus_one windows.right_annulus
  have hmesh : cal.parameters.κ * input.mesh ≤ mesh := by
    calc
      _ ≤ 1 * input.mesh :=
        mul_le_mul_of_nonneg_right windows.kappa input.mesh_nonneg
      _ = input.mesh := one_mul _
      _ ≤ mesh := windows.mesh
  unfold slack
  rw [hboundary]
  linarith [windows.support, windows.raw_clip, windows.width, windows.dyadic]

end ActualCapacityNormLengths

section Pair

variable {k l kLeft kRight : ℕ}
variable (left : SecondSideFrame (V := V) C R Ray .left k)
variable (right : SecondSideFrame (V := V) C R Ray .right l)
variable (calL : left.source.Calibration (σ := σ) ω ψ)
variable (calR : right.source.Calibration (σ := σ) ω ψ)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (BL : left.source.FrozenAtomBounds) (BR : right.source.FrozenAtomBounds)
variable (IL : (left.arithmeticCalibration calL W BL).CapacityInput)
variable (IR : (right.arithmeticCalibration calR W BR).CapacityInput)

open OriginalPairAllowanceProduction

/-- Construct the complete original allowance input from the actual
labels and individual windows. The only product bound concerns the
original extra Gauss scales, and the only radius bound concerns the
original physical kernel. The needed combined margin is proved here.

An original-geometry constructor can supply hgeometryL/hgeometryR by
reduction; this theorem does not build a competing nominal geometry.
-/
def OriginalPairAllowanceWindow.ofOriginalWindows
    (side : SecondColumnSide) (geometry : NominalChildGeometry)
    (firstD firstE : Ideal (𝓞 F))
    (Z ell annulus error mesh : ℝ)
    (herror : 0 < error) (hZ : annulusThreshold annulus error ≤ Z)
    (hbaseL : left.source.base = Z) (hbaseR : right.source.base = Z)
    (hgeometryL : IL.skeleton =
      { geometry with c₂ := idealLogLength Z W.leftIdeal })
    (hgeometryR : IR.skeleton =
      { geometry with c₂ := idealLogLength Z W.rightIdeal })
    (hfirst : geometry.c = commonLength side Z firstD firstE)
    (hgcd : geometry.g₂ = idealLogLength Z (gcd W.leftIdeal W.rightIdeal))
    (hunit : geometry.t₂ = idealLogLength Z W.unitIdeal.val)
    (hnonunit : geometry.V = idealLogLength Z W.nonunitIdeal.val)
    (hcommonL : IL.b₂ = (idealLogLength Z W.leftIdeal + idealLogLength Z W.rightIdeal) / 2)
    (hcommonR : IR.b₂ = (idealLogLength Z W.leftIdeal + idealLogLength Z W.rightIdeal) / 2)
    (hradicalL : IL.p₂ = idealLogLength Z (commonRadical W.leftIdeal W.rightIdeal))
    (hradicalR : IR.p₂ = idealLogLength Z (commonRadical W.leftIdeal W.rightIdeal))
    (hpoolL : IL.ell = ell) (hpoolR : IR.ell = ell)
    (hboundaryL : IL.boundary = boundary side Z firstD firstE)
    (hboundaryR : IR.boundary = boundary side Z firstD firstE)
    (errorsL : IL.OriginalErrorWindows annulus error mesh)
    (errorsR : IR.OriginalErrorWindows annulus error mesh)
    (hdivisor : left.source.allocation.divisor = right.source.allocation.divisor)
    (hscaleL : Z ^ (geometry.A - geometry.c - geometry.w) ≤ left.normalizationScale)
    (hscaleR : Z ^ (geometry.A - geometry.c - geometry.w) ≤ right.normalizationScale)
    (hradius : Z ^ (-geometry.Krow - geometry.g) ≤
      W.radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) W.mask)).val) :
    OriginalPairAllowanceWindow left right calL calR W BL BR IL IR Z
      (normalization side Z (geometry.A + (geometry.q + geometry.R + geometry.E)) firstD firstE)
      (geometry.wo + ell + 5 * error / 3 + mesh) := by
  have hZ1 : 1 < Z := (annulusThreshold_gt_one annulus error).trans_le hZ
  let LL := ActualCapacityNormLengths.ofOriginalLabels IL geometry
    (idealLogLength Z W.leftIdeal) Z ell W.leftIdeal W.rightIdeal
    W.unitIdeal.val W.nonunitIdeal.val hbaseL hgeometryL hgcd hunit hnonunit
    hcommonL hradicalL hpoolL
  let LR := ActualCapacityNormLengths.ofOriginalLabels IR geometry
    (idealLogLength Z W.rightIdeal) Z ell W.leftIdeal W.rightIdeal
    W.unitIdeal.val W.nonunitIdeal.val hbaseR hgeometryR hgcd hunit hnonunit
    hcommonR hradicalR hpoolR
  have hl := LL.slack_le_of_original_windows annulus error mesh
    (boundary side Z firstD firstE) herror hZ errorsL hboundaryL
  have hr := LR.slack_le_of_original_windows annulus error mesh
    (boundary side Z firstD firstE) herror hZ errorsR hboundaryR
  refine {
    a₀ := geometry.A - geometry.c - geometry.w
    q := geometry.q + geometry.R + geometry.E
    wo := geometry.wo
    w := geometry.w
    krow := geometry.Krow
    g := geometry.g
    ell := ell
    boundary := boundary side Z firstD firstE
    normalization := ?_
    divisor := hdivisor
    leftLengths := LL
    rightLengths := LR
    leftScale := left.originalScaleWindowOfProduct Z _ hZ1 hscaleL
    rightScale := right.originalScaleWindowOfProduct Z _ hZ1 hscaleR
    radius := hradius
    margin := ?_ }
  · simpa only [hfirst] using normalization_eq side Z geometry.A
      (geometry.q + geometry.R + geometry.E) geometry.w firstD firstE
  · linarith

end Pair
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.originalScaleWindowOfProduct
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalPairAllowanceProduction.annulus_error_le
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalPairAllowanceProduction.remaining_le_quarter
#print axioms HeckeSkeleton.Moments.EngineStep.ActualCapacityNormLengths.ofOriginalLabels
#print axioms HeckeSkeleton.Moments.EngineStep.ActualCapacityNormLengths.slack_le_of_original_windows
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalPairAllowanceWindow.ofOriginalWindows
