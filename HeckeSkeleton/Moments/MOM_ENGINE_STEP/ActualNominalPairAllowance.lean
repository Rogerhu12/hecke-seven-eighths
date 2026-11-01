import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNominalGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalPairAllowanceProduction

/-!
# The original nominal construction supplies the pair allowance

The capacity inputs in this file are computed by the original nominal
geometry provider. Their norm dictionaries, common lengths, boundary,
pool length, kappa bound and mesh are conclusions of that construction.
Only the separate original scale, radius and individual error windows
remain inputs. The second side permutes the original second ideals and
uses the same first geometry, retained dyad and original tag.

The selected first ideal may be either original first Cauchy side. The
right-side normalization is recovered from the actual equality of the
two common-support sets; the active first radical is not assumed to be
symmetric on arbitrary ideals.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open CommonSupportMass HeckePort.Moments
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

/-- The active radical is symmetric on the genuine common-support
labels. No symmetry is asserted for arbitrary ideal pairs. -/
theorem firstActiveRadical_swap_of_support (D E : Ideal (𝓞 K))
    (h : primeSupport D = primeSupport E) :
    firstActiveRadical E D = firstActiveRadical D E := by
  have hs : (primeSupport E).filter (fun P =>
      (normalizedFactors E).count P % 6 ≠ (normalizedFactors D).count P % 6) =
      (primeSupport D).filter (fun P =>
        (normalizedFactors D).count P % 6 ≠ (normalizedFactors E).count P % 6) := by
    ext P
    simp only [Finset.mem_filter, h, ne_comm]
  unfold firstActiveRadical
  rw [hs]

theorem firstLeftAllowance_swap_of_support (Z total : ℝ) (D E : Ideal (𝓞 K))
    (h : primeSupport D = primeSupport E) :
    firstLeftAllowance Z total E D = firstRightAllowance Z total D E := by
  unfold firstLeftAllowance firstRightAllowance
  rw [firstActiveRadical_swap_of_support D E h]

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

/-- Transport to the literal base field of an original source. This
does not change any ideal, scale, tag, error or retained dyad. -/
def atBase (base : ℝ) (hbase : base = Z) :
    OriginalNominalGeometry (K := K) a base step where
  ideals := G.ideals
  tag := G.tag
  retainedScale := G.retainedScale
  retainedScale_pos := G.retainedScale_pos
  supportError := G.supportError
  supportError_nonneg := G.supportError_nonneg
  retained_upper := by simpa only [hbase] using G.retained_upper
  error_prime_lower e p ht := by simpa only [hbase] using G.error_prime_lower e p ht

theorem atBase_skeleton (base : ℝ) (hbase : base = Z) :
    (G.atBase base hbase).skeleton = G.skeleton := by
  subst base
  rfl

theorem atBase_boundary (base : ℝ) (hbase : base = Z) :
    (G.atBase base hbase).boundary = G.boundary := by
  subst base
  rfl

/-- The existing ideal permutation gives the opposite second side.
The first ideal, opposite first ideal and all original scalar windows
are retained. -/
def swapSecond : OriginalNominalGeometry (K := K) a Z step where
  ideals := G.ideals.swapSecond
  tag := G.tag
  retainedScale := G.retainedScale
  retainedScale_pos := G.retainedScale_pos
  supportError := G.supportError
  supportError_nonneg := G.supportError_nonneg
  retained_upper := G.retained_upper
  error_prime_lower := G.error_prime_lower

theorem swapSecond_skeleton :
    G.swapSecond.skeleton =
      { G.skeleton with c₂ := idealLogLength Z G.ideals.secondOpposite.val } := by
  simp only [skeleton, swapSecond, OriginalNominalIdeals.swapSecond, gcd_comm]

theorem swapSecond_boundary : G.swapSecond.boundary = G.boundary := rfl

end OriginalNominalGeometry

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {ω ψ : HeckeCharacter K}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace ActualAllocatedSource.Calibration.OriginalLengthBinding

variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {D : s.Calibration (σ := σ) ω ψ}
variable {parent : MomentData K ω ψ} {a : RealParameters} {step : ℝ}
variable {G : OriginalNominalGeometry (K := K) a s.base step}
variable (B : D.OriginalLengthBinding parent a step G)

/-- Individual bounds on the original retained-scale and atom records
supply the capacity error windows. The same scale error controls both
the dyadic discrepancy and the width error of the computed input. -/
def originalErrorWindows
    (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
    (hfit : parent.geometry.fitsMesh mesh) (atoms : D.OriginalCapacityAtoms)
    (annulus error : ℝ)
    (hleft : atoms.leftAnnulus ≤ annulus) (hright : atoms.rightAnnulus ≤ annulus)
    (hsupport : G.supportError ≤ error) (hraw : B.rawScaleError ≤ error)
    (hwidth : B.scales.error ≤ error) :
    (B.capacityInput hstep mesh hmesh hfit atoms).OriginalErrorWindows annulus error mesh where
  left_annulus := hleft
  right_annulus := hright
  support := hsupport
  raw_clip := hraw
  width := hwidth
  dyadic := hwidth
  kappa := by rw [B.kappa]; exact B.parent_region.2.1
  mesh := le_rfl

end ActualAllocatedSource.Calibration.OriginalLengthBinding

section Pair

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsPrincipalIdealRing A.R]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {k l kLeft kRight : ℕ}
variable (left : SecondSideFrame (V := V) C R Ray .left k)
variable (right : SecondSideFrame (V := V) C R Ray .right l)
variable (calL : left.source.Calibration (σ := σ) ω ψ)
variable (calR : right.source.Calibration (σ := σ) ω ψ)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (frozenL : left.source.FrozenAtomBounds) (frozenR : right.source.FrozenAtomBounds)

open OriginalPairAllowanceProduction

/-- The two capacity inputs and their complete first allowance are
produced together from the original nominal length bindings. No input
capacity ledger, norm-length dictionary, combined slack, allowance
margin, child weight or kernel mass is required.

For the first right Cauchy side choose its common ideal as G.ideals.first;
firstLeftAllowance_swap_of_support then gives the literal original right
normalization from the true common-support label identity.
-/
def OriginalPairAllowanceWindow.ofNominalGeometry
    (parent : MomentData K ω ψ) (a : RealParameters) (Z step : ℝ)
    (G : OriginalNominalGeometry (K := K) a Z step)
    (hbaseL : left.source.base = Z) (hbaseR : right.source.base = Z)
    (hsecond : G.ideals.second.val = W.leftIdeal)
    (hopposite : G.ideals.secondOpposite.val = W.rightIdeal)
    (hunit : G.ideals.unitPart.val = W.unitIdeal.val)
    (hnonunit : G.ideals.nonunitPart.val = W.nonunitIdeal.val)
    (bindingL : (left.arithmeticCalibration calL W frozenL).OriginalLengthBinding
      parent a step (G.atBase left.source.base hbaseL))
    (bindingR : (right.arithmeticCalibration calR W frozenR).OriginalLengthBinding
      parent a step (G.swapSecond.atBase right.source.base hbaseR))
    (atomsL : (left.arithmeticCalibration calL W frozenL).OriginalCapacityAtoms)
    (atomsR : (right.arithmeticCalibration calR W frozenR).OriginalCapacityAtoms)
    (hstep : 0 < step) (annulus error mesh : ℝ) (herror : 0 < error)
    (hZ : annulusThreshold annulus error ≤ Z)
    (hmesh : 0 ≤ mesh) (hfit : parent.geometry.fitsMesh mesh)
    (hannulusLL : atomsL.leftAnnulus ≤ annulus)
    (hannulusLR : atomsL.rightAnnulus ≤ annulus)
    (hannulusRL : atomsR.leftAnnulus ≤ annulus)
    (hannulusRR : atomsR.rightAnnulus ≤ annulus)
    (hsupport : G.supportError ≤ error)
    (hrawL : bindingL.rawScaleError ≤ error) (hrawR : bindingR.rawScaleError ≤ error)
    (hwidthL : bindingL.scales.error ≤ error) (hwidthR : bindingR.scales.error ≤ error)
    (hdivisor : left.source.allocation.divisor = right.source.allocation.divisor)
    (hscaleL : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ left.normalizationScale)
    (hscaleR : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ right.normalizationScale)
    (hradius : Z ^ (-G.skeleton.Krow - G.skeleton.g) ≤
      W.radius.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) W.mask)).val) :
    OriginalPairAllowanceWindow left right calL calR W frozenL frozenR
      (bindingL.capacityInput hstep mesh hmesh hfit atomsL)
      (bindingR.capacityInput hstep mesh hmesh hfit atomsR) Z
      (firstLeftAllowance Z (G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E))
        G.ideals.first.val G.ideals.opposite.val)
      (G.skeleton.wo + G.tag.poolLength step + 5 * error / 3 + mesh) := by
  let IL := bindingL.capacityInput hstep mesh hmesh hfit atomsL
  let IR := bindingR.capacityInput hstep mesh hmesh hfit atomsR
  have hZ1 : 1 < Z := (annulusThreshold_gt_one annulus error).trans_le hZ
  let LL : ActualCapacityNormLengths IL Z
      (G.skeleton.A - G.skeleton.c - G.skeleton.w)
      (G.skeleton.q + G.skeleton.R + G.skeleton.E)
      G.skeleton.wo G.skeleton.w G.skeleton.Krow G.skeleton.g (G.tag.poolLength step)
      W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val := by
    simpa only [OriginalNominalGeometry.atBase_skeleton, hbaseL,
      hsecond, hopposite, hunit, hnonunit] using
      bindingL.normLengths hstep mesh hmesh hfit atomsL
  let LR : ActualCapacityNormLengths IR Z
      (G.skeleton.A - G.skeleton.c - G.skeleton.w)
      (G.skeleton.q + G.skeleton.R + G.skeleton.E)
      G.skeleton.wo G.skeleton.w G.skeleton.Krow G.skeleton.g (G.tag.poolLength step)
      W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val := by
    simpa only [OriginalNominalGeometry.atBase_skeleton,
      OriginalNominalGeometry.swapSecond_skeleton, hbaseR,
      hsecond, hopposite, hunit, hnonunit] using
      (bindingR.normLengths hstep mesh hmesh hfit atomsR).swap
  have hbL : IL.boundary = G.boundary :=
    G.atBase_boundary left.source.base hbaseL
  have hbR : IR.boundary = G.boundary :=
    (G.swapSecond.atBase_boundary right.source.base hbaseR).trans G.swapSecond_boundary
  have errorsL := bindingL.originalErrorWindows hstep mesh hmesh hfit atomsL annulus error
    hannulusLL hannulusLR hsupport hrawL hwidthL
  have errorsR := bindingR.originalErrorWindows hstep mesh hmesh hfit atomsR annulus error
    hannulusRL hannulusRR hsupport hrawR hwidthR
  have hl := LL.slack_le_of_original_windows annulus error mesh G.boundary
    herror hZ errorsL hbL
  have hr := LR.slack_le_of_original_windows annulus error mesh G.boundary
    herror hZ errorsR hbR
  refine {
    a₀ := G.skeleton.A - G.skeleton.c - G.skeleton.w
    q := G.skeleton.q + G.skeleton.R + G.skeleton.E
    wo := G.skeleton.wo
    w := G.skeleton.w
    krow := G.skeleton.Krow
    g := G.skeleton.g
    ell := G.tag.poolLength step
    boundary := G.boundary
    normalization := ?_
    divisor := hdivisor
    leftLengths := LL
    rightLengths := LR
    leftScale := left.originalScaleWindowOfProduct Z _ hZ1 hscaleL
    rightScale := right.originalScaleWindowOfProduct Z _ hZ1 hscaleR
    radius := hradius
    margin := ?_ }
  · exact firstLeftAllowance_second_exponent Z G.skeleton.A
      (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.w
      G.ideals.first.val G.ideals.opposite.val
  · linarith

end Pair
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.firstActiveRadical_swap_of_support
#print axioms HeckeSkeleton.Moments.EngineStep.firstLeftAllowance_swap_of_support
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.swapSecond_skeleton
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.OriginalLengthBinding.originalErrorWindows
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalPairAllowanceWindow.ofNominalGeometry
