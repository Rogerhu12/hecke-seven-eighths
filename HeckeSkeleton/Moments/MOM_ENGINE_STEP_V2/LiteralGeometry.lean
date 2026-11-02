import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNominalGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralCapacity

set_option linter.unusedSectionVars false

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

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

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
  sorry

theorem firstLeftAllowance_swap_of_support (Z total : ℝ) (D E : Ideal (𝓞 K))
    (h : primeSupport D = primeSupport E) :
    firstLeftAllowance Z total E D = firstRightAllowance Z total D E := by
  sorry

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
  sorry

theorem atBase_boundary (base : ℝ) (hbase : base = Z) :
    (G.atBase base hbase).boundary = G.boundary := by
  sorry

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
  sorry

theorem swapSecond_boundary : G.swapSecond.boundary = G.boundary := rfl

end OriginalNominalGeometry

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

theorem atBase_literalRowParameter (base : ℝ) (hbase : base = Z) (cutoff : ℝ) :
    (G.atBase base hbase).literalRowParameter cutoff = G.literalRowParameter cutoff := by
  sorry

theorem atBase_literalSupportParameter (base : ℝ) (hbase : base = Z) (root : ℝ) :
    (G.atBase base hbase).literalSupportParameter root = G.literalSupportParameter root := by
  sorry

theorem swapSecond_literalRowParameter (cutoff : ℝ) :
    G.swapSecond.literalRowParameter cutoff = G.literalRowParameter cutoff := by
  sorry

theorem swapSecond_literalSupportParameter (root : ℝ) :
    G.swapSecond.literalSupportParameter root = G.literalSupportParameter root := by
  sorry

end OriginalNominalGeometry

end HeckeSkeleton.Moments.EngineStepV2

