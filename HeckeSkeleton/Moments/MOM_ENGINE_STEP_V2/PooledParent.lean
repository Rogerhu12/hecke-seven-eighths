import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PooledFirstLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafSupport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original parent reaches its actual finite live two-transform leaves

The dependent finite carrier keeps every original first common label,
mask divisor, internal divisor and phase, side, pool main/error prime
and valuation, second common label and mask, both cover and occurrence
keys, row label, second Möbius divisor, phase and both allocations.
Zero weights and identically zero whole columns are removed by proved
identities.  All remaining leaves retain the original two fixed kernels
and their actual common positive Fourier measure.

The displayed first-zero, second-zero and tail budgets are the exact
previous terminal budgets, not new assumptions on an aggregate source.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

/-- The actual original first labels precede all previously constructed
finite labels of both pool sides. -/
abbrev CoveredLeafKey :=
  Σ v : s.CommonLabel, Σ D : ((s.block v).mask s.mask).powerset,
    (R v D).CoveredLeafKey L L

def coveredLeaf (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.CoveredLeafKey L) : ActualHybridLeaf K Q W E :=
  (R j.1 j.2.1).coveredLeaf L L (N.left j.1 j.2.1) (N.right j.1 j.2.1)
    (N.left_pos j.1 j.2.1) (N.right_pos j.1 j.2.1)
    (exceptional j.1 j.2.1) j.2.2

def parentLeaf (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.CoveredLeafKey L) : ActualHybridLeaf K Q W E :=
  (R.coveredLeaf L exceptional N j).scale (s.fiber : ℝ) (Nat.cast_nonneg _)

def liveLeaves (exceptional : R.CoverHybridPredicates L) (N : s.Normalization) :
    Finset (R.CoveredLeafKey L) :=
  ActualHybridFamily.live (R.parentLeaf L exceptional N)

theorem liveLeaves_spec (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) :
    (R.parentLeaf L exceptional N j.val).Live :=
  ActualHybridFamily.live_spec _ j

/-- A retained label's first internal divisor is squarefree because
the actual original Möbius weight is nonzero, not because the divisor
pool was assumed squarefree. -/
theorem live_first_divisor_squarefree
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) : Squarefree j.val.2.2.1.val := by
  have hw := (R.liveLeaves_spec L exceptional N j).1
  change (s.fiber : ℝ) * (R.coveredLeaf L exceptional N j.val).weight ≠ 0 at hw
  exact (R j.val.1 j.val.2.1).coveredLeaf_weight_nonzero_squarefree L L
    (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
    (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
    (exceptional j.val.1 j.val.2.1) j.val.2.2 (mul_ne_zero_iff.mp hw).2

end ActualFirstSource.SecondStages
end HeckeSkeleton.Moments.EngineStepV2

