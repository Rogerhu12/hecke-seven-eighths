import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralQuotientScales
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActiveProfileKernelMass

set_option linter.unusedSectionVars false
set_option quotPrecheck false

/-!
# The fixed bound on an already computed active literal radius

The original model supplies the actual Fourier plain tests. A nonzero
source then supplies a nonzero ideal summand, so both quotient scales
are at least the inverse original annulus endpoint. The two real
extractions and the allocation have actual nonzero ideal divisors;
their product transfers this lower bound back to the first extracted
scales used in the reciprocal balance.

No raw or clipped child window is an input here. The computed bound
formula is a literal identity, preserved by each table operation. The
result bounds the same coefficient used when constructing the side,
only on the original nonzero carrier.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralFullKappaInput.ComputedProfiles

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {W : d.ProfileData} {window : Set ℝ} {s : Finset (ℕ × ℕ)} {B : ℝ}
variable (T : CanonicalLiteralFullKappaInput.ComputedProfiles W window s B)

@[simp] theorem extract_bound {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    (T.extract b).bound = T.bound := rfl

@[simp] theorem onAtlas_bound {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (atlas : SourceCartesianAtlas columns ideal) (count : k = atlas.slotCount) :
    (T.onAtlas atlas count).bound = T.bound := by
  sorry

@[simp] theorem deleteMask_bound (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (T.deleteMask M).bound = T.bound := rfl

@[simp] theorem reprofile_bound
    {d' : CanonicalLiteralRectangles.Atoms (K := K) k} (W' : d'.ProfileData)
    (hleft : ∀ r u t y, (W'.left r).profile u t y = (W.left r).profile u t y)
    (hright : ∀ r u t y, (W'.right r).profile u t y = (W.right r).profile u t y)
    (hslot : ∀ j t y, (W'.slot j).profile t y = (W.slot j).profile t y) :
    (T.reprofile W' hleft hright hslot).bound = T.bound := rfl

@[simp] theorem extractThenScaleBalance_bound (c : ℂ) (balance : Bool → ℝ)
    (T : CanonicalLiteralFullKappaInput.ComputedProfiles
      ((W.scale c).balancePlain balance) window s B)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    (extractThenScaleBalance c balance T b).bound = T.bound := rfl

@[simp] theorem onAtlasThenScaleBalance_bound (c : ℂ) (balance : Bool → ℝ)
    (T : CanonicalLiteralFullKappaInput.ComputedProfiles
      ((W.scale c).balancePlain balance) window s B)
    {A : SArithmeticData K} {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (atlas : SourceCartesianAtlas columns ideal) (count : k = atlas.slotCount) :
    (onAtlasThenScaleBalance c balance T atlas count).bound = T.bound := by
  sorry

@[simp] theorem deleteMaskThenScaleBalance_bound (c : ℂ) (balance : Bool → ℝ)
    (T : CanonicalLiteralFullKappaInput.ComputedProfiles
      ((W.scale c).balancePlain balance) window s B)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (deleteMaskThenScaleBalance c balance T M).bound = T.bound := rfl

end CanonicalLiteralFullKappaInput.ComputedProfiles

namespace CanonicalLiteralFullKappaInput

@[simp] theorem scalarFreeBalanced_bound
    {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
    {window : Set ℝ} (E : W.SchwartzModel window)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    {A : SArithmeticData K} {σ : K →+* ℂ}
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (s : Finset (ℕ × ℕ)) (B : ℝ) (hB : 0 ≤ B) (hδhi : δ₁ + δ₂ ≤ 1 / 2)
    (hleft : ∀ r, (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders s)).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) ≤ B)
    (hright : ∀ r, (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders s)).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) ≤ B)
    (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders s)).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ B)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ Set.Ioo (1 : ℝ) 2) :
    (scalarFreeBalanced (σ := σ) E b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive
      s B hB hδhi hleft hright hslot hprime).bound = fun r =>
        B + B * CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
          (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders s) *
            (1 + CanonicalLiteralBalancedSchwartz.factor d b δ₁ δ₂ r) := rfl

end CanonicalLiteralFullKappaInput

namespace CanonicalLiteralActiveRadius

variable {ω ψ : HeckeCharacter K}

/-- Only the actual two plain tests are used. The inverse test, row
set and other atoms retain their original values. -/
theorem scale_and_clipping_bounds
    {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k} (W : d.ProfileData)
    {lo hi : ℝ} (E : W.SchwartzModel (Set.Icc lo hi))
    (hlo : 0 < lo) (hhi : 1 ≤ hi) (firstSign : ℝ) (negative : Bool) (r : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (child : MomentData K ω ψ) (parameters : RealParameters)
    (Z time : ℝ) (hZ : 1 < Z)
    (hleft : child.plainTest₁ = W.fourierLeft r firstSign negative ξ)
    (hright : child.plainTest₂ = W.fourierRight r firstSign negative ξ)
    (hne : pairedEnergy child parameters Z time ≠ 0) :
    (1 / hi ≤ Z ^ parameters.n₁ ∧ 1 / hi ≤ Z ^ parameters.n₂) ∧
      (plainClippingFactor Z parameters.n₁ ≤ hi ∧
        plainClippingFactor Z parameters.n₂ ≤ hi) := by
  sorry

theorem fixedCoefficient_nonneg (B lo hi : ℝ) (hB : 0 ≤ B)
    (hlo : 0 < lo) (hhi : 1 ≤ hi) (δ₁ δ₂ firstSign : ℝ)
    (s : Finset (ℕ × ℕ)) :
    0 ≤ CanonicalLiteralRadiusBound.fixedCoefficient B lo hi hlo δ₁ δ₂ firstSign s := by
  sorry

/-- Only the two fixed first-source signs are combined. The maximum
is independent of every moving source, label and Fourier variable. -/
def twoSignsCoefficient (B lo hi : ℝ) (hlo : 0 < lo) (δ₁ δ₂ : ℝ)
    (s : Finset (ℕ × ℕ)) : ℝ :=
  max (CanonicalLiteralRadiusBound.fixedCoefficient B lo hi hlo δ₁ δ₂ 1 s)
    (CanonicalLiteralRadiusBound.fixedCoefficient B lo hi hlo δ₁ δ₂ (-1) s)

theorem twoSignsCoefficient_nonneg (B lo hi : ℝ) (hB : 0 ≤ B)
    (hlo : 0 < lo) (hhi : 1 ≤ hi) (δ₁ δ₂ : ℝ) (s : Finset (ℕ × ℕ)) :
    0 ≤ twoSignsCoefficient B lo hi hlo δ₁ δ₂ s := by
  sorry

theorem fixedCoefficient_le_twoSigns (B lo hi : ℝ) (hlo : 0 < lo)
    (δ₁ δ₂ firstSign : ℝ) (s : Finset (ℕ × ℕ))
    (hfirstSign : firstSign = 1 ∨ firstSign = -1) :
    CanonicalLiteralRadiusBound.fixedCoefficient B lo hi hlo δ₁ δ₂ firstSign s ≤
      twoSignsCoefficient B lo hi hlo δ₁ δ₂ s := by
  sorry

section ActualTable

variable {k n : ℕ} (original : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {firstSupport : Finset (Ideal (𝓞 K))}
variable (first : SupportCartesianBranch original.plain₁ original.plain₂ original.slots firstSupport)
variable (beforeSecond : CanonicalLiteralRectangles.Atoms (K := K) n)
variable {secondSupport : Finset (Ideal (𝓞 K))}
variable (second : SupportCartesianBranch beforeSecond.plain₁ beforeSecond.plain₂
  beforeSecond.slots secondSupport)
variable {A : SArithmeticData K} {ι : Type*}
variable {columns : Finset ι} {ideal : ι → A.Exterior}
variable (atlas : SourceCartesianAtlas columns ideal) (count : second.keep.card = atlas.slotCount)
variable (scalar : ℂ) (balance : Bool → ℝ)
variable (W : ((((beforeSecond.extract second).onAtlas atlas count).scale scalar).balancePlain balance).ProfileData)
variable (allocation : ActualColumnAllocation K atlas.slotCount)
variable {lo hi B : ℝ} {s : Finset (ℕ × ℕ)}
variable (T : CanonicalLiteralFullKappaInput.ComputedProfiles W (Set.Icc lo hi) s B)

local notation "actualTable" =>
  (((beforeSecond.extract second).onAtlas atlas count).scale scalar).balancePlain balance

/-- The identity of `bound` is obtained by unfolding the original
constructor; the preceding simp lemmas preserve it along all actual
table transports. The scale identities concern the original first
extraction, not a completed child estimate. -/
theorem coefficient_le_fixed_of_nonzero
    (r : Bool) (m q κ δ₁ δ₂ firstSign : ℝ) (negative : Bool)
    (hB : 0 ≤ B) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (hδlo : 0 ≤ δ₁ + δ₂) (hδhi : δ₁ + δ₂ ≤ 1 / 2)
    (hproduct : original.scale₁ r * original.scale₂ r =
      original.scale₁ false * original.scale₂ false)
    (hbase : beforeSecond.base = original.base)
    (hfirst₁ : beforeSecond.scale₁ r = (original.extract first).scale₁ r)
    (hfirst₂ : beforeSecond.scale₂ r = (original.extract first).scale₂ r)
    (hbound : T.bound r = B + B *
      CanonicalLiteralRadiusBound.shapeCoefficient lo hi hlo δ₁ δ₂ s *
        (1 + CanonicalLiteralBalancedSchwartz.factor original first δ₁ δ₂ r))
    (ξ : WithLp 2 (ℝ × ℝ)) (child : MomentData K ω ψ) (time : ℝ)
    (hleft : child.plainTest₁ = W.fourierLeft r firstSign negative ξ)
    (hright : child.plainTest₂ = W.fourierRight r firstSign negative ξ)
    (hne : pairedEnergy child
      (CanonicalLiteralAllocatedData.parameters actualTable allocation r m q κ)
      original.base time ≠ 0) :
    T.coefficient original.base
      (CanonicalLiteralAllocatedData.parameters actualTable allocation r m q κ)
      isCompact_Icc (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign r ≤
        CanonicalLiteralRadiusBound.fixedCoefficient B lo hi hlo δ₁ δ₂ firstSign s := by
  sorry

/-- Source activity is the exact predicate used by the normalized
family. The genuine raw nonzero member is derived from its calibration,
so the final caller supplies no child-energy premise. -/
theorem coefficient_le_fixed_of_source_active
    (r : Bool) (m q κ δ₁ δ₂ firstSign : ℝ) (negative : Bool)
    (hB : 0 ≤ B) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (hδlo : 0 ≤ δ₁ + δ₂) (hδhi : δ₁ + δ₂ ≤ 1 / 2)
    (hproduct : original.scale₁ r * original.scale₂ r =
      original.scale₁ false * original.scale₂ false)
    (hbase : beforeSecond.base = original.base)
    (hfirst₁ : beforeSecond.scale₁ r = (original.extract first).scale₁ r)
    (hfirst₂ : beforeSecond.scale₂ r = (original.extract first).scale₂ r)
    (hbound : T.bound r = B + B *
      CanonicalLiteralRadiusBound.shapeCoefficient lo hi hlo δ₁ δ₂ s *
        (1 + CanonicalLiteralBalancedSchwartz.factor original first δ₁ δ₂ r))
    {H : Type*} {sourceSlots : ℕ} {σ : K →+* ℂ}
    (source : ActualAllocatedSource A (WithLp 2 (ℝ × ℝ)) H sourceSlots)
    (D : source.Calibration (σ := σ) ω ψ)
    (hsourceBase : source.base = original.base)
    (hparameters : D.parameters =
      CanonicalLiteralAllocatedData.parameters actualTable allocation r m q κ)
    (hleft : ∀ ξ, (D.data ξ).plainTest₁ = W.fourierLeft r firstSign negative ξ)
    (hright : ∀ ξ, (D.data ξ).plainTest₂ = W.fourierRight r firstSign negative ξ)
    (hactive : ¬∀ ξ, source.energy (σ := σ) ξ = 0) :
    T.coefficient source.base D.parameters isCompact_Icc
      (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign r ≤
        CanonicalLiteralRadiusBound.fixedCoefficient B lo hi hlo δ₁ δ₂ firstSign s := by
  sorry

end ActualTable
end CanonicalLiteralActiveRadius
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralActiveRadius.scale_and_clipping_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralActiveRadius.fixedCoefficient_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralActiveRadius.coefficient_le_fixed_of_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralActiveRadius.coefficient_le_fixed_of_source_active
