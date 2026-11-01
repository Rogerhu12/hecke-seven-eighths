import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPaidSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRawWindows

/-!
# An internal annulus containing the original profile support

The public box only requires a positive lower endpoint and an upper
endpoint at least one. Enlarging the latter to the maximum with the
inverse lower endpoint supplies the symmetric annular inequality used
by the literal exceptional estimates. All numerical lengths, losses,
cutoff exponents and logarithmic tilts retain their original values.

The original volume primitive is uniform over every Schwartz test, so
its density, remainder and volume estimate are reused verbatim on the
larger compact positive window. The original raw representatives are
also retained; only their support-inclusion proofs are enlarged.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open CanonicalPrimitiveEngineChoices

namespace CanonicalPrimitiveEngineAnnulus

/-- Only the upper endpoint is enlarged. All original fixed parameters
and their positivity certificates are retained. -/
def annularBox (b : Box) : Box :=
  { b with
    hi := max b.hi b.lo⁻¹
    hi_ge_one := b.hi_ge_one.trans (le_max_left _ _) }

@[simp] theorem annularBox_cap (b : Box) : (annularBox b).cap = b.cap := rfl
@[simp] theorem annularBox_widthMax (b : Box) : (annularBox b).widthMax = b.widthMax := rfl
@[simp] theorem annularBox_paddingMax (b : Box) : (annularBox b).paddingMax = b.paddingMax := rfl
@[simp] theorem annularBox_lo (b : Box) : (annularBox b).lo = b.lo := rfl
@[simp] theorem annularBox_hi (b : Box) : (annularBox b).hi = max b.hi b.lo⁻¹ := rfl
@[simp] theorem annularBox_step (b : Box) : (annularBox b).step = b.step := rfl
@[simp] theorem annularBox_ε (b : Box) : (annularBox b).ε = b.ε := rfl

@[simp] theorem annularBox_lengthBound (b : Box) :
    (annularBox b).lengthBound = b.lengthBound := rfl
@[simp] theorem annularBox_columnBound (b : Box) :
    (annularBox b).columnBound = b.columnBound := rfl
@[simp] theorem annularBox_normBound (b : Box) :
    (annularBox b).normBound = b.normBound := rfl
@[simp] theorem annularBox_loss (b : Box) : (annularBox b).loss = b.loss := rfl
@[simp] theorem annularBox_error (b : Box) : (annularBox b).error = b.error := rfl
@[simp] theorem annularBox_tilt (b : Box) : (annularBox b).tilt = b.tilt := rfl
@[simp] theorem annularBox_saving (b : Box) : (annularBox b).saving = b.saving := rfl
@[simp] theorem annularBox_firstDegree (b : Box) :
    (annularBox b).firstDegree = b.firstDegree := rfl
@[simp] theorem annularBox_secondDegree (b : Box) :
    (annularBox b).secondDegree = b.secondDegree := rfl
@[simp] theorem annularBox_firstDecay (b : Box) :
    (annularBox b).firstDecay = b.firstDecay := rfl
@[simp] theorem annularBox_secondDecay (b : Box) :
    (annularBox b).secondDecay = b.secondDecay := rfl
@[simp] theorem annularBox_firstCutoffExponent (b : Box) :
    (annularBox b).firstBox.cutoffExponent = b.firstBox.cutoffExponent := rfl
@[simp] theorem annularBox_firstCutoff (b : Box) (Z : ℝ) :
    (annularBox b).firstBox.cutoff Z = b.firstBox.cutoff Z := rfl
@[simp] theorem annularBox_secondCutoff (b : Box) (Z : ℝ) :
    (annularBox b).secondCutoff Z = b.secondCutoff Z := rfl
@[simp] theorem annularBox_rawNormBound (b : Box) :
    (annularBox b).rawNormBound = b.rawNormBound := rfl
@[simp] theorem annularBox_rowBound (b : Box) :
    (annularBox b).rowBound = b.rowBound := rfl

theorem hi_le_annularBox (b : Box) : b.hi ≤ (annularBox b).hi := le_max_left _ _

theorem inverse_lo_le_hi (b : Box) : (annularBox b).lo⁻¹ ≤ (annularBox b).hi :=
  le_max_right _ _

/-- The extra inequality is proved for the internal box; it is not a
new condition on the public original annulus. -/
theorem inverse_hi_le_lo (b : Box) : (annularBox b).hi⁻¹ ≤ (annularBox b).lo := by
  change (max b.hi b.lo⁻¹)⁻¹ ≤ b.lo
  simpa only [one_div, inv_inv] using
    one_div_le_one_div_of_le (inv_pos.mpr b.lo_pos) (le_max_right b.hi b.lo⁻¹)

theorem window_subset (b : Box) :
    Set.Icc b.lo b.hi ⊆ Set.Icc (annularBox b).lo (annularBox b).hi := by
  intro x hx
  exact ⟨hx.1, hx.2.trans (hi_le_annularBox b)⟩

theorem window_positive (b : Box) :
    Set.Icc (annularBox b).lo (annularBox b).hi ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  exact b.lo_pos.trans_le hx.1

end CanonicalPrimitiveEngineAnnulus

namespace CanonicalLiteralExceptionalPaidSource.VolumePrimitive

variable {K : Type} [Field K] [NumberField K]
variable {ψ : HeckeCharacter K} {theta : Finset (HeckeCharacter K)}
variable {window window' : Set ℝ}

/-- The original series estimate is global in its Schwartz test. A new
compact positive window only replaces these two window certificates. -/
def rewindow (primitive : CanonicalLiteralExceptionalPaidSource.VolumePrimitive ψ theta window)
    (hcompact : IsCompact window') (hpositive : window' ⊆ Set.Ioi (0 : ℝ)) :
    CanonicalLiteralExceptionalPaidSource.VolumePrimitive ψ theta window' where
  compact := hcompact
  positive := hpositive
  density := primitive.density
  remainder := primitive.remainder
  continuous := primitive.continuous
  volume := primitive.volume

@[simp] theorem rewindow_density
    (primitive : CanonicalLiteralExceptionalPaidSource.VolumePrimitive ψ theta window)
    (hcompact : IsCompact window') (hpositive : window' ⊆ Set.Ioi (0 : ℝ)) :
    (primitive.rewindow hcompact hpositive).density = primitive.density := rfl

@[simp] theorem rewindow_remainder
    (primitive : CanonicalLiteralExceptionalPaidSource.VolumePrimitive ψ theta window)
    (hcompact : IsCompact window') (hpositive : window' ⊆ Set.Ioi (0 : ℝ)) :
    (primitive.rewindow hcompact hpositive).remainder = primitive.remainder := rfl

end CanonicalLiteralExceptionalPaidSource.VolumePrimitive

namespace CanonicalPrimitiveEngineAnnulus

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K} {theta : Finset (HeckeCharacter K)}

/-- The same original density and remainder on the internal annulus.
All later seminorm orders are selected from this transported primitive. -/
def volumePrimitive (b : Box)
    (primitive : CanonicalLiteralExceptionalPaidSource.VolumePrimitive
      ψ theta (Set.Icc b.lo b.hi)) :
    CanonicalLiteralExceptionalPaidSource.VolumePrimitive
      ψ theta (Set.Icc (annularBox b).lo (annularBox b).hi) :=
  primitive.rewindow isCompact_Icc (window_positive b)

@[simp] theorem volumePrimitive_density (b : Box)
    (primitive : CanonicalLiteralExceptionalPaidSource.VolumePrimitive
      ψ theta (Set.Icc b.lo b.hi)) :
    (volumePrimitive b primitive).density = primitive.density := rfl

@[simp] theorem volumePrimitive_remainder (b : Box)
    (primitive : CanonicalLiteralExceptionalPaidSource.VolumePrimitive
      ψ theta (Set.Icc b.lo b.hi)) :
    (volumePrimitive b primitive).remainder = primitive.remainder := rfl

variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain : Set ℝ} {orders : Finset (ℕ × ℕ)}
variable {d : MomentData K ω ψ} {bound : ℝ}

/-- Enlarge support certificates while retaining all four actual
Schwartz representatives and their original seminorm bounds. -/
def rawWindow (b : Box)
    (profiles : RawProfileWindow rowDomain heightDomain (Set.Icc b.lo b.hi) orders d bound) :
    RawProfileWindow rowDomain heightDomain
      (Set.Icc (annularBox b).lo (annularBox b).hi) orders d bound :=
  CanonicalLiteralFourierWindows.enlargeWindow profiles (window_subset b)

@[simp] theorem rawWindow_inverseRep (b : Box)
    (profiles : RawProfileWindow rowDomain heightDomain (Set.Icc b.lo b.hi) orders d bound) :
    (rawWindow b profiles).inverseRep = profiles.inverseRep := rfl

@[simp] theorem rawWindow_leftRep (b : Box)
    (profiles : RawProfileWindow rowDomain heightDomain (Set.Icc b.lo b.hi) orders d bound) :
    (rawWindow b profiles).leftRep = profiles.leftRep := rfl

@[simp] theorem rawWindow_rightRep (b : Box)
    (profiles : RawProfileWindow rowDomain heightDomain (Set.Icc b.lo b.hi) orders d bound) :
    (rawWindow b profiles).rightRep = profiles.rightRep := rfl

@[simp] theorem rawWindow_primeRep (b : Box)
    (profiles : RawProfileWindow rowDomain heightDomain (Set.Icc b.lo b.hi) orders d bound) :
    (rawWindow b profiles).primeRep = profiles.primeRep := rfl

@[simp] theorem rawWindow_prime_support (b : Box)
    (profiles : RawProfileWindow rowDomain heightDomain (Set.Icc b.lo b.hi) orders d bound)
    (i : Fin d.geometry.slotCount) (t : ℝ) :
    Function.support ((rawWindow b profiles).primeRep i t) =
      Function.support (profiles.primeRep i t) := rfl

end CanonicalPrimitiveEngineAnnulus
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineAnnulus.inverse_hi_le_lo
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidSource.VolumePrimitive.rewindow
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineAnnulus.volumePrimitive
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineAnnulus.rawWindow
