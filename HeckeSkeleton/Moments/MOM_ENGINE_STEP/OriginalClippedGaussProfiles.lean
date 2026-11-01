import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalGaussProfileCompensation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSignedProfileBudget

/-!
# Bounded original Gauss compensation, including empty comparisons

The actual compensation scalar can be large at an arbitrarily short
comparison length. At such a length the original positive annulus has
no nonzero ideal point. Capping the positive scalar at the fixed square
root of the annular endpoint therefore preserves every original ideal
coefficient, including the empty comparison, without a nonempty-source
hypothesis.

The cap is installed in the literal profile data by `ProfileScalars`.
The remaining multiplier has scale one and the fixed signed exponent
`δ₁ + δ₂ - 1`. Its offset retains both original logarithmic phases.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.OriginalClippedGaussProfiles

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open CanonicalLogProfiles OriginalGaussProfileCompensation

/-- A positive coefficient, fixed before the Fourier parameter. -/
def clippedScalar (G D B δ₁ δ₂ : ℝ) : ℝ :=
  min (scalar G D δ₁ δ₂) (Real.sqrt B)

theorem clippedScalar_pos (G D B δ₁ δ₂ : ℝ)
    (hG : 0 < G) (hD : 0 < D) (hB : 1 ≤ B) :
    0 < clippedScalar G D B δ₁ δ₂ :=
  lt_min (scalar_pos G D δ₁ δ₂ hG hD)
    (Real.sqrt_pos.mpr (zero_lt_one.trans_le hB))

theorem clippedScalar_le (G D B δ₁ δ₂ : ℝ) :
    clippedScalar G D B δ₁ δ₂ ≤ Real.sqrt B := min_le_right _ _

theorem sqrt_annulus_one_le {B : ℝ} (hB : 1 ≤ B) : 1 ≤ Real.sqrt B := by
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hB

/-- The clipping is exact at every nonzero ideal norm. If the
unclipped coefficient exceeds the cap, the original profile value at
this length is forced to vanish by its own support window. -/
theorem clippedScalar_profile_eq
    (G D N B δ₁ δ₂ : ℝ) (hG : 0 < G) (hD : 1 ≤ D) (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (W : ℝ → ℂ) (hW : ∀ y, W y ≠ 0 → y ≤ B) :
    (clippedScalar G D B δ₁ δ₂ : ℂ) * W (N / G) =
      (scalar G D δ₁ δ₂ : ℂ) * W (N / G) := by
  by_cases hw : W (N / G) = 0
  · simp only [hw, mul_zero]
  · rw [clippedScalar, min_eq_left
      (scalar_le_sqrt_annulus G D N B δ₁ δ₂ hG hD hN hB
        (hW _ hw) hδ₁ hδ₂ hδ)]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- This is the literal original profile times both norm powers and
both Fourier phases. The bounded replacement changes no ideal point. -/
theorem clipped_multiplier_identity
    (G D N B δ₁ δ₂ : ℝ) (hG : 0 < G) (hD : 1 ≤ D) (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (W : ℝ → ℂ) (hW : ∀ y, W y ≠ 0 → y ≤ B)
    (firstDirection secondDirection ξ : V) :
    W (N / G) *
        ((Real.sqrt G * (D * N) ^ (δ₁ - 1) * N ^ δ₂ : ℝ) : ℂ) *
        jointPhase ξ (Real.log (D * N) • firstDirection + Real.log N • secondDirection) =
      ((clippedScalar G D B δ₁ δ₂ : ℂ) * W (N / G)) *
        (atom G D δ₁ δ₂ firstDirection secondDirection).multiplier ξ (N / G) := by
  have hm := multiplier_identity G D N δ₁ δ₂ hG (zero_lt_one.trans_le hD)
    (zero_lt_one.trans_le hN) firstDirection secondDirection ξ
  have hc := clippedScalar_profile_eq G D N B δ₁ δ₂ hG hD hN hB hδ₁ hδ₂ hδ W hW
  calc
    _ = W (N / G) *
        ((((Real.sqrt G * (D * N) ^ (δ₁ - 1) * N ^ δ₂ : ℝ) : ℂ)) *
          jointPhase ξ (Real.log (D * N) • firstDirection + Real.log N • secondDirection)) := by ring
    _ = ((scalar G D δ₁ δ₂ : ℂ) * W (N / G)) *
        (atom G D δ₁ δ₂ firstDirection secondDirection).multiplier ξ (N / G) := by rw [hm]; ring
    _ = _ := by rw [hc]

section OriginalProfiles

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable (d : MomentData K ω ψ)
variable (G₁ G₂ : ℝ) (G : Fin d.geometry.slotCount → ℝ)
variable (D₁ D₂ : NonzeroIdeal K) (B δ₁ δ₂ : ℝ)
variable (hG₁ : 0 < G₁) (hG₂ : 0 < G₂) (hG : ∀ i, 0 < G i) (hB : 1 ≤ B)

/-- The actual plain extractions and actual retained prime scales
construct one bounded positive scalar per original occurrence. -/
def profileScalars : ProfileScalars d.geometry.slotCount where
  left := clippedScalar G₁ (idealNorm K D₁) B δ₁ δ₂
  right := clippedScalar G₂ (idealNorm K D₂) B δ₁ δ₂
  prime i := clippedScalar (G i) 1 B δ₁ δ₂
  left_pos := clippedScalar_pos G₁ (idealNorm K D₁) B δ₁ δ₂ hG₁ (idealNorm_pos K D₁) hB
  right_pos := clippedScalar_pos G₂ (idealNorm K D₂) B δ₁ δ₂ hG₂ (idealNorm_pos K D₂) hB
  prime_pos i := clippedScalar_pos (G i) 1 B δ₁ δ₂ (hG i) zero_lt_one hB

local notation "scalars" => profileScalars d G₁ G₂ G D₁ D₂ B δ₁ δ₂ hG₁ hG₂ hG hB

theorem profileScalars_left_le : (scalars).left ≤ Real.sqrt B := min_le_right _ _
theorem profileScalars_right_le : (scalars).right ≤ Real.sqrt B := min_le_right _ _
theorem profileScalars_prime_le (i : Fin d.geometry.slotCount) :
    (scalars).prime i ≤ Real.sqrt B := min_le_right _ _

variable {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {P : ℝ}
variable (w : RawProfileWindow rowDomain heightDomain window orders d P)
variable (hwindow : window ⊆ Set.Iic B)
variable (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
variable (firstDirection secondDirection ξ : V)

/-- The left identity consumes the original profile window itself.
No bound for a moving compensated profile is supplied. -/
include w hwindow hδ₁ hδ₂ hδ in
theorem original_left_identity (u : NonzeroIdeal K) (hu : u ∈ rowDomain)
    (t : ℝ) (ht : t ∈ heightDomain) (I : NonzeroIdeal K) :
    d.plainTest₁.profile u t (idealNorm K I / G₁) *
        ((Real.sqrt G₁ * (idealNorm K D₁ * idealNorm K I) ^ (δ₁ - 1) *
          idealNorm K I ^ δ₂ : ℝ) : ℂ) *
        jointPhase ξ
          (Real.log (idealNorm K D₁ * idealNorm K I) • firstDirection +
            Real.log (idealNorm K I) • secondDirection) =
      (((scalars).left : ℂ) * d.plainTest₁.profile u t (idealNorm K I / G₁)) *
        (atom G₁ (idealNorm K D₁) δ₁ δ₂ firstDirection secondDirection).multiplier ξ (idealNorm K I / G₁) := by
  apply clipped_multiplier_identity G₁ (idealNorm K D₁) (idealNorm K I) B δ₁ δ₂
    hG₁ (one_le_idealNorm K D₁) (one_le_idealNorm K I) hB hδ₁ hδ₂ hδ
    (d.plainTest₁.profile u t)
  intro y hy
  apply hwindow
  apply w.left_support u hu t ht
  simpa only [w.left_eq] using hy

include w hwindow hδ₁ hδ₂ hδ in
theorem original_right_identity (u : NonzeroIdeal K) (hu : u ∈ rowDomain)
    (t : ℝ) (ht : t ∈ heightDomain) (I : NonzeroIdeal K) :
    d.plainTest₂.profile u t (idealNorm K I / G₂) *
        ((Real.sqrt G₂ * (idealNorm K D₂ * idealNorm K I) ^ (δ₁ - 1) *
          idealNorm K I ^ δ₂ : ℝ) : ℂ) *
        jointPhase ξ
          (Real.log (idealNorm K D₂ * idealNorm K I) • firstDirection +
            Real.log (idealNorm K I) • secondDirection) =
      (((scalars).right : ℂ) * d.plainTest₂.profile u t (idealNorm K I / G₂)) *
        (atom G₂ (idealNorm K D₂) δ₁ δ₂ firstDirection secondDirection).multiplier ξ (idealNorm K I / G₂) := by
  apply clipped_multiplier_identity G₂ (idealNorm K D₂) (idealNorm K I) B δ₁ δ₂
    hG₂ (one_le_idealNorm K D₂) (one_le_idealNorm K I) hB hδ₁ hδ₂ hδ
    (d.plainTest₂.profile u t)
  intro y hy
  apply hwindow
  apply w.right_support u hu t ht
  simpa only [w.right_eq] using hy

/-- A retained original prime has no new plain extraction factor.
The prime norm lower bound is the original nonzero-ideal bound. -/
include w hwindow hδ₁ hδ₂ hδ in
theorem original_prime_identity (i : Fin d.geometry.slotCount)
    (t : ℝ) (ht : t ∈ heightDomain) (q : HeightOneSpectrum (𝓞 K)) :
    (d.geometry.slots i).profile t ((Ideal.absNorm q.asIdeal : ℝ) / G i) *
        ((Real.sqrt (G i) * (1 * (Ideal.absNorm q.asIdeal : ℝ)) ^ (δ₁ - 1) *
          (Ideal.absNorm q.asIdeal : ℝ) ^ δ₂ : ℝ) : ℂ) *
        jointPhase ξ
          (Real.log (1 * (Ideal.absNorm q.asIdeal : ℝ)) • firstDirection +
            Real.log (Ideal.absNorm q.asIdeal : ℝ) • secondDirection) =
      (((scalars).prime i : ℂ) *
        (d.geometry.slots i).profile t ((Ideal.absNorm q.asIdeal : ℝ) / G i)) *
        (atom (G i) 1 δ₁ δ₂ firstDirection secondDirection).multiplier ξ ((Ideal.absNorm q.asIdeal : ℝ) / G i) := by
  have hN : (1 : ℝ) ≤ (Ideal.absNorm q.asIdeal : ℝ) :=
    one_le_idealNorm K ⟨q.asIdeal, mem_nonZeroDivisors_of_ne_zero q.ne_bot⟩
  apply clipped_multiplier_identity (G i) 1 (Ideal.absNorm q.asIdeal : ℝ) B δ₁ δ₂
    (hG i) le_rfl hN hB hδ₁ hδ₂ hδ ((d.geometry.slots i).profile t)
  intro y hy
  apply hwindow
  apply w.prime_support i t ht
  simpa only [w.prime_eq] using hy

end OriginalProfiles

section BoundedData

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable (d : MomentData K ω ψ)
variable (G₁ G₂ : ℝ) (G : Fin d.geometry.slotCount → ℝ)
variable (D₁ D₂ : NonzeroIdeal K) (B δ₁ δ₂ : ℝ)
variable (hG₁ : 0 < G₁) (hG₂ : 0 < G₂) (hG : ∀ i, 0 < G i) (hB : 1 ≤ B)
variable (hleft : PositivePlainProfile d.plainTest₁)
variable (hright : PositivePlainProfile d.plainTest₂)
variable (hslot : ∀ i, PositivePrimeProfile (d.geometry.slots i))
variable (firstDirection secondDirection : V)

local notation "scalars" => profileScalars d G₁ G₂ G D₁ D₂ B δ₁ δ₂ hG₁ hG₂ hG hB
local notation "leftAtom" => atom G₁ (idealNorm K D₁) δ₁ δ₂ firstDirection secondDirection
local notation "rightAtom" => atom G₂ (idealNorm K D₂) δ₁ δ₂ firstDirection secondDirection
local notation "slotAtom" => fun i => atom (G i) 1 δ₁ δ₂ firstDirection secondDirection

/-- The bounded child profiles are actual data, with every original
arithmetic field and every original slot length retained literally. -/
def clippedData (ξ : V) : MomentData K ω ψ :=
  CanonicalLogProfiles.data ((scalars).data d) leftAtom rightAtom slotAtom
    ((scalars).left_positive d hleft) ((scalars).right_positive d hright)
    ((scalars).prime_positive d hslot) ξ

local notation "boundedData" => clippedData d G₁ G₂ G D₁ D₂ B δ₁ δ₂ hG₁ hG₂ hG hB
  hleft hright hslot firstDirection secondDirection

@[simp] theorem clippedData_left (ξ : V) (u : NonzeroIdeal K) (t y : ℝ) :
    (boundedData ξ).plainTest₁.profile u t y =
      (((scalars).left : ℂ) * d.plainTest₁.profile u t y) * (leftAtom).multiplier ξ y := rfl

@[simp] theorem clippedData_right (ξ : V) (u : NonzeroIdeal K) (t y : ℝ) :
    (boundedData ξ).plainTest₂.profile u t y =
      (((scalars).right : ℂ) * d.plainTest₂.profile u t y) * (rightAtom).multiplier ξ y := rfl

@[simp] theorem clippedData_prime (ξ : V) (i : Fin d.geometry.slotCount) (t y : ℝ) :
    ((boundedData ξ).geometry.slots i).profile t y =
      (((scalars).prime i : ℂ) * (d.geometry.slots i).profile t y) *
        (slotAtom i).multiplier ξ y := rfl

@[simp] theorem clippedData_rows (ξ : V) (a : RealParameters) (Z : ℝ) :
    pairedRows (boundedData ξ) a Z = pairedRows d a Z := rfl

@[simp] theorem clippedData_slot_length (ξ : V) (i : Fin d.geometry.slotCount) :
    ((boundedData ξ).geometry.slots i).length = (d.geometry.slots i).length := rfl

/-- Norm dependence is constructed from the original norm recipe;
no second recipe for the moving profiles is requested. -/
def normProfiles (W : NormProfileRecipe (fun _ : PUnit => d)) :
    NormProfileRecipe boundedData where
  left ξ t y := (((scalars).left : ℂ) * W.left PUnit.unit t y) * (leftAtom).multiplier ξ y
  right ξ t y := (((scalars).right : ℂ) * W.right PUnit.unit t y) * (rightAtom).multiplier ξ y
  left_eq ξ u hu t y := by
    change (((scalars).left : ℂ) * d.plainTest₁.profile u t y) * (leftAtom).multiplier ξ y = _
    rw [W.left_eq PUnit.unit u hu t y]
  right_eq ξ u hu t y := by
    change (((scalars).right : ℂ) * d.plainTest₂.profile u t y) * (rightAtom).multiplier ξ y = _
    rw [W.right_eq PUnit.unit u hu t y]

/-- The true signed profile window is produced from the original
finite seminorm control. Its amplitude has no moving scale or label
dependence. Only the fixed number of tilt copies enters the palette. -/
def rawWindow
    {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (orders : Finset (ℕ × ℕ)) (δ : ℝ) (R j cap : ℕ) (P : ℝ)
    (hP : 0 ≤ P) (hcount : d.geometry.slotCount ≤ cap)
    (hj : j ≤ R) (hexponent : δ₁ + δ₂ = (j : ℝ) * δ)
    (w : RawProfileWindow rowDomain heightDomain window (sourceOrders orders) d P)
    (hleftSupport : ∀ u t, tsupport (w.leftRep u t) ⊆ window)
    (hrightSupport : ∀ u t, tsupport (w.rightRep u t) ⊆ window)
    (hslotSupport : ∀ i t, tsupport (w.primeRep i t) ⊆ window) (ξ : V) :
    RawProfileWindow rowDomain heightDomain window orders (boundedData ξ)
      (signedAmplitudeConstant window hcompact hpositive orders δ R cap
          (‖firstDirection‖ + ‖secondDirection‖) *
        Real.sqrt B * P * (1 + ‖ξ‖) ^ (orders.sup Prod.snd)) := by
  have he : δ₁ + δ₂ - 1 ∈ shiftedExponentPalette δ R := by
    rw [hexponent]
    exact mem_shiftedExponentPalette δ R j hj
  exact signedRawWindow d scalars leftAtom rightAtom slotAtom hleft hright hslot
    hcompact hpositive orders δ R cap (‖firstDirection‖ + ‖secondDirection‖)
    (Real.sqrt B) P (add_nonneg (norm_nonneg _) (norm_nonneg _))
    (sqrt_annulus_one_le hB) hP hcount he he (fun _ => he)
    (norm_add_le _ _) (norm_add_le _ _) (fun _ => norm_add_le _ _)
    rfl rfl (fun _ => rfl)
    (min_le_right _ _) (min_le_right _ _) (fun _ => min_le_right _ _)
    w hleftSupport hrightSupport hslotSupport ξ

end BoundedData

end HeckeSkeleton.Moments.EngineStep.OriginalClippedGaussProfiles

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalClippedGaussProfiles.clippedScalar_profile_eq
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalClippedGaussProfiles.clipped_multiplier_identity
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalClippedGaussProfiles.original_left_identity
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalClippedGaussProfiles.original_prime_identity
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalClippedGaussProfiles.rawWindow
