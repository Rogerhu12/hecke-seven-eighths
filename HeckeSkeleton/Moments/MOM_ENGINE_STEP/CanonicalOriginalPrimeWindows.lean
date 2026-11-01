import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalChosenChildProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalProfileAtomBounds

/-!
# Raw prime and clipped profile windows at one actual radius

The radius already chosen for clipping also bounds the original moving
profiles: its annular clipping coefficient is at least one.  This gives
the prime theorem its raw single-slot window before the capacity data or
any removed subset is constructed.  A nonzero actual source member then
gives the clipped window at exactly that same radius.

All Schwartz representatives come from the original compact positive
window.  In particular this applies to the signed exponents of the real
residual profiles.  No transformed profile bound or amplitude bound is
assumed, and no capacity child is selected here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- A fixed union of original seminorm orders can serve both the base
and prime theorems without changing any representative or radius. -/
def RawProfileWindow.restrictOrders
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
    {s t : Finset (ℕ × ℕ)} {d : MomentData K ω ψ} {P : ℝ}
    (w : RawProfileWindow rowDomain heightDomain window t d P) (hst : s ⊆ t) :
    RawProfileWindow rowDomain heightDomain window s d P := by
  have hsup (φ : 𝓢(ℝ, ℂ)) :
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤
        t.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ :=
    Seminorm.finset_sup_apply_le (apply_nonneg _ _)
      (fun p hp => Seminorm.le_finset_sup_apply (hst hp))
  exact
    { w with
      inverse_bound := fun u hu v hv => (hsup _).trans (w.inverse_bound u hu v hv)
      left_bound := fun u hu v hv => (hsup _).trans (w.left_bound u hu v hv)
      right_bound := fun u hu v hv => (hsup _).trans (w.right_bound u hu v hv)
      prime_bound := fun i v hv => (hsup _).trans (w.prime_bound i v hv) }

namespace CanonicalLogProfiles.OriginalLogProfiles

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (D : OriginalLogProfiles K ω ψ (WithLp 2 (U × E)))

/-- The literal un-clipped log profiles fit the already chosen clipped
radius.  Global support follows from the original closed window. -/
def rawPolynomialWindow_at_clippedRadius
    (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B) (orders : Finset (ℕ × ℕ))
    {P : ℝ} (hP : 0 ≤ P)
    (w : RawProfileWindow Set.univ Set.univ (Set.Icc a B)
      (sourceOrders orders) D.original P) (z : U × E) :
    RawProfileWindow Set.univ Set.univ (Set.Icc a B) orders
      (D.moving (WithLp.toLp 2 z))
      (polynomialProfileRadius (D.amplitude a B ha orders P)
        (orders.sup Prod.snd) (orders.sup Prod.snd) z) := by
  let raw := polynomialWindow D.original D.left D.right D.slot
    D.left_positive D.right_positive D.slot_positive isCompact_Icc
    (positiveAnnulus a B ha) orders hP w
    (fun u t => closure_minimal (w.left_support u (Set.mem_univ _) t (Set.mem_univ _))
      isClosed_Icc)
    (fun u t => closure_minimal (w.right_support u (Set.mem_univ _) t (Set.mem_univ _))
      isClosed_Icc)
    (fun i t => closure_minimal (w.prime_support i t (Set.mem_univ _)) isClosed_Icc) z
  refine raw.mono ?_
  have hM := profileAmplitude_nonneg D.original D.left D.right D.slot
    (Set.Icc a B) isCompact_Icc (positiveAnnulus a B ha) orders hP
  have hclip := clippingCoefficient_one_le B hB orders
  unfold polynomialProfileRadius
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  change profileAmplitude D.original D.left D.right D.slot (Set.Icc a B)
      isCompact_Icc (positiveAnnulus a B ha) orders P ≤
    clippingCoefficient B orders * profileAmplitude D.original D.left D.right D.slot
      (Set.Icc a B) isCompact_Icc (positiveAnnulus a B ha) orders P
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hclip hM

/-- The raw prime orders are selected from the fixed common order set.
The coefficient and both polynomial degrees stay those of that set. -/
def rawPrimeWindow_at_clippedRadius
    (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B)
    (orders primeOrders : Finset (ℕ × ℕ))
    (horders : OriginalProfileAtomBounds.profileOrders primeOrders ⊆ orders)
    {P : ℝ} (hP : 0 ≤ P)
    (w : RawProfileWindow Set.univ Set.univ (Set.Icc a B)
      (sourceOrders orders) D.original P) (ξ : WithLp 2 (U × E)) :
    RawProfileWindow Set.univ Set.univ (Set.Icc a B)
      (OriginalProfileAtomBounds.profileOrders primeOrders) (D.moving ξ)
      (polynomialProfileRadius (D.amplitude a B ha orders P)
        (orders.sup Prod.snd) (orders.sup Prod.snd) (WithLp.ofLp ξ)) := by
  have raw := D.rawPolynomialWindow_at_clippedRadius a B ha hB orders hP w
    (WithLp.ofLp ξ)
  have hraw : RawProfileWindow Set.univ Set.univ (Set.Icc a B) orders
      (D.moving ξ)
      (polynomialProfileRadius (D.amplitude a B ha orders P)
        (orders.sup Prod.snd) (orders.sup Prod.snd) (WithLp.ofLp ξ)) := by
    simpa only [WithLp.toLp_ofLp] using raw
  exact hraw.restrictOrders horders

variable {A : SArithmeticData K} {σ : K →+* ℂ} {H : Type*} {k : ℕ}
variable {source : ActualAllocatedSource A (WithLp 2 (U × E)) H k}

/-- The active original source supplies a genuine nonzero energy
witness before normalization.  Its raw and clipped profiles then use
one literal radius, with no normalized-capacity data as an input. -/
def clippedWindow_of_actualSource
    (cal : source.Calibration (σ := σ) ω ψ)
    (hdata : ∀ ξ, cal.data ξ = D.moving ξ)
    (t : ℝ) (htime : ∀ ξ, cal.height ξ = t)
    (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B) (orders : Finset (ℕ × ℕ))
    {P : ℝ} (hP : 0 ≤ P)
    (w : RawProfileWindow Set.univ Set.univ (Set.Icc a B)
      (sourceOrders orders) D.original P)
    (hnonzero : ¬ ∀ ξ, source.energy (σ := σ) ξ = 0)
    (ξ : WithLp 2 (U × E)) :
    RawProfileWindow Set.univ Set.univ (Set.Icc (a / B) B) orders
      (cal.clippedData ξ)
      (polynomialProfileRadius (D.amplitude a B ha orders P)
        (orders.sup Prod.snd) (orders.sup Prod.snd) (WithLp.ofLp ξ)) := by
  let ξ₀ := Classical.choose (not_forall.mp hnonzero)
  have hsource : source.energy (σ := σ) ξ₀ ≠ 0 :=
    Classical.choose_spec (not_forall.mp hnonzero)
  have henergy : pairedEnergy (D.moving ξ₀) cal.parameters source.base t ≠ 0 := by
    intro he
    have hb := cal.energy_le ξ₀
    rw [hdata ξ₀, htime ξ₀, he, mul_zero] at hb
    exact hsource (le_antisymm hb (source.energy_nonneg (σ := σ) ξ₀))
  have hclipped : cal.clippedData ξ = clipPlainData (D.moving ξ)
      cal.parameters source.base (zero_lt_one.trans source.base_gt_one) :=
    congrArg (fun d => clipPlainData d cal.parameters source.base
      (zero_lt_one.trans source.base_gt_one)) (hdata ξ)
  rw [hclipped]
  have raw := clippedPolynomialWindow D.original D.left D.right D.slot
    D.left_positive D.right_positive D.slot_positive cal.parameters source.base t
    source.base_gt_one a B ha hB orders hP w
    (fun u v => closure_minimal (w.left_support u (Set.mem_univ _) v (Set.mem_univ _))
      isClosed_Icc)
    (fun u v => closure_minimal (w.right_support u (Set.mem_univ _) v (Set.mem_univ _))
      isClosed_Icc)
    (fun i v => closure_minimal (w.prime_support i v (Set.mem_univ _)) isClosed_Icc)
    (fun _ _ => Set.mem_univ _) (Set.mem_univ _) ξ₀ henergy (WithLp.ofLp ξ)
  simpa only [WithLp.toLp_ofLp] using raw

end CanonicalLogProfiles.OriginalLogProfiles
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.RawProfileWindow.restrictOrders
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.OriginalLogProfiles.rawPolynomialWindow_at_clippedRadius
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.OriginalLogProfiles.rawPrimeWindow_at_clippedRadius
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.OriginalLogProfiles.clippedWindow_of_actualSource
