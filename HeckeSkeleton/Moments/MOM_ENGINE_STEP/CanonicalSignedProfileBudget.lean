import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalProfileScaleBudget

/-!
# Fixed budgets for the signed original norm powers

The original inverse column norm leaves powers of the form `j * δ - 1`
after the two logarithmic transforms.  Their profile argument lies in
the original positive compact window.  The actual atom scale is one;
all original scale dependence in the unit phase remains in the offset.

The finite exponent palette, tilt, target orders, direction bound and
slot cap precede the moving original profiles and Fourier variables.
The analytic constants below are obtained from the already proved
Schwartz multiplier estimate, which allows every real exponent.
An explicit scalar multiplying an actual representative is also paid;
it is never silently included in the original seminorm budget.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

namespace CanonicalLogProfiles

/-- The shift is the literal original inverse-norm factor. -/
def shiftedExponentPalette (δ : ℝ) (R : ℕ) : Finset ℝ :=
  (Finset.range (R + 1)).image (fun j : ℕ => (j : ℝ) * δ - 1)

theorem mem_shiftedExponentPalette (δ : ℝ) (R j : ℕ) (hj : j ≤ R) :
    (j : ℝ) * δ - 1 ∈ shiftedExponentPalette δ R :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), rfl⟩

theorem shiftedExponentPalette_lower {δ e : ℝ} {R : ℕ}
    (hδ : 0 ≤ δ) (he : e ∈ shiftedExponentPalette δ R) : -1 ≤ e := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
  have hj : 0 ≤ (j : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ
  linarith

theorem shiftedExponentPalette_upper {δ e : ℝ} {R : ℕ}
    (hδ : 0 ≤ δ) (he : e ∈ shiftedExponentPalette δ R) :
    e ≤ (R : ℝ) * δ - 1 := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
  have hjR : j ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact sub_le_sub_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hjR) hδ) 1

theorem shiftedExponentPalette_interval {δ e : ℝ} {R : ℕ}
    (hδ : 0 ≤ δ) (hhalf : (R : ℝ) * δ ≤ 1 / 2)
    (he : e ∈ shiftedExponentPalette δ R) : e ∈ Set.Icc (-1) (-(1 / 2)) := by
  have hu := shiftedExponentPalette_upper hδ he
  exact ⟨shiftedExponentPalette_lower hδ he, by linarith⟩

/-- Reserve the signed-power condition after any earlier positive tilt
choice.  The old small-power budgets can only decrease. -/
def reserveSignedTilt (R : ℕ) (δ : ℝ) : ℝ :=
  min δ (1 / (2 * ((R : ℝ) + 1)))

theorem reserveSignedTilt_pos (R : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 < reserveSignedTilt R δ :=
  lt_min hδ (by positivity)

theorem reserveSignedTilt_le (R : ℕ) (δ : ℝ) : reserveSignedTilt R δ ≤ δ :=
  min_le_left _ _

theorem reserveSignedTilt_half (R : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (R : ℝ) * reserveSignedTilt R δ ≤ 1 / 2 := by
  have ht := (reserveSignedTilt_pos R hδ).le
  have hden : 0 < 2 * ((R : ℝ) + 1) := by positivity
  have hb : reserveSignedTilt R δ * (2 * ((R : ℝ) + 1)) ≤ 1 :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  nlinarith

def shiftedShapeCoefficient (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (orders : Finset (ℕ × ℕ))
    (δ : ℝ) (R : ℕ) : ℝ :=
  ∑ e ∈ shiftedExponentPalette δ R,
    shapeCoefficient window hcompact hpositive e orders

theorem shiftedShapeCoefficient_nonneg (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (orders : Finset (ℕ × ℕ)) (δ : ℝ) (R : ℕ) :
    0 ≤ shiftedShapeCoefficient window hcompact hpositive orders δ R :=
  Finset.sum_nonneg (fun e _ => shapeCoefficient_nonneg window hcompact hpositive e orders)

theorem shapeCoefficient_le_shifted (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (orders : Finset (ℕ × ℕ)) (δ : ℝ) (R : ℕ)
    {e : ℝ} (he : e ∈ shiftedExponentPalette δ R) :
    shapeCoefficient window hcompact hpositive e orders ≤
      shiftedShapeCoefficient window hcompact hpositive orders δ R :=
  Finset.single_le_sum
    (fun e _ => shapeCoefficient_nonneg window hcompact hpositive e orders) he

def signedAtomConstant (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (orders : Finset (ℕ × ℕ))
    (δ : ℝ) (R : ℕ) (D : ℝ) : ℝ :=
  shiftedShapeCoefficient window hcompact hpositive orders δ R *
    (1 + 2 * Real.pi * D) ^ (orders.sup Prod.snd)

theorem signedAtomConstant_nonneg (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (orders : Finset (ℕ × ℕ))
    (δ : ℝ) (R : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    0 ≤ signedAtomConstant window hcompact hpositive orders δ R D :=
  mul_nonneg (shiftedShapeCoefficient_nonneg window hcompact hpositive orders δ R)
    (pow_nonneg (by positivity) _)

def signedAmplitudeConstant (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (orders : Finset (ℕ × ℕ))
    (δ : ℝ) (R cap : ℕ) (D : ℝ) : ℝ :=
  1 + ((cap : ℝ) + 2) * signedAtomConstant window hcompact hpositive orders δ R D

theorem signedAmplitudeConstant_one_le (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (orders : Finset (ℕ × ℕ))
    (δ : ℝ) (R cap : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    1 ≤ signedAmplitudeConstant window hcompact hpositive orders δ R cap D := by
  exact le_add_of_nonneg_right (mul_nonneg (by positivity)
    (signedAtomConstant_nonneg window hcompact hpositive orders δ R D hD))

section Atoms

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Negative powers cost only the positive original support window.
There is no original moving scale power when the actual scale is one. -/
theorem Atom.profileCoefficient_le_shifted (p : Atom V)
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (orders : Finset (ℕ × ℕ)) (δ : ℝ) (R : ℕ) (D : ℝ)
    (hscale : p.scale = 1) (he : p.exponent ∈ shiftedExponentPalette δ R)
    (hd : ‖p.direction‖ ≤ D) :
    p.profileCoefficient window hcompact hpositive orders ≤
      signedAtomConstant window hcompact hpositive orders δ R D := by
  have hdirection : (1 + 2 * Real.pi * ‖p.direction‖) ^ (orders.sup Prod.snd) ≤
      (1 + 2 * Real.pi * D) ^ (orders.sup Prod.snd) :=
    pow_le_pow_left₀ (by positivity)
      (add_le_add_left (mul_le_mul_of_nonneg_left hd (by positivity)) 1) _
  unfold Atom.profileCoefficient
  rw [hscale, Real.one_rpow, mul_one]
  exact mul_le_mul (shapeCoefficient_le_shifted window hcompact hpositive orders δ R he)
    hdirection (pow_nonneg (by positivity) _)
    (shiftedShapeCoefficient_nonneg window hcompact hpositive orders δ R)

/-- This is the actual scaled Schwartz representative.  The bound pays
the scalar explicitly, and is uniform in the original test and offset. -/
theorem Atom.scaledSchwartz_signed_bound (p : Atom V)
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (orders : Finset (ℕ × ℕ)) (δ : ℝ) (R : ℕ) (D S P : ℝ)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hP : 0 ≤ P)
    (hscale : p.scale = 1) (he : p.exponent ∈ shiftedExponentPalette δ R)
    (hd : ‖p.direction‖ ≤ D)
    (c : ℂ) (hc : ‖c‖ ≤ S) (ξ : V) (φ : 𝓢(ℝ, ℂ))
    (hsupport : tsupport φ ⊆ window)
    (hφ : (sourceOrders orders).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤ P) :
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (c • p.schwartz window hcompact hpositive ξ φ hsupport) ≤
      (S * signedAtomConstant window hcompact hpositive orders δ R D) *
        P * (1 + ‖ξ‖) ^ (orders.sup Prod.snd) := by
  have hC := signedAtomConstant_nonneg window hcompact hpositive orders δ R D hD
  have hpow : 0 ≤ (1 + ‖ξ‖) ^ (orders.sup Prod.snd) := pow_nonneg (by positivity) _
  have hb := p.schwartz_finset_bound window hcompact hpositive orders ξ φ hsupport
  have hb' := hb.trans
    (mul_le_mul
      (mul_le_mul_of_nonneg_right
        (p.profileCoefficient_le_shifted window hcompact hpositive orders δ R D hscale he hd)
        hpow) hφ (apply_nonneg _ _) (mul_nonneg hC hpow))
  rw [map_smul_eq_mul]
  apply (mul_le_mul hc hb' (apply_nonneg _ _) hS).trans_eq
  ring

end Atoms

section Amplitudes

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The actual common amplitude has a fixed bound before any moving
profile or Fourier parameter.  Both plain atoms and every retained
prime occurrence are counted. -/
theorem profileAmplitude_le_shifted
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (orders : Finset (ℕ × ℕ)) (δ : ℝ) (R cap : ℕ) (D P : ℝ)
    (hD : 0 ≤ D) (hP : 0 ≤ P)
    (d : MomentData K ω ψ) (left right : Atom V)
    (slot : Fin d.geometry.slotCount → Atom V) (hcount : d.geometry.slotCount ≤ cap)
    (hlE : left.exponent ∈ shiftedExponentPalette δ R)
    (hrE : right.exponent ∈ shiftedExponentPalette δ R)
    (hsE : ∀ i, (slot i).exponent ∈ shiftedExponentPalette δ R)
    (hlD : ‖left.direction‖ ≤ D) (hrD : ‖right.direction‖ ≤ D)
    (hsD : ∀ i, ‖(slot i).direction‖ ≤ D)
    (hlS : left.scale = 1) (hrS : right.scale = 1) (hsS : ∀ i, (slot i).scale = 1) :
    profileAmplitude d left right slot window hcompact hpositive orders P ≤
      signedAmplitudeConstant window hcompact hpositive orders δ R cap D * P := by
  let C := signedAtomConstant window hcompact hpositive orders δ R D
  have hC : 0 ≤ C := signedAtomConstant_nonneg window hcompact hpositive orders δ R D hD
  have hleft : left.profileCoefficient window hcompact hpositive orders ≤ C :=
    left.profileCoefficient_le_shifted window hcompact hpositive orders δ R D hlS hlE hlD
  have hright : right.profileCoefficient window hcompact hpositive orders ≤ C :=
    right.profileCoefficient_le_shifted window hcompact hpositive orders δ R D hrS hrE hrD
  have hsum : (∑ i, (slot i).profileCoefficient window hcompact hpositive orders) ≤
      (d.geometry.slotCount : ℝ) * C := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
        (slot i).profileCoefficient_le_shifted window hcompact hpositive orders δ R D
          (hsS i) (hsE i) (hsD i))
  have hsumCap : (∑ i, (slot i).profileCoefficient window hcompact hpositive orders) ≤
      (cap : ℝ) * C :=
    hsum.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hC)
  have hwhole : 1 + left.profileCoefficient window hcompact hpositive orders +
      right.profileCoefficient window hcompact hpositive orders +
        ∑ i, (slot i).profileCoefficient window hcompact hpositive orders ≤
      1 + ((cap : ℝ) + 2) * C := by linarith
  unfold profileAmplitude
  exact (mul_le_mul_of_nonneg_left hwhole hP).trans_eq (mul_comm _ _)

end Amplitudes

/-- These are the actual positive scalar factors of the original plain
and prime profiles. They precede the Fourier parameter. -/
structure ProfileScalars (n : ℕ) where
  left : ℝ
  right : ℝ
  prime : Fin n → ℝ
  left_pos : 0 < left
  right_pos : 0 < right
  prime_pos : ∀ i, 0 < prime i

section ScalarData

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

private def scalarIdealTest (W : IdealTest K) (c : ℝ) (hc : 0 < c) : IdealTest K where
  profile u t y := (c : ℂ) * W.profile u t y
  support := W.support
  support_spec u t N I := by
    rw [W.support_spec]
    exact ⟨mul_ne_zero (by exact_mod_cast hc.ne'), right_ne_zero_of_mul⟩

private def scalarPrimeWindow (W : PrimeWindow K) (c : ℝ) (hc : 0 < c) : PrimeWindow K where
  length := W.length
  length_pos := W.length_pos
  profile t y := (c : ℂ) * W.profile t y
  support := W.support
  support_spec t N p := by
    rw [W.support_spec]
    exact ⟨mul_ne_zero (by exact_mod_cast hc.ne'), right_ne_zero_of_mul⟩

namespace ProfileScalars

variable (d : MomentData K ω ψ) (c : ProfileScalars d.geometry.slotCount)

/-- Only the stated profile scalars are installed. All arithmetic,
allowed rows, finite supports and original slot lengths remain literal. -/
def data : MomentData K ω ψ :=
  { d with
    plainTest₁ := scalarIdealTest d.plainTest₁ c.left c.left_pos
    plainTest₂ := scalarIdealTest d.plainTest₂ c.right c.right_pos
    geometry :=
      { slotCount := d.geometry.slotCount
        slots i := scalarPrimeWindow (d.geometry.slots i) (c.prime i) (c.prime_pos i) } }

@[simp] theorem data_count : (c.data d).geometry.slotCount = d.geometry.slotCount := rfl

@[simp] theorem data_prime_length (i : Fin d.geometry.slotCount) :
    ((c.data d).geometry.slots i).length = (d.geometry.slots i).length := rfl

@[simp] theorem data_pairedRows (a : RealParameters) (Z : ℝ) :
    pairedRows (c.data d) a Z = pairedRows d a Z := rfl

theorem left_positive (h : PositivePlainProfile d.plainTest₁) :
    PositivePlainProfile (c.data d).plainTest₁ := by
  intro u t y hy
  exact h u t y (right_ne_zero_of_mul hy)

theorem right_positive (h : PositivePlainProfile d.plainTest₂) :
    PositivePlainProfile (c.data d).plainTest₂ := by
  intro u t y hy
  exact h u t y (right_ne_zero_of_mul hy)

theorem prime_positive (h : ∀ i, PositivePrimeProfile (d.geometry.slots i)) :
    ∀ i, PositivePrimeProfile ((c.data d).geometry.slots i) := by
  intro i t y hy
  exact h i t y (right_ne_zero_of_mul hy)

/-- A bounded actual scalar is paid from the original seminorm bound.
The moving scaled profiles are not supplied with their own bound. -/
def rawWindow {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
    {orders : Finset (ℕ × ℕ)} {P : ℝ} (hP : 0 ≤ P)
    (w : RawProfileWindow rowDomain heightDomain window orders d P)
    (S : ℝ) (hS : 1 ≤ S) (hleft : c.left ≤ S) (hright : c.right ≤ S)
    (hprime : ∀ i, c.prime i ≤ S) :
    RawProfileWindow rowDomain heightDomain window orders (c.data d) (S * P) := by
  have hbound (r : ℝ) (hr : 0 ≤ r) (hrS : r ≤ S)
      (φ : 𝓢(ℝ, ℂ)) (hφ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤ P) :
      orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) ((r : ℂ) • φ) ≤ S * P := by
    rw [map_smul_eq_mul, Complex.norm_of_nonneg hr]
    exact mul_le_mul hrS hφ (apply_nonneg _ _) (zero_le_one.trans hS)
  refine
    { inverseRep := w.inverseRep
      leftRep := fun u t => (c.left : ℂ) • w.leftRep u t
      rightRep := fun u t => (c.right : ℂ) • w.rightRep u t
      primeRep := fun i t => (c.prime i : ℂ) • w.primeRep i t
      inverse_eq := w.inverse_eq
      left_eq := ?_
      right_eq := ?_
      prime_eq := ?_
      inverse_support := w.inverse_support
      left_support := ?_
      right_support := ?_
      prime_support := ?_
      inverse_bound := fun u hu t ht => (w.inverse_bound u hu t ht).trans
        (le_mul_of_one_le_left hP hS)
      left_bound := fun u hu t ht =>
        hbound c.left c.left_pos.le hleft _ (w.left_bound u hu t ht)
      right_bound := fun u hu t ht =>
        hbound c.right c.right_pos.le hright _ (w.right_bound u hu t ht)
      prime_bound := fun i t ht =>
        hbound (c.prime i) (c.prime_pos i).le (hprime i) _ (w.prime_bound i t ht) }
  · intro u t y
    change (c.left : ℂ) * d.plainTest₁.profile u t y = (c.left : ℂ) * w.leftRep u t y
    rw [w.left_eq]
  · intro u t y
    change (c.right : ℂ) * d.plainTest₂.profile u t y = (c.right : ℂ) * w.rightRep u t y
    rw [w.right_eq]
  · intro i t y
    change (c.prime i : ℂ) * (d.geometry.slots i).profile t y =
      (c.prime i : ℂ) * w.primeRep i t y
    rw [w.prime_eq]
  · intro u hu t ht y hy
    exact w.left_support u hu t ht (right_ne_zero_of_mul hy)
  · intro u hu t ht y hy
    exact w.right_support u hu t ht (right_ne_zero_of_mul hy)
  · intro i t ht y hy
    exact w.prime_support i t ht (right_ne_zero_of_mul hy)

end ProfileScalars
end ScalarData

section SignedWindows

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Construct the true signed multiplier window, including each actual
positive prefactor, directly from the original profile representatives.
The common coefficient depends only on the fixed palette and cap. -/
def signedRawWindow
    (d : MomentData K ω ψ) (c : ProfileScalars d.geometry.slotCount)
    (left right : Atom V) (slot : Fin d.geometry.slotCount → Atom V)
    (hleft : PositivePlainProfile d.plainTest₁)
    (hright : PositivePlainProfile d.plainTest₂)
    (hslot : ∀ i, PositivePrimeProfile (d.geometry.slots i))
    {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (orders : Finset (ℕ × ℕ)) (δ : ℝ) (R cap : ℕ) (D S P : ℝ)
    (hD : 0 ≤ D) (hS : 1 ≤ S) (hP : 0 ≤ P)
    (hcount : d.geometry.slotCount ≤ cap)
    (hlE : left.exponent ∈ shiftedExponentPalette δ R)
    (hrE : right.exponent ∈ shiftedExponentPalette δ R)
    (hsE : ∀ i, (slot i).exponent ∈ shiftedExponentPalette δ R)
    (hlD : ‖left.direction‖ ≤ D) (hrD : ‖right.direction‖ ≤ D)
    (hsD : ∀ i, ‖(slot i).direction‖ ≤ D)
    (hlS : left.scale = 1) (hrS : right.scale = 1) (hsS : ∀ i, (slot i).scale = 1)
    (hscalarLeft : c.left ≤ S) (hscalarRight : c.right ≤ S)
    (hscalarPrime : ∀ i, c.prime i ≤ S)
    (w : RawProfileWindow rowDomain heightDomain window (sourceOrders orders) d P)
    (hleftSupport : ∀ u t, tsupport (w.leftRep u t) ⊆ window)
    (hrightSupport : ∀ u t, tsupport (w.rightRep u t) ⊆ window)
    (hslotSupport : ∀ i t, tsupport (w.primeRep i t) ⊆ window) (ξ : V) :
    RawProfileWindow rowDomain heightDomain window orders
      (data (c.data d) left right slot
        (c.left_positive d hleft) (c.right_positive d hright) (c.prime_positive d hslot) ξ)
      (signedAmplitudeConstant window hcompact hpositive orders δ R cap D *
        S * P * (1 + ‖ξ‖) ^ (orders.sup Prod.snd)) := by
  let base := c.rawWindow d hP w S hS hscalarLeft hscalarRight hscalarPrime
  have hSP : 0 ≤ S * P := mul_nonneg (zero_le_one.trans hS) hP
  have hlSupport : ∀ u t, tsupport (base.leftRep u t) ⊆ window := by
    intro u t
    exact (tsupport_smul_subset_right (fun _ : ℝ => (c.left : ℂ))
      (w.leftRep u t)).trans (hleftSupport u t)
  have hrSupport : ∀ u t, tsupport (base.rightRep u t) ⊆ window := by
    intro u t
    exact (tsupport_smul_subset_right (fun _ : ℝ => (c.right : ℂ))
      (w.rightRep u t)).trans (hrightSupport u t)
  have hsSupport : ∀ i t, tsupport (base.primeRep i t) ⊆ window := by
    intro i t
    exact (tsupport_smul_subset_right (fun _ : ℝ => (c.prime i : ℂ))
      (w.primeRep i t)).trans (hslotSupport i t)
  let formed := rawWindow (c.data d) left right slot
    (c.left_positive d hleft) (c.right_positive d hright) (c.prime_positive d hslot)
    hcompact hpositive orders hSP base hlSupport hrSupport hsSupport ξ
  refine formed.mono ?_
  have hb := profileAmplitude_le_shifted window hcompact hpositive orders δ R cap D
    (S * P) hD hSP (c.data d) left right slot hcount hlE hrE hsE hlD hrD hsD hlS hrS hsS
  exact (mul_le_mul_of_nonneg_right hb (pow_nonneg (by positivity) _)).trans_eq (by ring)

/-- The signed profiles and their original positive prefactors have an
actual two-variable polynomial window. This constructs the input to
the existing normalization theorem on the same data. -/
def signedPolynomialWindow
    {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : MomentData K ω ψ) (c : ProfileScalars d.geometry.slotCount)
    (left right : Atom (WithLp 2 (U × E)))
    (slot : Fin d.geometry.slotCount → Atom (WithLp 2 (U × E)))
    (hleft : PositivePlainProfile d.plainTest₁)
    (hright : PositivePlainProfile d.plainTest₂)
    (hslot : ∀ i, PositivePrimeProfile (d.geometry.slots i))
    {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (orders : Finset (ℕ × ℕ)) (δ : ℝ) (R cap : ℕ) (D S P : ℝ)
    (hD : 0 ≤ D) (hS : 1 ≤ S) (hP : 0 ≤ P)
    (hcount : d.geometry.slotCount ≤ cap)
    (hlE : left.exponent ∈ shiftedExponentPalette δ R)
    (hrE : right.exponent ∈ shiftedExponentPalette δ R)
    (hsE : ∀ i, (slot i).exponent ∈ shiftedExponentPalette δ R)
    (hlD : ‖left.direction‖ ≤ D) (hrD : ‖right.direction‖ ≤ D)
    (hsD : ∀ i, ‖(slot i).direction‖ ≤ D)
    (hlS : left.scale = 1) (hrS : right.scale = 1) (hsS : ∀ i, (slot i).scale = 1)
    (hscalarLeft : c.left ≤ S) (hscalarRight : c.right ≤ S)
    (hscalarPrime : ∀ i, c.prime i ≤ S)
    (w : RawProfileWindow rowDomain heightDomain window (sourceOrders orders) d P)
    (hleftSupport : ∀ u t, tsupport (w.leftRep u t) ⊆ window)
    (hrightSupport : ∀ u t, tsupport (w.rightRep u t) ⊆ window)
    (hslotSupport : ∀ i t, tsupport (w.primeRep i t) ⊆ window) (z : U × E) :
    RawProfileWindow rowDomain heightDomain window orders
      (data (c.data d) left right slot
        (c.left_positive d hleft) (c.right_positive d hright) (c.prime_positive d hslot)
        (WithLp.toLp 2 z))
      (polynomialProfileRadius
        (signedAmplitudeConstant window hcompact hpositive orders δ R cap D * S * P)
        (orders.sup Prod.snd) (orders.sup Prod.snd) z) := by
  let w' := signedRawWindow d c left right slot hleft hright hslot hcompact hpositive
    orders δ R cap D S P hD hS hP hcount hlE hrE hsE hlD hrD hsD hlS hrS hsS
    hscalarLeft hscalarRight hscalarPrime w hleftSupport hrightSupport hslotSupport
    (WithLp.toLp 2 z)
  refine w'.mono ?_
  have hC := zero_le_one.trans
    (signedAmplitudeConstant_one_le window hcompact hpositive orders δ R cap D hD)
  have hA : 0 ≤ signedAmplitudeConstant window hcompact hpositive orders δ R cap D * S * P :=
    mul_nonneg (mul_nonneg hC (zero_le_one.trans hS)) hP
  have hb := mul_le_mul_of_nonneg_left
    (hilbert_product_polynomial_le (orders.sup Prod.snd) z) hA
  exact hb.trans (by unfold polynomialProfileRadius; linarith)

/-- The actual clipping radius uses the same signed atoms.  The
original bounded prefactors and clipping coefficient both stay visible
in its one fixed amplitude constant. -/
theorem clippedProfileAmplitude_le_shifted
    {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B) (orders : Finset (ℕ × ℕ))
    (δ : ℝ) (R cap : ℕ) (D S P : ℝ) (hD : 0 ≤ D) (hS : 0 ≤ S) (hP : 0 ≤ P)
    (d : MomentData K ω ψ) (left right : Atom (WithLp 2 (U × E)))
    (slot : Fin d.geometry.slotCount → Atom (WithLp 2 (U × E)))
    (hcount : d.geometry.slotCount ≤ cap)
    (hlE : left.exponent ∈ shiftedExponentPalette δ R)
    (hrE : right.exponent ∈ shiftedExponentPalette δ R)
    (hsE : ∀ i, (slot i).exponent ∈ shiftedExponentPalette δ R)
    (hlD : ‖left.direction‖ ≤ D) (hrD : ‖right.direction‖ ≤ D)
    (hsD : ∀ i, ‖(slot i).direction‖ ≤ D)
    (hlS : left.scale = 1) (hrS : right.scale = 1) (hsS : ∀ i, (slot i).scale = 1) :
    clippedProfileAmplitude d left right slot a B ha orders (S * P) ≤
      (clippingCoefficient B orders *
        signedAmplitudeConstant (Set.Icc a B) isCompact_Icc (positiveAnnulus a B ha)
          orders δ R cap D * S) * P := by
  have hb := profileAmplitude_le_shifted (Set.Icc a B) isCompact_Icc
    (positiveAnnulus a B ha) orders δ R cap D (S * P) hD (mul_nonneg hS hP)
    d left right slot hcount hlE hrE hsE hlD hrD hsD hlS hrS hsS
  unfold clippedProfileAmplitude
  exact (mul_le_mul_of_nonneg_left hb
    (zero_le_one.trans (clippingCoefficient_one_le B hB orders))).trans_eq (by ring)

end SignedWindows

end CanonicalLogProfiles
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.Atom.scaledSchwartz_signed_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.profileAmplitude_le_shifted
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.ProfileScalars.rawWindow
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.signedRawWindow
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.signedPolynomialWindow
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.clippedProfileAmplitude_le_shifted
