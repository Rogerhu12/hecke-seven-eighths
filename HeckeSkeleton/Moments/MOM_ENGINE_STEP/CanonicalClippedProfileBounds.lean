import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfileBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Actual clipping of the original Schwartz profiles

The prescribed plain clipping is the literal function
`sqrt c * φ (c * y)`.  Its derivatives are computed from the linear
change of variable.  For `1 ≤ c ≤ B`, one fixed factor
`sqrt B * B^J` controls every requested seminorm through order `J`.
The original annulus changes only from `[a,B]` to `[a/B,B]`.

The bound on `c` is obtained from a genuine nonzero original plain
polynomial and the original ideal-norm lower bound.  No clipped profile
window is supplied as an input.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap ContDiff Topology

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

namespace CanonicalLogProfiles

def dilation (c : ℝ) (φ : 𝓢(ℝ, ℂ)) (y : ℝ) : ℂ :=
  (Real.sqrt c : ℂ) * φ (c * y)

theorem dilation_smooth (c : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (dilation c φ) :=
  contDiff_const.mul (φ.smooth'.comp (contDiff_const.mul contDiff_id))

theorem iteratedDeriv_dilation (c : ℝ) (φ : 𝓢(ℝ, ℂ)) (n : ℕ) (y : ℝ) :
    iteratedDeriv n (dilation c φ) y =
      (Real.sqrt c : ℂ) * (c ^ n • iteratedDeriv n φ (c * y)) := by
  unfold dilation
  rw [iteratedDeriv_const_mul_field]
  exact congrArg (fun z : ℂ => (Real.sqrt c : ℂ) * z)
    (congrFun (iteratedDeriv_comp_const_smul (n := n) (f := (φ : ℝ → ℂ))
      (φ.smooth'.of_le (by simp)) c) y)

theorem norm_iteratedDeriv_dilation (c : ℝ) (hc : 0 ≤ c)
    (φ : 𝓢(ℝ, ℂ)) (n : ℕ) (y : ℝ) :
    ‖iteratedDeriv n (dilation c φ) y‖ =
      (Real.sqrt c * c ^ n) * ‖iteratedDeriv n φ (c * y)‖ := by
  rw [iteratedDeriv_dilation]
  simp only [norm_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (pow_nonneg hc _)]
  ring

theorem dilation_weighted_derivative_bound (c : ℝ) (hc : 1 ≤ c)
    (φ : 𝓢(ℝ, ℂ)) (k n : ℕ) (y : ℝ) :
    |y| ^ k * ‖iteratedDeriv n (dilation c φ) y‖ ≤
      (Real.sqrt c * c ^ n) * SchwartzMap.seminorm ℂ k n φ := by
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hfactor : 0 ≤ Real.sqrt c * c ^ n :=
    mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hc0 _)
  have habs : |y| ≤ |c * y| := by
    rw [abs_mul, abs_of_nonneg hc0]
    nlinarith [abs_nonneg y]
  rw [norm_iteratedDeriv_dilation c hc0 φ n y]
  calc
    _ ≤ |c * y| ^ k * ((Real.sqrt c * c ^ n) * ‖iteratedDeriv n φ (c * y)‖) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) habs k)
        (mul_nonneg hfactor (norm_nonneg _))
    _ = (Real.sqrt c * c ^ n) * (|c * y| ^ k * ‖iteratedDeriv n φ (c * y)‖) := by ring
    _ ≤ (Real.sqrt c * c ^ n) * SchwartzMap.seminorm ℂ k n φ :=
      mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm' ℂ k n φ (c * y)) hfactor

/-- The actual clipped function is Schwartz without a compact-support
or decay certificate for the transformed function. -/
def dilationSchwartz (c : ℝ) (hc : 1 ≤ c) (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) where
  toFun := dilation c φ
  smooth' := dilation_smooth c φ
  decay' k n := ⟨(Real.sqrt c * c ^ n) * SchwartzMap.seminorm ℂ k n φ, fun y => by
    rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact dilation_weighted_derivative_bound c hc φ k n y⟩

@[simp] theorem dilationSchwartz_apply (c : ℝ) (hc : 1 ≤ c)
    (φ : 𝓢(ℝ, ℂ)) (y : ℝ) :
    dilationSchwartz c hc φ y = (Real.sqrt c : ℂ) * φ (c * y) := rfl

theorem dilationSchwartz_seminorm_bound (c : ℝ) (hc : 1 ≤ c)
    (φ : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (dilationSchwartz c hc φ) ≤
      (Real.sqrt c * c ^ n) * SchwartzMap.seminorm ℂ k n φ := by
  apply SchwartzMap.seminorm_le_bound' ℂ k n _
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (zero_le_one.trans hc) _))
      (apply_nonneg _ _))
  exact dilation_weighted_derivative_bound c hc φ k n

/-- Only the fixed original annulus and derivative order enter this
coefficient.  The pointwise scale and all Fourier parameters are later. -/
def clippingCoefficient (B : ℝ) (s : Finset (ℕ × ℕ)) : ℝ :=
  Real.sqrt B * B ^ (s.sup Prod.snd)

theorem clippingCoefficient_one_le (B : ℝ) (hB : 1 ≤ B) (s : Finset (ℕ × ℕ)) :
    1 ≤ clippingCoefficient B s := by
  have hsqrt : 1 ≤ Real.sqrt B := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hB
  have hpow : 1 ≤ B ^ (s.sup Prod.snd) := one_le_pow₀ hB
  change 1 ≤ Real.sqrt B * B ^ (s.sup Prod.snd)
  simpa only [one_mul] using mul_le_mul hsqrt hpow zero_le_one (zero_le_one.trans hsqrt)

theorem dilationSchwartz_finset_bound (B : ℝ) (hB : 1 ≤ B)
    (s : Finset (ℕ × ℕ)) (c : ℝ) (hc : 1 ≤ c) (hcB : c ≤ B) (φ : 𝓢(ℝ, ℂ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (dilationSchwartz c hc φ) ≤
      clippingCoefficient B s * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  have hC : 0 ≤ clippingCoefficient B s := zero_le_one.trans (clippingCoefficient_one_le B hB s)
  apply Seminorm.finset_sup_apply_le (mul_nonneg hC (apply_nonneg _ _))
  intro p hp
  have hpow : c ^ p.2 ≤ B ^ (s.sup Prod.snd) :=
    (pow_le_pow_left₀ (zero_le_one.trans hc) hcB _).trans
      (pow_le_pow_right₀ hB (Finset.le_sup (f := Prod.snd) hp))
  have hfactor : Real.sqrt c * c ^ p.2 ≤ clippingCoefficient B s :=
    mul_le_mul (Real.sqrt_le_sqrt hcB) hpow
      (pow_nonneg (zero_le_one.trans hc) _) (Real.sqrt_nonneg _)
  exact (dilationSchwartz_seminorm_bound c hc φ p.1 p.2).trans
    (mul_le_mul hfactor
      (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ ℝ ℂ) (x := φ) hp)
      (apply_nonneg _ _) hC)

theorem dilationSchwartz_support (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B)
    (c : ℝ) (hc : 1 ≤ c) (hcB : c ≤ B) (φ : 𝓢(ℝ, ℂ))
    (hsupport : Function.support (φ : ℝ → ℂ) ⊆ Set.Icc a B) :
    Function.support (dilationSchwartz c hc φ) ⊆ Set.Icc (a / B) B := by
  intro y hy
  change (Real.sqrt c : ℂ) * φ (c * y) ≠ 0 at hy
  have hφ : φ (c * y) ≠ 0 := right_ne_zero_of_mul hy
  have hcy := hsupport hφ
  have hc0 := zero_le_one.trans hc
  have hB0 := zero_lt_one.trans_le hB
  have hy0 : 0 < y := by
    by_contra h
    have hn := mul_nonpos_of_nonneg_of_nonpos hc0 (le_of_not_gt h)
    linarith [hcy.1]
  constructor
  · apply (div_le_iff₀ hB0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcB hy0.le, hcy.1]
  · have hyc : y ≤ c * y := by nlinarith
    exact hyc.trans hcy.2

theorem dilationSchwartz_tsupport (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B)
    (c : ℝ) (hc : 1 ≤ c) (hcB : c ≤ B) (φ : 𝓢(ℝ, ℂ))
    (hsupport : tsupport φ ⊆ Set.Icc a B) :
    tsupport (dilationSchwartz c hc φ) ⊆ Set.Icc (a / B) B :=
  closure_minimal (dilationSchwartz_support a B ha hB c hc hcB φ
    ((subset_tsupport φ).trans hsupport)) isClosed_Icc

theorem originalAnnulus_subset_clipped (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B) :
    Set.Icc a B ⊆ Set.Icc (a / B) B := by
  have hlow : a / B ≤ a := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hB)).mpr
    nlinarith
  intro y hy
  exact ⟨hlow.trans hy.1, hy.2⟩

section Windows

variable {K : Type} [Field K] [NumberField K] {«ω» ψ : HeckeCharacter K}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}

/-- A literal original window gives the window of the actual clipped
data.  Every transformed representative and every seminorm bound is
constructed from the original representative. -/
def clipRawWindow (d : MomentData K «ω» ψ) (p : RealParameters)
    (Z : ℝ) (hZ : 1 ≤ Z) (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B)
    (s : Finset (ℕ × ℕ)) {A : ℝ} (hA : 0 ≤ A)
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc a B) s d A)
    (hleft : plainClippingFactor Z p.n₁ ≤ B)
    (hright : plainClippingFactor Z p.n₂ ≤ B) :
    RawProfileWindow rowDomain heightDomain (Set.Icc (a / B) B) s
      (clipPlainData d p Z (zero_lt_one.trans_le hZ)) (clippingCoefficient B s * A) := by
  let c₁ := plainClippingFactor Z p.n₁
  let c₂ := plainClippingFactor Z p.n₂
  have hc₁ : 1 ≤ c₁ := plainClippingFactor_one_le Z p.n₁ hZ
  have hc₂ : 1 ≤ c₂ := plainClippingFactor_one_le Z p.n₂ hZ
  have hC : 0 ≤ clippingCoefficient B s := zero_le_one.trans (clippingCoefficient_one_le B hB s)
  have hAC : A ≤ clippingCoefficient B s * A := by
    simpa only [mul_comm] using le_mul_of_one_le_right hA (clippingCoefficient_one_le B hB s)
  refine
    { inverseRep := w.inverseRep
      leftRep := fun u t => dilationSchwartz c₁ hc₁ (w.leftRep u t)
      rightRep := fun u t => dilationSchwartz c₂ hc₂ (w.rightRep u t)
      primeRep := w.primeRep
      inverse_eq := w.inverse_eq
      left_eq := ?_
      right_eq := ?_
      prime_eq := w.prime_eq
      inverse_support := fun u hu t ht =>
        (w.inverse_support u hu t ht).trans (originalAnnulus_subset_clipped a B ha hB)
      left_support := fun u hu t ht => dilationSchwartz_support a B ha hB c₁ hc₁ hleft
        (w.leftRep u t) (w.left_support u hu t ht)
      right_support := fun u hu t ht => dilationSchwartz_support a B ha hB c₂ hc₂ hright
        (w.rightRep u t) (w.right_support u hu t ht)
      prime_support := fun i t ht =>
        (w.prime_support i t ht).trans (originalAnnulus_subset_clipped a B ha hB)
      inverse_bound := fun u hu t ht => (w.inverse_bound u hu t ht).trans hAC
      left_bound := fun u hu t ht =>
        (dilationSchwartz_finset_bound B hB s c₁ hc₁ hleft (w.leftRep u t)).trans
          (mul_le_mul_of_nonneg_left (w.left_bound u hu t ht) hC)
      right_bound := fun u hu t ht =>
        (dilationSchwartz_finset_bound B hB s c₂ hc₂ hright (w.rightRep u t)).trans
          (mul_le_mul_of_nonneg_left (w.right_bound u hu t ht) hC)
      prime_bound := fun i t ht => (w.prime_bound i t ht).trans hAC }
  · intro u t y
    change (Real.sqrt c₁ : ℂ) * d.plainTest₁.profile u t (c₁ * y) = _
    rw [dilationSchwartz_apply, w.left_eq]
  · intro u t y
    change (Real.sqrt c₂ : ℂ) * d.plainTest₂.profile u t (c₂ * y) = _
    rw [dilationSchwartz_apply, w.right_eq]

/-- The dilation constants are derived from one genuine nonzero
original row, using the actual ideal lower bound in the clipping lemma. -/
theorem clipping_factors_le_of_window_nonzero
    (d : MomentData K «ω» ψ) (p : RealParameters) (Z t a B : ℝ)
    (hZ : 1 < Z) (hB : 1 ≤ B) (s : Finset (ℕ × ℕ)) (A : ℝ)
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc a B) s d A)
    (hrows : ∀ u ∈ pairedRows d p Z, u ∈ rowDomain) (ht : t ∈ heightDomain)
    (hne : pairedEnergy d p Z t ≠ 0) :
    plainClippingFactor Z p.n₁ ≤ B ∧ plainClippingFactor Z p.n₂ ≤ B := by
  obtain ⟨u, hu, hleft, hright⟩ := nonzero_pairedEnergy_plain_witness d p Z t hne
  have hleftAnnulus : ∀ y, d.plainTest₁.profile u t y ≠ 0 → y ≤ B := by
    intro y hy
    rw [w.left_eq] at hy
    exact (w.left_support u (hrows u hu) t ht hy).2
  have hrightAnnulus : ∀ y, d.plainTest₂.profile u t y ≠ 0 → y ≤ B := by
    intro y hy
    rw [w.right_eq] at hy
    exact (w.right_support u (hrows u hu) t ht hy).2
  exact ⟨clipping_factor_le_of_nonempty_support d.plainTest₁ u Z p.n₁ t B hZ hB
      hleftAnnulus (plainPolynomial_support_nonempty d d.plainTest₁ u _ t hleft),
    clipping_factor_le_of_nonempty_support d.plainTest₂ u Z p.n₂ t B hZ hB
      hrightAnnulus (plainPolynomial_support_nonempty d d.plainTest₂ u _ t hright)⟩

def clipRawWindow_of_nonzero (d : MomentData K «ω» ψ) (p : RealParameters)
    (Z t : ℝ) (hZ : 1 < Z) (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B)
    (s : Finset (ℕ × ℕ)) {A : ℝ} (hA : 0 ≤ A)
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc a B) s d A)
    (hrows : ∀ u ∈ pairedRows d p Z, u ∈ rowDomain) (ht : t ∈ heightDomain)
    (hne : pairedEnergy d p Z t ≠ 0) :
    RawProfileWindow rowDomain heightDomain (Set.Icc (a / B) B) s
      (clipPlainData d p Z (zero_lt_one.trans hZ)) (clippingCoefficient B s * A) :=
  clipRawWindow d p Z hZ.le a B ha hB s hA w
    (clipping_factors_le_of_window_nonzero d p Z t a B hZ hB s A w hrows ht hne).1
    (clipping_factors_le_of_window_nonzero d p Z t a B hZ hB s A w hrows ht hne).2

end Windows

section CanonicalWindows

variable {K : Type} [Field K] [NumberField K] {«ω» ψ : HeckeCharacter K}
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}
variable (d : MomentData K «ω» ψ)
variable (left right : Atom (WithLp 2 (U × E)))
variable (slot : Fin d.geometry.slotCount → Atom (WithLp 2 (U × E)))
variable (hleft : PositivePlainProfile d.plainTest₁)
variable (hright : PositivePlainProfile d.plainTest₂)
variable (hslot : ∀ i, PositivePrimeProfile (d.geometry.slots i))

def positiveAnnulus (a B : ℝ) (ha : 0 < a) : Set.Icc a B ⊆ Set.Ioi 0 :=
  fun _ hy => lt_of_lt_of_le ha hy.1

/-- The common amplitude retains the real Mellin scale powers from
`profileAmplitude`.  Actual clipping adds only this fixed annular
coefficient, with no additional Fourier degree. -/
def clippedProfileAmplitude (a B : ℝ) (ha : 0 < a) (s : Finset (ℕ × ℕ)) (A : ℝ) : ℝ :=
  clippingCoefficient B s * profileAmplitude d left right slot (Set.Icc a B)
    isCompact_Icc (positiveAnnulus a B ha) s A

theorem clippedProfileAmplitude_nonneg (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B)
    (s : Finset (ℕ × ℕ)) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ clippedProfileAmplitude d left right slot a B ha s A :=
  mul_nonneg (zero_le_one.trans (clippingCoefficient_one_le B hB s))
    (profileAmplitude_nonneg d left right slot (Set.Icc a B) isCompact_Icc
      (positiveAnnulus a B ha) s hA)

/-- One actual nonzero member supplies both clipping bounds once.
Every moving profile is then normalized with the same computed
polynomial radius, before any capacity subset is removed. -/
def clippedPolynomialWindow (p : RealParameters) (Z t : ℝ) (hZ : 1 < Z)
    (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B) (s : Finset (ℕ × ℕ))
    {A : ℝ} (hA : 0 ≤ A)
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc a B) (sourceOrders s) d A)
    (hleftSupport : ∀ u v, tsupport (w.leftRep u v) ⊆ Set.Icc a B)
    (hrightSupport : ∀ u v, tsupport (w.rightRep u v) ⊆ Set.Icc a B)
    (hslotSupport : ∀ i v, tsupport (w.primeRep i v) ⊆ Set.Icc a B)
    (hrows : ∀ u ∈ pairedRows d p Z, u ∈ rowDomain) (ht : t ∈ heightDomain)
    (ξ₀ : WithLp 2 (U × E))
    (hne : pairedEnergy (data d left right slot hleft hright hslot ξ₀) p Z t ≠ 0)
    (z : U × E) :
    RawProfileWindow rowDomain heightDomain (Set.Icc (a / B) B) s
      (clipPlainData (data d left right slot hleft hright hslot (WithLp.toLp 2 z))
        p Z (zero_lt_one.trans hZ))
      (polynomialProfileRadius (clippedProfileAmplitude d left right slot a B ha s A)
        (s.sup Prod.snd) (s.sup Prod.snd) z) := by
  let M := profileAmplitude d left right slot (Set.Icc a B) isCompact_Icc
    (positiveAnnulus a B ha) s A
  have hM : 0 ≤ M := profileAmplitude_nonneg d left right slot (Set.Icc a B)
    isCompact_Icc (positiveAnnulus a B ha) s hA
  let raw := fun ξ => rawWindow d left right slot hleft hright hslot isCompact_Icc
    (positiveAnnulus a B ha) s hA w hleftSupport hrightSupport hslotSupport ξ
  have hclip := clipping_factors_le_of_window_nonzero
    (data d left right slot hleft hright hslot ξ₀) p Z t a B hZ hB s
    (M * (1 + ‖ξ₀‖) ^ (s.sup Prod.snd)) (raw ξ₀) hrows ht hne
  let clipped := clipRawWindow
    (data d left right slot hleft hright hslot (WithLp.toLp 2 z)) p Z hZ.le
    a B ha hB s (mul_nonneg hM (pow_nonneg (by positivity) _))
    (raw (WithLp.toLp 2 z)) hclip.1 hclip.2
  refine clipped.mono ?_
  have hC : 0 ≤ clippingCoefficient B s := zero_le_one.trans (clippingCoefficient_one_le B hB s)
  change clippingCoefficient B s * (M * (1 + ‖WithLp.toLp 2 z‖) ^ (s.sup Prod.snd)) ≤
    polynomialProfileRadius (clippingCoefficient B s * M) (s.sup Prod.snd) (s.sup Prod.snd) z
  calc
    _ = (clippingCoefficient B s * M) * (1 + ‖WithLp.toLp 2 z‖) ^ (s.sup Prod.snd) := by ring
    _ ≤ (clippingCoefficient B s * M) *
        ((1 + ‖z.1‖) ^ (s.sup Prod.snd) * (1 + ‖z.2‖) ^ (s.sup Prod.snd)) :=
      mul_le_mul_of_nonneg_left (hilbert_product_polynomial_le (s.sup Prod.snd) z)
        (mul_nonneg hC hM)
    _ ≤ _ := by unfold polynomialProfileRadius; linarith

theorem normalized_clipped_polynomial_window (p : RealParameters) (Z t : ℝ) (hZ : 1 < Z)
    (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B) (s : Finset (ℕ × ℕ))
    {A : ℝ} (hA : 0 ≤ A)
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc a B) (sourceOrders s) d A)
    (hleftSupport : ∀ u v, tsupport (w.leftRep u v) ⊆ Set.Icc a B)
    (hrightSupport : ∀ u v, tsupport (w.rightRep u v) ⊆ Set.Icc a B)
    (hslotSupport : ∀ i v, tsupport (w.primeRep i v) ⊆ Set.Icc a B)
    (hrows : ∀ u ∈ pairedRows d p Z, u ∈ rowDomain) (ht : t ∈ heightDomain)
    (ξ₀ : WithLp 2 (U × E))
    (hne : pairedEnergy (data d left right slot hleft hright hslot ξ₀) p Z t ≠ 0)
    (z : U × E) :
    InFixedProfileWindow rowDomain heightDomain (Set.Icc (a / B) B) s
      (normalizedMomentProfiles
        (clipPlainData (data d left right slot hleft hright hslot (WithLp.toLp 2 z))
          p Z (zero_lt_one.trans hZ))
        (polynomialProfileRadius (clippedProfileAmplitude d left right slot a B ha s A)
          (s.sup Prod.snd) (s.sup Prod.snd) z)
        (polynomialProfileRadius_pos _
          (clippedProfileAmplitude_nonneg d left right slot a B ha hB s hA) _ _ z)) :=
  normalizedMomentProfiles_in_fixed_window _
    (clippedPolynomialWindow d left right slot hleft hright hslot p Z t hZ
      a B ha hB s hA w hleftSupport hrightSupport hslotSupport hrows ht ξ₀ hne z)

end CanonicalWindows
end CanonicalLogProfiles
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.dilationSchwartz_finset_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.clipping_factors_le_of_window_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.clipRawWindow_of_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.normalized_clipped_polynomial_window
