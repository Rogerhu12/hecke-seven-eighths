import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFamilyIntegrability

/-!
# The low-level profile-scaling dependency and its actual normalization

This module records the low-level scaling interface independently of
the capacity construction. `CanonicalProfileNormalizationInput` supplies
its concrete instance using `NormalizedMomentProfiles` and the exact
finite-polynomial homogeneity theorem. No moment estimate, whole-family
admissibility, or uniform Fourier bound is among the fields.

Raw windows below are literal Schwartz representatives of every inverse,
plain and prime profile. Their finite seminorm supremum may grow with the
Fourier parameter. Dividing by the positive envelope places every such
profile in one fixed unit ball without changing any arithmetic data or
formal length. The exact removed-slot factor is retained separately.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Precisely the scalar identities of the profile owner. All energy
statements are exact homogeneity identities for the canonical energy. -/
structure ProfileNormalizationInput (K : Type) [Field K] [NumberField K]
    (ω ψ : HeckeCharacter K) where
  scaleData : (d : MomentData K ω ψ) → (c : ℝ) → 0 < c → MomentData K ω ψ
  slotCount : ∀ d c hc, (scaleData d c hc).geometry.slotCount = d.geometry.slotCount
  slotEquiv : ∀ d c hc,
    Fin (scaleData d c hc).geometry.slotCount ≃ Fin d.geometry.slotCount
  slotLength : ∀ d c hc i, ((scaleData d c hc).geometry.slots i).length =
    (d.geometry.slots (slotEquiv d c hc i)).length
  totalLength : ∀ d c hc, (scaleData d c hc).geometry.totalLength = d.geometry.totalLength
  fitsMesh : ∀ d c hc mesh,
    (scaleData d c hc).geometry.fitsMesh mesh ↔ d.geometry.fitsMesh mesh
  rows : ∀ d c hc, (scaleData d c hc).rows = d.rows
  allowedRow : ∀ d c hc, (scaleData d c hc).allowedRow = d.allowedRow
  commonMask : ∀ d c hc, (scaleData d c hc).commonMask = d.commonMask
  rowCharacter : ∀ d c hc, (scaleData d c hc).rowCharacter = d.rowCharacter
  theta : ∀ d c hc, (scaleData d c hc).theta = d.theta
  direction : ∀ d c hc, (scaleData d c hc).direction = d.direction
  inverseBackground : ∀ d c hc, (scaleData d c hc).inverseBackground = d.inverseBackground
  plainBackground : ∀ d c hc, (scaleData d c hc).plainBackground = d.plainBackground
  slotCoefficient : ∀ d c hc i,
    (scaleData d c hc).slotCoefficient i = d.slotCoefficient (slotEquiv d c hc i)
  inverse_support : ∀ d c hc, (scaleData d c hc).inverseTest.support = d.inverseTest.support
  plain₁_support : ∀ d c hc, (scaleData d c hc).plainTest₁.support = d.plainTest₁.support
  plain₂_support : ∀ d c hc, (scaleData d c hc).plainTest₂.support = d.plainTest₂.support
  prime_support : ∀ d c hc i,
    ((scaleData d c hc).geometry.slots i).support =
      (d.geometry.slots (slotEquiv d c hc i)).support
  inverse_profile : ∀ d c hc u t y,
    (scaleData d c hc).inverseTest.profile u t y = (c : ℂ) * d.inverseTest.profile u t y
  plain₁_profile : ∀ d c hc u t y,
    (scaleData d c hc).plainTest₁.profile u t y = (c : ℂ) * d.plainTest₁.profile u t y
  plain₂_profile : ∀ d c hc u t y,
    (scaleData d c hc).plainTest₂.profile u t y = (c : ℂ) * d.plainTest₂.profile u t y
  prime_profile : ∀ d c hc i t y,
    ((scaleData d c hc).geometry.slots i).profile t y =
      (c : ℂ) * (d.geometry.slots (slotEquiv d c hc i)).profile t y
  energy_scale : ∀ d p c hc Z t,
    pairedEnergy (scaleData d c hc) p Z t =
      c ^ ((d.geometry.slotCount + 2) * 2) * pairedEnergy d p Z t

/-- Original single-profile windows. The bound is allowed to depend on
the external Fourier parameter; the support window and seminorms do not. -/
structure RawProfileWindow (rowDomain : Set (NonzeroIdeal K))
    (heightDomain window : Set ℝ) (s : Finset (ℕ × ℕ))
    (d : MomentData K ω ψ) (A : ℝ) where
  inverseRep : NonzeroIdeal K → ℝ → 𝓢(ℝ, ℂ)
  leftRep : NonzeroIdeal K → ℝ → 𝓢(ℝ, ℂ)
  rightRep : NonzeroIdeal K → ℝ → 𝓢(ℝ, ℂ)
  primeRep : Fin d.geometry.slotCount → ℝ → 𝓢(ℝ, ℂ)
  inverse_eq : ∀ u t y, d.inverseTest.profile u t y = inverseRep u t y
  left_eq : ∀ u t y, d.plainTest₁.profile u t y = leftRep u t y
  right_eq : ∀ u t y, d.plainTest₂.profile u t y = rightRep u t y
  prime_eq : ∀ i t y, (d.geometry.slots i).profile t y = primeRep i t y
  inverse_support : ∀ u ∈ rowDomain, ∀ t ∈ heightDomain, Function.support (inverseRep u t) ⊆ window
  left_support : ∀ u ∈ rowDomain, ∀ t ∈ heightDomain, Function.support (leftRep u t) ⊆ window
  right_support : ∀ u ∈ rowDomain, ∀ t ∈ heightDomain, Function.support (rightRep u t) ⊆ window
  prime_support : ∀ i, ∀ t ∈ heightDomain, Function.support (primeRep i t) ⊆ window
  inverse_bound : ∀ u ∈ rowDomain, ∀ t ∈ heightDomain, s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (inverseRep u t) ≤ A
  left_bound : ∀ u ∈ rowDomain, ∀ t ∈ heightDomain, s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (leftRep u t) ≤ A
  right_bound : ∀ u ∈ rowDomain, ∀ t ∈ heightDomain, s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (rightRep u t) ≤ A
  prime_bound : ∀ i, ∀ t ∈ heightDomain, s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (primeRep i t) ≤ A

def RawProfileWindow.mono {rowDomain : Set (NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {s : Finset (ℕ × ℕ)}
    {d : MomentData K ω ψ} {A B : ℝ} (w : RawProfileWindow rowDomain heightDomain window s d A)
    (hAB : A ≤ B) : RawProfileWindow rowDomain heightDomain window s d B :=
  { w with
    inverse_bound := fun u hu t ht => (w.inverse_bound u hu t ht).trans hAB
    left_bound := fun u hu t ht => (w.left_bound u hu t ht).trans hAB
    right_bound := fun u hu t ht => (w.right_bound u hu t ht).trans hAB
    prime_bound := fun i t ht => (w.prime_bound i t ht).trans hAB }

/-- This is a concrete fixed analytic family, not an arbitrary
admissibility predicate supplied for all moving children. -/
def InFixedProfileWindow (rowDomain : Set (NonzeroIdeal K))
    (heightDomain window : Set ℝ) (s : Finset (ℕ × ℕ))
    (d : MomentData K ω ψ) : Prop := Nonempty (RawProfileWindow rowDomain heightDomain window s d 1)

namespace ProfileNormalizationInput

variable (P : ProfileNormalizationInput K ω ψ)

def normalizeData (d : MomentData K ω ψ) (A : ℝ) (hA : 0 < A) : MomentData K ω ψ :=
  P.scaleData d A⁻¹ (inv_pos.mpr hA)

theorem normalized_count (d : MomentData K ω ψ) (A : ℝ) (hA : 0 < A) :
    (P.normalizeData d A hA).geometry.slotCount = d.geometry.slotCount :=
  P.slotCount d A⁻¹ (inv_pos.mpr hA)

/-- A genuine normalized profile lies in the original fixed support
window and finite seminorm unit ball. Scalar homogeneity here is over ℂ,
while the strictly positive envelope and its norm are real. -/
def normalizeWindow {rowDomain : Set (NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {s : Finset (ℕ × ℕ)}
    {d : MomentData K ω ψ} {A : ℝ} (hA : 0 < A)
    (w : RawProfileWindow rowDomain heightDomain window s d A) :
    RawProfileWindow rowDomain heightDomain window s (P.normalizeData d A hA) 1 := by
  have hbound (φ : 𝓢(ℝ, ℂ))
      (hφ : s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤ A) :
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (((A⁻¹ : ℝ) : ℂ) • φ) ≤ 1 := by
    rw [map_smul_eq_mul, Complex.norm_of_nonneg (inv_pos.mpr hA).le]
    exact (mul_le_mul_of_nonneg_left hφ (inv_pos.mpr hA).le).trans_eq
      (inv_mul_cancel₀ hA.ne')
  refine
    { inverseRep := fun u t => ((A⁻¹ : ℝ) : ℂ) • w.inverseRep u t
      leftRep := fun u t => ((A⁻¹ : ℝ) : ℂ) • w.leftRep u t
      rightRep := fun u t => ((A⁻¹ : ℝ) : ℂ) • w.rightRep u t
      primeRep := fun i t => ((A⁻¹ : ℝ) : ℂ) •
        w.primeRep (P.slotEquiv d A⁻¹ (inv_pos.mpr hA) i) t
      inverse_eq := ?_
      left_eq := ?_
      right_eq := ?_
      prime_eq := ?_
      inverse_support := ?_
      left_support := ?_
      right_support := ?_
      prime_support := ?_
      inverse_bound := fun u hu t ht => hbound _ (w.inverse_bound u hu t ht)
      left_bound := fun u hu t ht => hbound _ (w.left_bound u hu t ht)
      right_bound := fun u hu t ht => hbound _ (w.right_bound u hu t ht)
      prime_bound := fun i t ht => hbound _ (w.prime_bound _ t ht) }
  · intro u t y
    change (P.scaleData d A⁻¹ (inv_pos.mpr hA)).inverseTest.profile u t y =
      ((A⁻¹ : ℝ) : ℂ) * w.inverseRep u t y
    rw [P.inverse_profile, w.inverse_eq]
  · intro u t y
    change (P.scaleData d A⁻¹ (inv_pos.mpr hA)).plainTest₁.profile u t y =
      ((A⁻¹ : ℝ) : ℂ) * w.leftRep u t y
    rw [P.plain₁_profile, w.left_eq]
  · intro u t y
    change (P.scaleData d A⁻¹ (inv_pos.mpr hA)).plainTest₂.profile u t y =
      ((A⁻¹ : ℝ) : ℂ) * w.rightRep u t y
    rw [P.plain₂_profile, w.right_eq]
  · intro i t y
    change ((P.scaleData d A⁻¹ (inv_pos.mpr hA)).geometry.slots i).profile t y =
      ((A⁻¹ : ℝ) : ℂ) * w.primeRep (P.slotEquiv d A⁻¹ (inv_pos.mpr hA) i) t y
    rw [P.prime_profile, w.prime_eq]
  · intro u hu t ht y hy
    apply w.inverse_support u hu t ht
    exact right_ne_zero_of_mul hy
  · intro u hu t ht y hy
    apply w.left_support u hu t ht
    exact right_ne_zero_of_mul hy
  · intro u hu t ht y hy
    apply w.right_support u hu t ht
    exact right_ne_zero_of_mul hy
  · intro i t ht y hy
    apply w.prime_support _ t ht
    exact right_ne_zero_of_mul hy

theorem normalized_in_fixed_window {rowDomain : Set (NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {s : Finset (ℕ × ℕ)}
    {d : MomentData K ω ψ} {A : ℝ} (hA : 0 < A)
    (w : RawProfileWindow rowDomain heightDomain window s d A) :
    InFixedProfileWindow rowDomain heightDomain window s (P.normalizeData d A hA) :=
  ⟨P.normalizeWindow hA w⟩

theorem normalized_energy (d : MomentData K ω ψ) (p : RealParameters)
    (A : ℝ) (hA : 0 < A) (Z t : ℝ) :
    normalizedPairedEnergy (P.normalizeData d A hA) p Z t =
      A⁻¹ ^ ((d.geometry.slotCount + 2) * 2) * normalizedPairedEnergy d p Z t := by
  unfold normalizedPairedEnergy normalizeData
  rw [P.energy_scale]
  ring

theorem energy_recover (d : MomentData K ω ψ) (p : RealParameters)
    (A : ℝ) (hA : 0 < A) (Z t : ℝ) :
    normalizedPairedEnergy d p Z t =
      A ^ ((d.geometry.slotCount + 2) * 2) *
        normalizedPairedEnergy (P.normalizeData d A hA) p Z t := by
  rw [P.normalized_energy, inv_pow, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hA.ne'), one_mul]

theorem sqrt_energy_recover (d : MomentData K ω ψ) (p : RealParameters)
    (A : ℝ) (hA : 0 < A) (Z t : ℝ) :
    Real.sqrt (normalizedPairedEnergy d p Z t) =
      A ^ (d.geometry.slotCount + 2) *
        Real.sqrt (normalizedPairedEnergy (P.normalizeData d A hA) p Z t) := by
  rw [P.energy_recover d p A hA Z t, pow_mul,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hA.le _)]

end ProfileNormalizationInput

/-- Removing slots with raw bounds A² Bᵢ and then normalizing the live
profiles pays exactly the original degree, including when no slot lives. -/
theorem removed_profile_envelope_degree {ι : Type*}
    (removed : Finset ι) (bounds : ι → ℝ) (A : ℝ) (live total : ℕ)
    (hcount : removed.card + live = total) :
    (∏ i ∈ removed, A ^ 2 * bounds i) * A ^ ((live + 2) * 2) =
      A ^ ((total + 2) * 2) * (∏ i ∈ removed, bounds i) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  calc
    _ = A ^ (2 * removed.card + (live + 2) * 2) *
        (∏ i ∈ removed, bounds i) := by rw [pow_add, pow_mul]; ring
    _ = _ := by
      have he : 2 * removed.card + (live + 2) * 2 = (total + 2) * 2 := by omega
      rw [he]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ProfileNormalizationInput.normalized_in_fixed_window
#print axioms HeckeSkeleton.Moments.EngineStep.ProfileNormalizationInput.sqrt_energy_recover
#print axioms HeckeSkeleton.Moments.EngineStep.removed_profile_envelope_degree
