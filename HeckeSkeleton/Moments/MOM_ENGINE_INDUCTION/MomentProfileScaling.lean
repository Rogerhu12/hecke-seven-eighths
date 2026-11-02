import HeckeGeneral.Analysis.MomentInputs
import Mathlib.Algebra.BigOperators.Fin

/-!
# Scalar normalization of literal moment polynomials

This low-level module imports only the actual polynomial definitions. It
has no dependency on the induction interface or any engine-step module,
so the analytic producer can consume the same proved normalization without
creating a circular import. All supports, rows, characters, masks, lengths
and slot counts remain literal; only the analytic profiles are scaled.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open scoped BigOperators Classical

variable {K : Type} [Field K] [NumberField K]

/-- A positive scalar leaves the test's exact original ideal support intact. -/
def scaledIdealTest (W : IdealTest K) (a : ℝ) (ha : 0 < a) : IdealTest K where
  profile u t y := (a : ℂ) * W.profile u t y
  support := W.support
  support_spec u t D I := by
    rw [W.support_spec]
    constructor
    · intro h
      exact mul_ne_zero (by exact_mod_cast ha.ne') h
    · exact right_ne_zero_of_mul

/-- Prime scaling is independent of the row and retains the actual length. -/
def scaledPrimeWindow (W : PrimeWindow K) (a : ℝ) (ha : 0 < a) : PrimeWindow K where
  length := W.length
  length_pos := W.length_pos
  profile t y := (a : ℂ) * W.profile t y
  support := W.support
  support_spec t P p := by
    rw [W.support_spec]
    constructor
    · intro h
      exact mul_ne_zero (by exact_mod_cast ha.ne') h
    · exact right_ne_zero_of_mul

def scaledGeometry (g : SlotGeometry K) (a : ℝ) (ha : 0 < a) : SlotGeometry K where
  slotCount := g.slotCount
  slots i := scaledPrimeWindow (g.slots i) a ha

variable {ω ψ : HeckeCharacter K}

/-- Scale all analytic profiles, retaining every arithmetic field literally. -/
def scaledMomentProfiles (d : MomentData K ω ψ) (a : ℝ) (ha : 0 < a) :
    MomentData K ω ψ :=
  { d with
    inverseTest := scaledIdealTest d.inverseTest a ha
    plainTest₁ := scaledIdealTest d.plainTest₁ a ha
    plainTest₂ := scaledIdealTest d.plainTest₂ a ha
    geometry := scaledGeometry d.geometry a ha }

theorem scaledIdealTest_profile_support (W : IdealTest K) (a : ℝ) (ha : 0 < a)
    (u : NonzeroIdeal K) (t : ℝ) :
    Function.support ((scaledIdealTest W a ha).profile u t) =
      Function.support (W.profile u t) := by
  ext y
  change (a : ℂ) * W.profile u t y ≠ 0 ↔ W.profile u t y ≠ 0
  exact ⟨right_ne_zero_of_mul, mul_ne_zero (by exact_mod_cast ha.ne')⟩

theorem scaledPrimeWindow_profile_support (W : PrimeWindow K) (a : ℝ) (ha : 0 < a)
    (t : ℝ) :
    Function.support ((scaledPrimeWindow W a ha).profile t) =
      Function.support (W.profile t) := by
  ext y
  change (a : ℂ) * W.profile t y ≠ 0 ↔ W.profile t y ≠ 0
  exact ⟨right_ne_zero_of_mul, mul_ne_zero (by exact_mod_cast ha.ne')⟩

/-- The row predicate and every zero mask remain the original ones. The
same data also retain their total slot length and every mesh bound. -/
theorem scaledMomentProfiles_invariants (d : MomentData K ω ψ) (a : ℝ) (ha : 0 < a) :
    (scaledMomentProfiles d a ha).rows = d.rows ∧
    (scaledMomentProfiles d a ha).allowedRow = d.allowedRow ∧
    (scaledMomentProfiles d a ha).commonMask = d.commonMask ∧
    (scaledMomentProfiles d a ha).rowCharacter = d.rowCharacter ∧
    (scaledMomentProfiles d a ha).theta = d.theta ∧
    (scaledMomentProfiles d a ha).inverseBackground = d.inverseBackground ∧
    (scaledMomentProfiles d a ha).plainBackground = d.plainBackground ∧
    (scaledMomentProfiles d a ha).slotCoefficient = d.slotCoefficient ∧
    (scaledMomentProfiles d a ha).geometry.slotCount = d.geometry.slotCount ∧
    (∀ i, ((scaledMomentProfiles d a ha).geometry.slots i).length =
      (d.geometry.slots i).length) ∧
    (scaledMomentProfiles d a ha).geometry.totalLength = d.geometry.totalLength ∧
    (∀ mesh, (scaledMomentProfiles d a ha).geometry.fitsMesh mesh ↔
      d.geometry.fitsMesh mesh) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, fun _ => Iff.rfl⟩

@[simp] theorem pairedRows_scaledMomentProfiles (d : MomentData K ω ψ)
    (a : ℝ) (ha : 0 < a) (p : RealParameters) (U : ℝ) :
    pairedRows (scaledMomentProfiles d a ha) p U = pairedRows d p U := rfl

private theorem mul_sum_scaled_profile {ι : Type*} (s : Finset ι)
    (p c : ℂ) (f g h : ι → ℂ) :
    p * (∑ i ∈ s, f i * (c * g i) * h i) =
      c * (p * ∑ i ∈ s, f i * g i * h i) := by
  calc
    _ = p * (c * ∑ i ∈ s, f i * g i * h i) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by ring

/-- The inverse polynomial, including its actual Moebius coefficient and
integer orientation, is linear in its own ideal profile. -/
theorem inversePolynomial_scaledMomentProfiles (d : MomentData K ω ψ)
    (a : ℝ) (ha : 0 < a) (u : NonzeroIdeal K) (D t : ℝ) :
    inversePolynomial (scaledMomentProfiles d a ha) u D t =
      (a : ℂ) * inversePolynomial d u D t := by
  exact mul_sum_scaled_profile (d.inverseTest.support u t D)
    (Real.sqrt D : ℂ)⁻¹ (a : ℂ)
    (fun I => (UniqueFactorizationMonoid.moebius I.val : ℂ) *
      heckeIdealCoefficient K d.inverseBackground I *
      heckeIdealCoefficient K (d.rowCharacter u) I ^ d.direction)
    (fun I => d.inverseTest.profile u t (idealNorm K I / D))
    (fun I => maskValue d u I.val)

theorem plainPolynomial_scaledMomentProfiles (d : MomentData K ω ψ)
    (W : IdealTest K) (a : ℝ) (ha : 0 < a) (u : NonzeroIdeal K) (N t : ℝ) :
    plainPolynomial (scaledMomentProfiles d a ha) (scaledIdealTest W a ha) u N t =
      (a : ℂ) * plainPolynomial d W u N t := by
  exact mul_sum_scaled_profile (W.support u t N) (Real.sqrt N : ℂ)⁻¹ (a : ℂ)
    (fun I => heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I)
    (fun I => W.profile u t (idealNorm K I / N)) (fun I => maskValue d u I.val)

theorem primePolynomial_scaledMomentProfiles (d : MomentData K ω ψ)
    (a : ℝ) (ha : 0 < a) (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (U t : ℝ) :
    primePolynomial (scaledMomentProfiles d a ha) i u U t =
      (a : ℂ) * primePolynomial d i u U t := by
  exact mul_sum_scaled_profile
    ((d.geometry.slots i).support t (U ^ (d.geometry.slots i).length))
    (Real.sqrt (U ^ (d.geometry.slots i).length) : ℂ)⁻¹ (a : ℂ)
    (fun p => primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p)
    (fun p => (d.geometry.slots i).profile t
      ((Ideal.absNorm p.asIdeal : ℝ) / U ^ (d.geometry.slots i).length))
    (fun p => maskValue d u p.asIdeal)

theorem slotProduct_scaledMomentProfiles (d : MomentData K ω ψ)
    (a : ℝ) (ha : 0 < a) (u : NonzeroIdeal K) (U t : ℝ) :
    slotProduct (scaledMomentProfiles d a ha) u U t =
      (a : ℂ) ^ d.geometry.slotCount * slotProduct d u U t := by
  change (∏ i : Fin d.geometry.slotCount,
    primePolynomial (scaledMomentProfiles d a ha) i u U t) =
      (a : ℂ) ^ d.geometry.slotCount *
        (∏ i : Fin d.geometry.slotCount, primePolynomial d i u U t)
  simp only [primePolynomial_scaledMomentProfiles, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] <;> rfl

/-- The complete ordinary paired energy has the exact profile degree;
no row bound, induction interface or moment estimate is used. -/
theorem pairedEnergy_scaledMomentProfiles (d : MomentData K ω ψ) (p : RealParameters)
    (a : ℝ) (ha : 0 < a) (U t : ℝ) :
    pairedEnergy (scaledMomentProfiles d a ha) p U t =
      a ^ ((d.geometry.slotCount + 2) * 2) * pairedEnergy d p U t := by
  unfold pairedEnergy
  rw [pairedRows_scaledMomentProfiles, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  change ‖plainPolynomial (scaledMomentProfiles d a ha) (scaledIdealTest d.plainTest₁ a ha)
      u (U ^ p.n₁) t *
    plainPolynomial (scaledMomentProfiles d a ha) (scaledIdealTest d.plainTest₂ a ha)
      u (U ^ p.n₂) t * slotProduct (scaledMomentProfiles d a ha) u U t‖ ^ 2 = _
  rw [plainPolynomial_scaledMomentProfiles, plainPolynomial_scaledMomentProfiles,
    slotProduct_scaledMomentProfiles]
  have hamp :
      ((a : ℂ) * plainPolynomial d d.plainTest₁ u (U ^ p.n₁) t) *
        ((a : ℂ) * plainPolynomial d d.plainTest₂ u (U ^ p.n₂) t) *
        ((a : ℂ) ^ d.geometry.slotCount * slotProduct d u U t) =
      (a : ℂ) ^ (d.geometry.slotCount + 2) *
        (plainPolynomial d d.plainTest₁ u (U ^ p.n₁) t *
          plainPolynomial d d.plainTest₂ u (U ^ p.n₂) t * slotProduct d u U t) := by
    rw [pow_add]
    ring
  rw [hamp, norm_mul, norm_pow, Complex.norm_of_nonneg ha.le, mul_pow, ← pow_mul]

/-- Extract the exact ordinary child energy envelope without importing
the induction's node type. -/
theorem pairedEnergy_normalizedMomentProfiles (d : MomentData K ω ψ) (p : RealParameters)
    (A : ℝ) (hA : 0 < A) (U t : ℝ) :
    pairedEnergy d p U t = A ^ ((d.geometry.slotCount + 2) * 2) *
      pairedEnergy (scaledMomentProfiles d A⁻¹ (inv_pos.mpr hA)) p U t := by
  rw [pairedEnergy_scaledMomentProfiles, inv_pow, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hA.ne'), one_mul]

/-- Each side of the actual Cauchy kernel contributes its own half-degree
envelope; their product is charged once to the original common measure. -/
theorem sqrt_pairedEnergy_normalizedMomentProfiles
    (d : MomentData K ω ψ) (p : RealParameters) (A : ℝ) (hA : 0 < A) (U t : ℝ) :
    Real.sqrt (pairedEnergy d p U t) = A ^ (d.geometry.slotCount + 2) *
      Real.sqrt (pairedEnergy (scaledMomentProfiles d A⁻¹ (inv_pos.mpr hA)) p U t) := by
  rw [pairedEnergy_normalizedMomentProfiles d p A hA U t, pow_mul,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hA.le _)]

end HeckeSkeleton.Moments.EngineInduction
