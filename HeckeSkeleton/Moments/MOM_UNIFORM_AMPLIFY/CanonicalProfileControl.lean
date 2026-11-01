import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileNormTwists
import HeckeSkeleton.ExpansionModels.Core
import Expansion.CanonicalCutoff

/-!
# Uniform bounds for the actual canonical profile formulas

The primitive input consists of the fixed dyadic annular window, the original
one-sided cutoff, and the literal affine power in each prime window.  This
module proves the model profile bound from those formulas, uniformly in the
two independent scales, sectors, row parameters, and selected prime slots.
No moment or profile-bound conclusion is a field of the primitive input.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators ContDiff ComplexConjugate

variable {K : Type} [Field K] [NumberField K]
variable {omega ψ : HeckeCharacter K}

def dyadicSmoothAnnularTest : SmoothAnnularTest where
  toFun := Expansion.Dyadic.annularProfile
  smooth := Expansion.Dyadic.annularProfile_smooth
  lower := 1 / 2
  upper := 2
  lower_pos := by norm_num
  upper_ge := by norm_num
  support := Expansion.Dyadic.annularProfile_support

def primeSmoothAnnularTest (g : PrimeWindowGeometry) (j : Fin g.slots) :
    SmoothAnnularTest where
  toFun := (g.weight j).toFun
  smooth := (g.weight j).smooth
  lower := 1 / 2
  upper := 2
  lower_pos := by norm_num
  upper_ge := by norm_num
  support := by
    intro y hy
    have h := g.support_annular j hy
    exact ⟨by linarith [h.1], h.2.le⟩

theorem SliceControl.mono_constant {J : ℕ} {A C C' H a b T : ℝ}
    {f : ℝ → ℂ} (h : SliceControl J A C H a b T f)
    (hC : C ≤ C') (hT : 0 ≤ T) : SliceControl J A C' H a b T f := by
  exact ⟨h.1, h.2.1, h.2.2.trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (by linarith) _))⟩

private theorem euler_zero (j : ℕ) :
    eulerDerivativeOrder j (fun _ : ℝ => (0 : ℂ)) = fun _ => 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (eulerDerivative^[j + 1]) (fun _ : ℝ => (0 : ℂ)) = _
    rw [Function.iterate_succ_apply']
    change eulerDerivative (eulerDerivativeOrder j (fun _ : ℝ => (0 : ℂ))) = _
    rw [ih]
    funext y
    simp [eulerDerivative]

theorem zero_slice_control (J : ℕ) (A C H a b T : ℝ)
    (hC : 0 ≤ C) (hT : 0 ≤ T) :
    SliceControl J A C H a b T (fun _ : ℝ => (0 : ℂ)) := by
  refine ⟨contDiff_const, fun y hy => False.elim (hy rfl), ?_⟩
  have hz : testSeminorm (fun _ : ℝ => (0 : ℂ)) J A = 0 := by
    simp [testSeminorm, testIntegral, euler_zero]
  rw [hz]
  exact mul_nonneg hC (Real.rpow_nonneg (by linarith) _)

/-- Slot selection and the dyadic row exponent change no scalar profile. -/
theorem modelProfileControl_restrictSlots (d : MomentData K omega ψ)
    (I : Finset (Fin d.geometry.slotCount)) {J : ℕ} {A C H a b T : ℝ}
    (h : ModelProfileControl d J A C H a b T) :
    ModelProfileControl (d.restrictSlots I) J A C H a b T := by
  intro q
  cases q with
  | inverse u => exact h (.inverse u)
  | plain₁ u => exact h (.plain₁ u)
  | plain₂ u => exact h (.plain₂ u)
  | prime j => exact h (.prime (selectedSlotIndex I j))

theorem modelProfileControl_changeSlotBase (d : MomentData K omega ψ)
    (r : ℝ) (hr : 0 < r) {J : ℕ} {A C H a b T : ℝ}
    (h : ModelProfileControl d J A C H a b T) :
    ModelProfileControl (d.changeSlotBase r hr) J A C H a b T := by
  intro q
  cases q with
  | inverse u => exact h (.inverse u)
  | plain₁ u => exact h (.plain₁ u)
  | plain₂ u => exact h (.plain₂ u)
  | prime j => exact h (.prime j)

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)
variable (omega ψ : HeckeCharacter K) (g : PrimeWindowGeometry)

/-- Literal primitive formulas of the canonical detector family.  The
frequency multiplier is one fixed real number, with no restriction on its
size; it enters the scalar constant before any moving scale or height. -/
theorem canonical_recipe_model_profile_control
    (F : RecipeFamily K ψ g)
    (hinverse : ∀ u t y, F.inverseAnnular.profile u t y = Expansion.Dyadic.annularProfile y)
    (hplain : ∀ u t y, F.plainAnnular.profile u t y = Expansion.Dyadic.annularProfile y)
    (hcutoff : F.cutoff = Expansion.Dyadic.cutoffProfile)
    (hprime : ∀ j p, F.slotPower j p =
      conj ((17 / 50 : ℂ) + (p 2 : ℂ) * Complex.I) - 1)
    (J : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → ∀ U D : ℝ,
      0 < U → 0 ≤ D → ∀ s (ξ : RecipeVector)
        (σ τ : NonzeroIdeal K → RecipeVector),
      ‖ξ‖ ≤ T → (∀ u, ‖σ u‖ ≤ 8) → (∀ u, ‖τ u‖ ≤ 1 + ‖ξ‖) →
      ModelProfileControl (F.fullModel K S P R omega ψ g U D s ξ σ τ)
        J A C (J : ℝ) (1 / 2) 2 T ∧
      ModelProfileControl (F.inverseFamily K S P R omega ψ g U D s ξ σ τ)
        J A C (J : ℝ) (1 / 2) 2 T := by
  obtain ⟨C₀, hC₀, hb₀⟩ := annular_oneSided_cutoff_norm_twist_slice_control
    dyadicSmoothAnnularTest Expansion.Dyadic.cutoffProfile
    Expansion.Dyadic.cutoffProfile_smooth Expansion.Dyadic.cutoffProfile_one
    Expansion.Dyadic.cutoffProfile_zero 8 |F.frequencyScale|
    (by norm_num) (abs_nonneg _) J A
  obtain ⟨C₁, hC₁, hb₁⟩ := annular_norm_twist_slice_control dyadicSmoothAnnularTest
    8 |F.frequencyScale| (by norm_num) (abs_nonneg _) J A
  have hslots (j : Fin g.slots) := annular_norm_twist_slice_control
    (primeSmoothAnnularTest g j) 1 1 (by norm_num) (by norm_num) J A
  choose Cₚ hCₚ hbₚ using hslots
  let C := C₀ + C₁ + (∑ j : Fin g.slots, Cₚ j) + 1
  have hsum : 0 ≤ ∑ j : Fin g.slots, Cₚ j := Finset.sum_nonneg (fun j _ => (hCₚ j).le)
  have hC : 0 < C := by dsimp [C]; linarith
  have h₀ : C₀ ≤ C := by dsimp [C]; linarith
  have h₁ : C₁ ≤ C := by dsimp [C]; linarith
  have hpC (j : Fin g.slots) : Cₚ j ≤ C := by
    have hj : Cₚ j ≤ ∑ k : Fin g.slots, Cₚ k :=
      Finset.single_le_sum (fun k _ => (hCₚ k).le) (Finset.mem_univ j)
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro T hT U D hU hD s ξ σ τ hξ hσ hτ
  let z : NonzeroIdeal K → ℂ :=
    fun u => -(σ u 0 : ℂ) + (F.frequencyScale * τ u 0 : ℝ) * Complex.I
  have hzre (u : NonzeroIdeal K) : |(z u).re| ≤ 8 := by
    simpa [z, Real.norm_eq_abs] using (norm_le_pi_norm (σ u) 0).trans (hσ u)
  have hzim (u : NonzeroIdeal K) : |(z u).im| ≤ |F.frequencyScale| * (1 + T) := by
    have ht : |τ u 0| ≤ 1 + T := by
      have hh := (norm_le_pi_norm (τ u) 0).trans (hτ u)
      rw [Real.norm_eq_abs] at hh
      linarith
    simpa [z, abs_mul] using mul_le_mul_of_nonneg_left ht (abs_nonneg F.frequencyScale)
  have hratio : 0 ≤ D / U ^ (2 * ξ 3) :=
    div_nonneg hD (Real.rpow_pos_of_pos hU _).le
  have hi (u : NonzeroIdeal K) :
      SliceControl J A C (J : ℝ) (1 / 2) 2 T
        (fun y => F.inverseAnnular.profile u 0 y * F.cutoff ((D / U ^ (2 * ξ 3)) * y) *
          profilePower (z u) y) := by
    have h := (hb₀ T hT _ hratio (z u) (hzre u) (hzim u)).mono_constant h₀ hT
    change SliceControl J A C (J : ℝ) (1 / 2) 2 T
      (fun y => Expansion.Dyadic.annularProfile y *
        Expansion.Dyadic.cutoffProfile ((D / U ^ (2 * ξ 3)) * y) * profilePower (z u) y) at h
    simpa only [hinverse, hcutoff] using h
  have hp (u : NonzeroIdeal K) :
      SliceControl J A C (J : ℝ) (1 / 2) 2 T
        (fun y => F.plainAnnular.profile u 0 y * profilePower (z u) y) := by
    have h := (hb₁ T hT (z u) (hzre u) (hzim u)).mono_constant h₁ hT
    change SliceControl J A C (J : ℝ) (1 / 2) 2 T
      (fun y => Expansion.Dyadic.annularProfile y * profilePower (z u) y) at h
    simpa only [hplain] using h
  have hpr (j : Fin g.slots) :
      SliceControl J A C (J : ℝ) (1 / 2) 2 T
        (fun y => (g.weight j).toFun y * profilePower (F.slotPower j (recipePhysicalPoint ξ)) y) := by
    have hreal : |(F.slotPower j (recipePhysicalPoint ξ)).re| ≤ 1 := by
      rw [hprime]
      norm_num
    have himag : |(F.slotPower j (recipePhysicalPoint ξ)).im| ≤ 1 * (1 + T) := by
      have hcoord := (norm_le_pi_norm ξ 2).trans hξ
      rw [hprime]
      simpa only [recipePhysicalPoint, Complex.sub_im, Complex.conj_im, Complex.add_im,
        Complex.ofReal_im, zero_add, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, mul_one, mul_zero, add_zero, Complex.one_im, sub_zero,
        abs_neg, one_mul, Real.norm_eq_abs] using hcoord.trans (by linarith : T ≤ 1 + T)
    have h := (hbₚ j T hT _ hreal himag).mono_constant (hpC j) hT
    exact h
  constructor
  · intro q
    cases q with
    | inverse u => exact hi u
    | plain₁ u => exact hp u
    | plain₂ u => exact hp u
    | prime j => exact hpr j
  · intro q
    cases q with
    | inverse u => exact hi u
    | plain₁ u => exact zero_slice_control J A C (J : ℝ) (1 / 2) 2 T hC.le hT
    | plain₂ u => exact zero_slice_control J A C (J : ℝ) (1 / 2) 2 T hC.le hT
    | prime j => exact Fin.elim0 j

end HeckeSkeleton.Moments.UniformAmplify

#print axioms HeckeSkeleton.Moments.UniformAmplify.canonical_recipe_model_profile_control
