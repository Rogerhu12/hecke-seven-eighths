import HeckeSkeleton.HeckeUniformBufferedControl
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
Finite-order physical row characters preserve the infinity type of every
fixed continuous unitary background. Taking a finite sum of the resulting
constants gives one buffered estimate for a finite background family.
No finite-order restriction is imposed on the backgrounds themselves.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HeckeFiniteBackgroundControl

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Bridge HeckeGeneral.Analysis
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.HeckeBufferedReciprocal HeckeSkeleton.HeckeUniformBufferedControl
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The physical root-of-unity hypothesis supplies the totally complex field
condition, without any additional restriction on a continuous character. -/
theorem all_complex_of_primitive12 {ζ : K} (hζ : IsPrimitiveRoot ζ 12) :
    ∀ v : InfinitePlace K, v.IsComplex := by
  have hz : InfinitePlace.nrRealPlaces K = 0 :=
    InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by norm_num) hζ
  exact (NumberField.nrRealPlaces_eq_zero_iff.mp hz).isComplex

theorem radialParameters_mul_finiteOrder (β χ : HeckeCharacter K) (hχ : FiniteOrder χ) :
    (fun v => heckeRadialParameter K v (β * χ)) =
      (fun v => heckeRadialParameter K v β) := by
  funext v
  rw [heckeRadialParameter_mul, heckeRadialParameter_finiteOrder K v hχ, add_zero]

theorem archWeight_mul_finiteOrder_of_complex
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (β χ : HeckeCharacter K) (hχ : FiniteOrder χ) :
    heckeArchWeight K (β * χ) = heckeArchWeight K β := by
  funext v
  rw [heckeArchWeight_of_complex K (β * χ) v (hcomplex v),
    heckeArchWeight_of_complex K β v (hcomplex v), heckeComplexWeight_mul,
    heckeComplexWeight_finiteOrder K v (hcomplex v) hχ, add_zero]

/-- One constant covers all finite-order row factors and all members of a
fixed finite family of arbitrary continuous unitary backgrounds. Apply it
also with chi^{-1} for the conjugate orientation of a physical row. -/
theorem exists_uniform_finiteBackground_buffered_control
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (B : Finset (HeckeCharacter K))
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ β ∈ B, ∀ χ : HeckeCharacter K, FiniteOrder χ →
      ∀ a H Hupper : ℝ,
      (∀ t : ℝ, β * χ ≠ heckeNormTwist K t) →
      1 / 2 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ Hupper →
      ZeroUpperBound K (β * χ) Hupper (a + 2 * e) →
      ∀ s : ℂ, a + 6 * e ≤ s.re → s.re ≤ 2 → |s.im| ≤ H →
        ‖heckeContinuation K (β * χ) s‖ + ‖(heckeContinuation K (β * χ) s)⁻¹‖ ≤
          D * heckeConductorScale K (β * χ) ^ ε *
            (2 + Hupper) ^ ((2 * Fintype.card (InfinitePlace K) : ℕ) * ε) := by
  have hlocal := fun β : B => exists_uniform_fixedType_buffered_control K hcomplex
    (fun v => heckeRadialParameter K v β.val) (heckeArchWeight K β.val) he he' hε
  choose D hDpos hD using hlocal
  let D₀ : ℝ := (∑ β : B, D β) + 1
  have hD₀ : 0 < D₀ := by
    have hsum : 0 ≤ ∑ β : B, D β :=
      Finset.sum_nonneg (fun β _ => (hDpos β).le)
    exact hsum.trans_lt (lt_add_one _)
  refine ⟨D₀, hD₀, ?_⟩
  intro β hβ χ hχ a H Hupper hnon ha ha' hH hpadding hupper s hs hs' hheight
  have hb := hD (⟨β, hβ⟩ : B) (β * χ) a H Hupper hnon
    (radialParameters_mul_finiteOrder K β χ hχ)
    (archWeight_mul_finiteOrder_of_complex K hcomplex β χ hχ)
    ha ha' hH hpadding hupper s hs hs' hheight
  have hDb : D (⟨β, hβ⟩ : B) ≤ D₀ := by
    have hsingle : D (⟨β, hβ⟩ : B) ≤ ∑ η : B, D η :=
      Finset.single_le_sum (f := fun η : B => D η)
        (s := (Finset.univ : Finset B)) (a := (⟨β, hβ⟩ : B))
        (fun η _ => (hDpos η).le) (Finset.mem_univ _)
    exact hsingle.trans (le_add_of_nonneg_right (by norm_num))
  have hHU : 0 ≤ Hupper := by linarith
  have hQ : 0 ≤ heckeConductorScale K (β * χ) := by
    unfold heckeConductorScale
    positivity
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hDb (Real.rpow_nonneg hQ _))
      (Real.rpow_nonneg (by linarith : 0 ≤ 2 + Hupper) _))

end HeckeSkeleton.HeckeFiniteBackgroundControl
