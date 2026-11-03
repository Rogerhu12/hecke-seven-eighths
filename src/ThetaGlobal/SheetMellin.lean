import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Mellin factorization after norm-sheet disintegration

There are two concrete measure changes: the norm-sheet splitting and the
product of local factors. Their measure-preserving assertions are exactly
the Haar/disintegration data already carried by the actual source. The
only function identity assumed is a pointwise finite tensor expansion;
the Mellin integral identity is proved by absolute Fubini.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.SheetMellin

open MeasureTheory
open scoped BigOperators

variable {T X G : Type*} [MeasurableSpace T] [MeasurableSpace X] [MeasurableSpace G]
  {ν : Measure T} {μ : Measure X} {ξ : Measure G} [SigmaFinite ν] [SigmaFinite μ]

def sheetProfile (e : T × X ≃ᵐ G) (W : G → ℂ) (t : T) : ℂ :=
  ∫ x, W (e (t, x)) ∂μ

/-- Integrating a sheet profile against the norm weight is exactly the
weighted group integral. All Fubini steps follow from the displayed L1
condition on the original group, before any factorization is used. -/
theorem sheet_transform_eq_global
    (e : T × X ≃ᵐ G) (he : MeasurePreserving e (ν.prod μ) ξ)
    (normCoordinate : G → T) (hnorm : ∀ z, normCoordinate (e z) = z.1)
    (weight : T → ℂ) (W : G → ℂ)
    (hW : Integrable (fun g => weight (normCoordinate g) * W g) ξ) :
    (∫ t, weight t * sheetProfile (μ := μ) e W t ∂ν) =
      ∫ g, weight (normCoordinate g) * W g ∂ξ := by
  have hi : Integrable (fun z : T × X => weight z.1 * W (e z)) (ν.prod μ) := by
    have h := he.integrable_comp_of_integrable hW
    apply h.congr
    exact Filter.Eventually.of_forall fun z => by simp only [Function.comp_apply, hnorm]
  calc
    _ = ∫ t, ∫ x, weight t * W (e (t, x)) ∂μ ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => (integral_const_mul (weight t) _).symm
    _ = ∫ z : T × X, weight z.1 * W (e z) ∂(ν.prod μ) :=
      (integral_prod _ hi).symm
    _ = ∫ z : T × X, weight (normCoordinate (e z)) * W (e z) ∂(ν.prod μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change weight z.1 * W (e z) = weight (normCoordinate (e z)) * W (e z)
        rw [hnorm]
    _ = ∫ g, weight (normCoordinate g) * W g ∂ξ :=
      he.integral_comp' (fun g : G => weight (normCoordinate g) * W g)

variable {P J : Type*} [Fintype P] [Fintype J]
  {Y : P → Type*} [∀ p, MeasurableSpace (Y p)]
  (localMeasure : ∀ p, Measure (Y p)) [∀ p, SigmaFinite (localMeasure p)]

/-- A finite sum of local tensor products is globally integrable as soon
as its individual local factors are integrable. -/
theorem finite_tensor_integrable
    (φ : G ≃ᵐ (∀ p, Y p)) (hφ : MeasurePreserving φ ξ (Measure.pi localMeasure))
    (f : J → ∀ p, Y p → ℂ) (hf : ∀ j p, Integrable (f j p) (localMeasure p))
    (W : G → ℂ) (hW : ∀ g, W g = ∑ j, ∏ p, f j p (φ g p)) :
    Integrable W ξ := by
  have hi : Integrable (fun y : ∀ p, Y p => ∑ j, ∏ p, f j p (y p)) (Measure.pi localMeasure) :=
    integrable_finsetSum Finset.univ (fun j _ => Integrable.fintype_prod_dep (hf j))
  apply (hφ.integrable_comp_of_integrable hi).congr
  exact Filter.Eventually.of_forall fun g => (hW g).symm

theorem finite_tensor_integral
    (φ : G ≃ᵐ (∀ p, Y p)) (hφ : MeasurePreserving φ ξ (Measure.pi localMeasure))
    (f : J → ∀ p, Y p → ℂ) (hf : ∀ j p, Integrable (f j p) (localMeasure p))
    (W : G → ℂ) (hW : ∀ g, W g = ∑ j, ∏ p, f j p (φ g p)) :
    (∫ g, W g ∂ξ) = ∑ j, ∏ p, ∫ y, f j p y ∂localMeasure p := by
  calc
    _ = ∫ g, ∑ j, ∏ p, f j p (φ g p) ∂ξ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hW
    _ = ∫ y : ∀ p, Y p, ∑ j, ∏ p, f j p (y p) ∂Measure.pi localMeasure :=
      hφ.integral_comp' (fun y : ∀ p, Y p => ∑ j, ∏ p, f j p (y p))
    _ = ∑ j, ∫ y : ∀ p, Y p, ∏ p, f j p (y p) ∂Measure.pi localMeasure :=
      integral_finsetSum _ (fun j _ => Integrable.fintype_prod_dep (hf j))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact integral_fintype_prod_eq_prod (f j)

/-- The full sheet Mellin factorization. In the intended application
`weight t = t^s`, `f` contains the local period, norm power, class indicator
and Whittaker value, and the tensor index includes the finite class split. -/
theorem sheet_mellin_factorization
    (e : T × X ≃ᵐ G) (he : MeasurePreserving e (ν.prod μ) ξ)
    (normCoordinate : G → T) (hnorm : ∀ z, normCoordinate (e z) = z.1)
    (φ : G ≃ᵐ (∀ p, Y p)) (hφ : MeasurePreserving φ ξ (Measure.pi localMeasure))
    (weight : T → ℂ) (W : G → ℂ)
    (f : J → ∀ p, Y p → ℂ) (hf : ∀ j p, Integrable (f j p) (localMeasure p))
    (hpoint : ∀ g, weight (normCoordinate g) * W g =
      ∑ j, ∏ p, f j p (φ g p)) :
    (∫ t, weight t * sheetProfile (μ := μ) e W t ∂ν) =
      ∑ j, ∏ p, ∫ y, f j p y ∂localMeasure p := by
  have hi := finite_tensor_integrable localMeasure φ hφ f hf
    (fun g => weight (normCoordinate g) * W g) hpoint
  rw [sheet_transform_eq_global e he normCoordinate hnorm weight W hi]
  exact finite_tensor_integral localMeasure φ hφ f hf _ hpoint

end ThetaGlobal.SheetMellin

#print axioms ThetaGlobal.SheetMellin.sheet_mellin_factorization
