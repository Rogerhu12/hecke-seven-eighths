import HeckeSkeleton.HighBinSupport.FiniteResidueFourier
import Mathlib.Algebra.Group.Units.Equiv
/-!
# Sixth-unit compatibility of the actual two-layer finite convolution

A change of an allowed generator by a sixth power changes its principal
additive character by the inverse sixth-unit shift. The literal finite
sums below are invariant under those shifts. Units may be units only in
the current quotient; they need not be global S-units.

The elementary `fourier_unit_invariant` argument is the same residue
variable bijection already present in project Arithmetic/PeriodicFourier.
The two-layer convolution and its simultaneous generator/frequency
invariances are made explicit here and depend only on Mathlib.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-30.
-/

noncomputable section
namespace HighBin.GeneratorUnitInvariance
open scoped BigOperators

section OneRing
variable {R : Type*} [CommRing R] [Fintype R]

/-- Change of residue variables by an actual quotient unit. -/
theorem fourier_unit_invariant (ψ : AddChar R ℂ) (f : R → ℂ) (u : Rˣ)
    (hf : ∀ a : R, f ((u : R) * a) = f a) (h : R) :
    HighBin.FiniteResidueFourier.fourier ψ f ((u : R) * h) =
      HighBin.FiniteResidueFourier.fourier ψ f h := by
  unfold HighBin.FiniteResidueFourier.fourier
  refine Fintype.sum_bijective _ u.mulLeft_bijective _ _ (fun a => ?_)
  rw [hf]
  congr 1
  congr 1
  ring

omit [Fintype R] in
/-- Sixth-order zero-extended characters are invariant under sixth powers
of quotient units, including at nonunit arguments. -/
theorem character_sixth_unit (χ : MulChar R ℂ) (hχ : χ ^ 6 = 1)
    (u : Rˣ) (x : R) : χ ((u : R) ^ 6 * x) = χ x := by
  have hu : χ u ^ 6 = 1 := by
    rw [← MulChar.pow_apply_coe χ 6 u, hχ, MulChar.one_apply_coe]
  rw [map_mul, map_pow, hu, one_mul]

theorem fourier_sixth_unit (ψ : AddChar R ℂ) (χ : MulChar R ℂ)
    (hχ : χ ^ 6 = 1) (u : Rˣ) (h : R) :
    HighBin.FiniteResidueFourier.fourier ψ χ ((u : R) ^ 6 * h) =
      HighBin.FiniteResidueFourier.fourier ψ χ h := by
  have hf : ∀ x : R, χ (((u ^ 6 : Rˣ) : R) * x) = χ x := by
    intro x
    simpa only [Units.val_pow_eq_pow_val] using character_sixth_unit χ hχ u x
  simpa only [Units.val_pow_eq_pow_val] using fourier_unit_invariant ψ χ (u ^ 6) hf h

/-- Changing the literal denominator by a sixth unit changes the
character by such a shift; the Gauss sum itself is unchanged. -/
theorem fourier_sixth_character_shift (ψ : AddChar R ℂ) (χ : MulChar R ℂ)
    (hχ : χ ^ 6 = 1) (u : Rˣ) (h : R) :
    HighBin.FiniteResidueFourier.fourier (ψ.mulShift ((u : R) ^ 6)) χ h =
      HighBin.FiniteResidueFourier.fourier ψ χ h := by
  simpa only [HighBin.FiniteResidueFourier.fourier, AddChar.mulShift_apply, mul_assoc] using
    fourier_sixth_unit ψ χ hχ u h
end OneRing

section TwoLayer
variable {R D B : Type*} [CommRing R] [CommRing D] [CommRing B]
variable [Fintype R] [Fintype D]

/-- The normalized two-layer sum with the same quotient projections and
minus sign as the original finitePoissonFactor. -/
def finiteConvolution (πd : R →+* D) (πa : R →+* B)
    (χd : MulChar D ℂ) (χa : MulChar B ℂ)
    (ψd : AddChar D ℂ) (ψ : AddChar R ℂ) (h : R) : ℂ :=
  (Fintype.card D : ℂ)⁻¹ * HighBin.FiniteResidueFourier.fourier ψ
    (fun m => HighBin.FiniteResidueFourier.fourier ψd χd (-πd m) * χa (πa m)) h

/-- A sixth-power frequency change by a quotient unit preserves the
complete finite convolution, without dropping either zero extension. -/
theorem finiteConvolution_frequency_sixth_unit (πd : R →+* D) (πa : R →+* B)
    (χd : MulChar D ℂ) (χa : MulChar B ℂ)
    (hχd : χd ^ 6 = 1) (hχa : χa ^ 6 = 1)
    (ψd : AddChar D ℂ) (ψ : AddChar R ℂ) (u : Rˣ) (h : R) :
    finiteConvolution πd πa χd χa ψd ψ ((u : R) ^ 6 * h) =
      finiteConvolution πd πa χd χa ψd ψ h := by
  let f : R → ℂ := fun m =>
    HighBin.FiniteResidueFourier.fourier ψd χd (-πd m) * χa (πa m)
  have hf : ∀ m : R, f (((u ^ 6 : Rˣ) : R) * m) = f m := by
    intro m
    simp only [Units.val_pow_eq_pow_val]
    change HighBin.FiniteResidueFourier.fourier ψd χd (-πd ((u : R) ^ 6 * m)) *
        χa (πa ((u : R) ^ 6 * m)) = _
    rw [map_mul πd, map_pow πd, map_mul πa, map_pow πa]
    have hn : -((πd u) ^ 6 * πd m) = (πd u) ^ 6 * (-πd m) := by ring
    have hd := fourier_sixth_unit ψd χd hχd (Units.map πd.toMonoidHom u) (-πd m)
    change HighBin.FiniteResidueFourier.fourier ψd χd ((πd u) ^ 6 * (-πd m)) =
      HighBin.FiniteResidueFourier.fourier ψd χd (-πd m) at hd
    have ha := character_sixth_unit χa hχa (Units.map πa.toMonoidHom u) (πa m)
    change χa ((πa u) ^ 6 * πa m) = χa (πa m) at ha
    rw [hn, hd, ha]
  change (Fintype.card D : ℂ)⁻¹ * HighBin.FiniteResidueFourier.fourier ψ f ((u : R) ^ 6 * h) =
    (Fintype.card D : ℂ)⁻¹ * HighBin.FiniteResidueFourier.fourier ψ f h
  congr 1
  simpa only [Units.val_pow_eq_pow_val] using fourier_unit_invariant ψ f (u ^ 6) hf h

/-- The denominator Gauss character may be shifted independently. -/
theorem finiteConvolution_denominator_shift (πd : R →+* D) (πa : R →+* B)
    (χd : MulChar D ℂ) (χa : MulChar B ℂ) (hχd : χd ^ 6 = 1)
    (ψd : AddChar D ℂ) (ψ : AddChar R ℂ) (u : Dˣ) (h : R) :
    finiteConvolution πd πa χd χa (ψd.mulShift ((u : D) ^ 6)) ψ h =
      finiteConvolution πd πa χd χa ψd ψ h := by
  unfold finiteConvolution
  simp_rw [fourier_sixth_character_shift ψd χd hχd u]

/-- This is the change of the product denominator gen(d)gen(A). -/
theorem finiteConvolution_outer_shift (πd : R →+* D) (πa : R →+* B)
    (χd : MulChar D ℂ) (χa : MulChar B ℂ)
    (hχd : χd ^ 6 = 1) (hχa : χa ^ 6 = 1)
    (ψd : AddChar D ℂ) (ψ : AddChar R ℂ) (u : Rˣ) (h : R) :
    finiteConvolution πd πa χd χa ψd (ψ.mulShift ((u : R) ^ 6)) h =
      finiteConvolution πd πa χd χa ψd ψ h := by
  simpa only [finiteConvolution, HighBin.FiniteResidueFourier.fourier,
    AddChar.mulShift_apply, mul_assoc] using
    finiteConvolution_frequency_sixth_unit πd πa χd χa hχd hχa ψd ψ u h

#print axioms fourier_sixth_character_shift
#print axioms finiteConvolution_frequency_sixth_unit
#print axioms finiteConvolution_denominator_shift
#print axioms finiteConvolution_outer_shift
end TwoLayer
end HighBin.GeneratorUnitInvariance
