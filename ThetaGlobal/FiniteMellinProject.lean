import HeckeGeneral.Analysis.GlobalThetaData
import ThetaGlobal.FiniteTensorCoefficients

/-!
# Project adapter for literal finite-place shell data

This adapter deliberately does not import `HeckeSkeleton.Base` or
`HeckeSkeleton.Theta`; it does not depend on their admitted declarations.
It produces the existing `FiniteMellinData` structure from local shell data
whose κ dependence is the explicit reflected class mask.

The unresolved realization obligation is to supply these local vectors,
periods, class dictionaries and normalizations from the SAME arithmetic
choice as the marked theta period.  No global reflection identity is a
field or a hypothesis here.  The pointwise local support and decay inputs
are the finite-place KP statements, not bounds on coefficient sequences.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ProjectFiniteMellin

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.FiniteShell ThetaGlobal.FiniteClass ThetaGlobal.FiniteTensor
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable {Tensor : Type} [Fintype Tensor]
variable {Class : S → Type} [∀ p, Fintype (Class p)]
variable {Point UnitSpace : S → Type} [∀ p, MeasurableSpace (UnitSpace p)]

variable (B : Set (SixthLocalClasses K S))
variable (H : SixthLocalClasses K S → SixthLocalClasses K S → ℂ)
variable (hH : ∀ x y, ‖H x y‖ ≤ 1)
variable (assemble : (∀ p, Class p) → SixthLocalClasses K S)
variable (pivot : S)
variable (classOf : ∀ p, Point p → Class p)
variable (d : SixthUnitClasses K S → Tensor → ∀ p,
  LocalShellData PUnit (Point p) (UnitSpace p))
variable (μ : ∀ p, Measure (UnitSpace p)) [∀ p, IsFiniteMeasure (μ p)]
variable (C₀ : ℂ) (hC₀ : C₀ ≠ 0) (A₀ : ℝ) (hA₀ : 0 < A₀)

/-- Literal KP coefficient-table constructor.  The finite sum ranges over
raw tensor summands and all finite-place power-class tuples.  It uses no
choice of coefficients unrelated to the underlying shell integrals. -/
def finiteMellinDataOfClassShells : FiniteMellinData K S where
  terms := Fintype.card (Tensor × (∀ p, Class p))
  coefficient u κ l p k :=
    let tσ := (Fintype.equivFin (Tensor × (∀ p, Class p))).symm l
    FiniteShell.coefficient (withClassMask B H hH assemble pivot classOf p (d u tσ.1 p))
      (μ p) (κ, tσ.2) k
  C₀ := C₀
  C₀_ne_zero := hC₀
  A₀ := A₀
  A₀_pos := hA₀

local notation "F" => finiteMellinDataOfClassShells K S B H hH assemble pivot classOf d μ C₀ hC₀ A₀ hA₀

/-- Required coefficient specification.  In the application `Point p`
is `K_pˣ`, `UnitSpace p` its integral units, `shell k u = π_p^k u`,
`d.value` is the actual rotated local Whittaker vector, and `d.multiplier`
is the actual local period including its unit-sector Hilbert correction.
The allowed-class indicator and κ Hilbert square are explicit. -/
theorem coefficient_shell_spec
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (l : Fin F.terms) (p : S) (k : ℤ) :
    F.coefficient u κ l p k =
      let tσ := (Fintype.equivFin (Tensor × (∀ p, Class p))).symm l
      ∫ z, (if p = pivot then powerClassMask B H κ (assemble tσ.2) else 1) *
        (if classOf p ((d u tσ.1 p).shell k z) = tσ.2 p then 1 else 0) *
        (d u tσ.1 p).multiplier PUnit.unit k z *
        (d u tσ.1 p).value ((d u tσ.1 p).shell k z) ∂μ p := rfl

/-- TH-FINITE-VALUATION-CUTOFF for the constructed table, from pointwise
large-norm support of the finite family of actual local Whittaker vectors. -/
theorem valuation_cutoff
    (hd : ∀ u t p, LocalWhittakerBounds (d u t p)) :
    ∃ k₀ : ℤ, ∀ u κ l p k, k < k₀ → F.coefficient u κ l p k = 0 := by
  obtain ⟨k₀, hk₀⟩ := FiniteTensor.uniform_cutoff B H hH assemble pivot classOf d μ hd
  refine ⟨k₀, ?_⟩
  intro u κ l p k hk
  let tσ := (Fintype.equivFin (Tensor × (∀ p, Class p))).symm l
  exact hk₀ u tσ.1 p κ tσ.2 k hk

/-- TH-FINITE-VALUATION-DECAY, with the actual prime-ideal norms.
The normalization hypothesis identifies a local field's residue cardinality;
it is not an estimate or a coefficient conclusion. -/
theorem valuation_decay
    (hq : ∀ u t p, (d u t p).q = p.val.asIdeal.absNorm)
    (hd : ∀ u t p, LocalWhittakerBounds (d u t p)) :
    ∀ δ : ℝ, δ < 1 / 3 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ u κ l p k, 0 ≤ k →
        ‖F.coefficient u κ l p k‖ ≤ C *
          (p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * δ) := by
  intro δ hδ
  obtain ⟨C, hC, hc⟩ := FiniteTensor.uniform_decay B H hH assemble pivot classOf d μ hd δ hδ
  refine ⟨C, hC, ?_⟩
  intro u κ l p k hk
  let tσ := (Fintype.equivFin (Tensor × (∀ p, Class p))).symm l
  change ‖FiniteShell.coefficient
    (withClassMask B H hH assemble pivot classOf p (d u tσ.1 p)) (μ p) (κ, tσ.2) k‖ ≤ _
  simpa only [hq] using hc u tσ.1 p κ tσ.2 k hk

/-- All finite-Mellin admissibility fields follow for the same constructed
coefficient table.  No further Mellin-convergence assumption is required. -/
theorem finiteAdmissible
    (hq : ∀ u t p, (d u t p).q = p.val.asIdeal.absNorm)
    (hd : ∀ u t p, LocalWhittakerBounds (d u t p)) :
    FiniteMellinAdmissible K S F := by
  have hcut := valuation_cutoff K S B H hH assemble pivot classOf d μ C₀ hC₀ A₀ hA₀ hd
  have hdecay := valuation_decay K S B H hH assemble pivot classOf d μ C₀ hC₀ A₀ hA₀ hq hd
  refine ⟨hcut, hdecay, ?_⟩
  intro u κ l p s hs
  apply FiniteShell.summable_mellin_of_bounds p.val.asIdeal.absNorm
    (NumberField.HeightOneSpectrum.one_lt_absNorm p.val) (F.coefficient u κ l p) ?_ ?_ s hs
  · obtain ⟨k₀, hk₀⟩ := hcut
    exact ⟨k₀, fun k hk => hk₀ u κ l p k hk⟩
  · intro δ hδ
    obtain ⟨C, hC, hc⟩ := hdecay δ hδ
    exact ⟨C, hC, fun k hk => hc u κ l p k hk⟩

end ThetaGlobal.ProjectFiniteMellin

#print axioms ThetaGlobal.ProjectFiniteMellin.valuation_cutoff
#print axioms ThetaGlobal.ProjectFiniteMellin.valuation_decay
#print axioms ThetaGlobal.ProjectFiniteMellin.finiteAdmissible
