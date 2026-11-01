import HeckeSkeleton.PrimeCancellationExplicit
import HeckeSkeleton.PrimeCancellationHecke
import HeckeSkeleton.PrimeCancellationPolynomials
import HeckeSkeleton.PrimeCancellationMoment
import HeckeSkeleton.PrimeCancellationBounds
import HeckeSkeleton.PrimeCancellationWindows

/-!
# Prime cancellation for the actual paired moment models

`PrimeSlotModelControl` repairs the original model interface.  It controls
the actual prime windows and the conductors of every summed row, bounds the
number of slots, and records the finite exceptional characters needed to
exclude the principal prime character.  It contains no prime-sum, moment,
Euler-series, nonvanishing, or growth estimate.

The analytic data use the actual Hecke continuation (equivalently the
deleted continuation with empty deletion).  The packet boundary is taken
from `c.family.boundary`; finite-order polynomial growth is proved by the
Hecke adapter.  The complete original mask is retained.  Both the contour
loss and the logarithmic mask/conductor losses fit the original `lamA`.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.PrimeCancellationWiring

open NumberField IsDedekindDomain
open HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open HeckeSkeleton.PrimeCancellationHecke HeckeSkeleton.PrimeCancellationMoment
open HeckeSkeleton.PrimeCancellationBounds HeckeSkeleton.ExplicitHeckeFunctionalEquation
open PrimeCancellation PrimeCancellation.Analytic PrimeCancellation.Paired
open PrimeCancellation.UniformProfiles PrimeCancellation.PairedProfiles
open scoped Classical BigOperators SchwartzMap

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}

local instance sectorFintype : Fintype (SixthUnitClasses K (places K c)) :=
  Fintype.ofFinite _

/-- Additional, purely structural and profile/conductor requirements on
the entire family of actual paired models.  The existing calibration and
eligibility records are retained as separate premises.

The all-row conductor bound is deliberate: physical-row calibration alone
does not cover the sum in `PairedPrimeProductBound`.  The window bound is on
the actual chosen height parameters, so no unproved height-range condition
is imported from `WholeMomentProfileControl`.
-/
structure PrimeSlotModelControl (M : ActualSourceModels K c) where
  slot_count : ∀ Z T (i : ActualSourceIndex K c Z T) s,
    (pairedModelFor M i s).geometry.slotCount ≤ c.geometry.slots
  inverse_mem : ∀ Z T (i : ActualSourceIndex K c Z T) s j,
    ((pairedModelFor M i s).slotCoefficient j)⁻¹ ∈ (pairedModelFor M i s).theta
  window : ∀ Z T (i : ActualSourceIndex K c Z T) s,
    Fin (pairedModelFor M i s).geometry.slotCount → SchwartzMap ℝ ℂ
  window_eq : ∀ Z T (i : ActualSourceIndex K c Z T) s j,
    (window Z T i s j : ℝ → ℂ) = ((pairedModelFor M i s).geometry.slots j).profile 0
  window_support : ∀ Z T (i : ActualSourceIndex K c Z T) s j,
    Function.support (window Z T i s j : ℝ → ℂ) ⊆ Set.Icc (1 : ℝ) 2
  window_control : ∀ seminorms : Finset (ℕ × ℕ),
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ Z T (i : ActualSourceIndex K c Z T) s j, 1 ≤ Z → 1 ≤ T →
        sourceSeminorm seminorms (window Z T i s j) ≤ C * (1 + T) ^ A
  conductor_control : ∃ D q : ℝ, 1 ≤ D ∧ 0 ≤ q ∧
    ∀ Z T (i : ActualSourceIndex K c Z T) s u,
      1 ≤ Z → 1 ≤ T → 1 ≤ momentBaseFor i →
      u ∈ pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i) →
      ∀ j, Real.log (heckeConductorScale K
        ((pairedModelFor M i s).rowCharacter u * (pairedModelFor M i s).slotCoefficient j)) ≤
          D * (1 + Real.log (momentBaseFor i)) * (1 + T) ^ q

/-- The old source interface maps to an independent explicit family using
only its structural model, mask, geometry and finite-slot calibration.
The source index itself remains part of this compatibility definition.
-/
def explicitModelFamilyOfSource
    (M : ActualSourceModels K c)
    (hcal : SourcePolynomialCalibrationFor (momentRowCharacters K c) M)
    (hrows : SourceRowEligibilityFor M) :
    PrimeCancellationExplicit.ExplicitModelFamily c
      (fun Z T => ActualSourceIndex K c Z T) where
  model := fun _ _ i s => pairedModelFor M i s
  base := fun _ _ i => momentBaseFor i
  parameters := fun _ _ i => pairedParametersFor i
  length := fun _ _ i => selectedLengthFor i
  base_pos := by
    intro Z T i hZ _hT
    exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _
  row_exponent := by
    intro Z T i
    have hw := recipeMoment_rowWidth_spec (R := expansionRecipeRaw K c) i
    have h1 : 1 < rowWidthFor i := hw.1
    have h2 : momentBaseFor i ^ rowWidthFor i = 2 * momentBaseFor i := hw.2.2
    refine ⟨?_, ?_⟩
    · change 1 ≤ rowWidthFor i + 0
      linarith
    · change momentBaseFor i ^ (rowWidthFor i + 0) ≤ 2 * momentBaseFor i
      rw [add_zero]
      exact h2.le
  parameter_length := by
    intro Z T i
    rfl
  geometry_length := fun Z T i s => (hrows.geometry Z T i s).2
  mask := fun Z T i s v I => (hcal.mask Z T i s v I).2
  finite_slots := hrows.paired_finite_slots

/-- The all-row window and conductor contract transfers without an
additional analytic premise. -/
def explicitModelControlOfSource
    (M : ActualSourceModels K c)
    (hcal : SourcePolynomialCalibrationFor (momentRowCharacters K c) M)
    (hrows : SourceRowEligibilityFor M) (control : PrimeSlotModelControl M) :
    PrimeCancellationExplicit.ExplicitModelControl (explicitModelFamilyOfSource M hcal hrows) where
  slot_count := control.slot_count
  inverse_mem := control.inverse_mem
  window := control.window
  window_eq := control.window_eq
  window_support := control.window_support
  window_control := control.window_control
  conductor_control := control.conductor_control

/-- Compatibility with the original source-indexed uniform conclusion.
The independent explicit theorem proves the estimate; the old capacity
premise supplies its purely geometric total-length bound.
-/
theorem exists_uniform_paired_prime_bound
    (M : ActualSourceModels K c) (hB : c.family.B < 1)
    (hcal : SourcePolynomialCalibrationFor (momentRowCharacters K c) M)
    (hrows : SourceRowEligibilityFor M) (control : PrimeSlotModelControl M) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧
      ∀ Z T (i : ActualSourceIndex K c Z T), 1 ≤ Z → 1 ≤ T → pairedCapacityFor i →
        (∑ s : SixthUnitClasses K (places K c),
          ∑ u ∈ pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i),
            ‖slotProduct (pairedModelFor M i s) u (momentBaseFor i) 0‖ ^ 2) ≤
          C * (momentBaseFor i) ^
            (1 + (2 * c.family.B - 1) * selectedLengthFor i + c.family.lamA) * (1 + T) ^ A := by
  obtain ⟨A, C, hA, hC, hbound⟩ :=
    PrimeCancellationExplicit.exists_uniform_paired_prime_bound
      (explicitModelFamilyOfSource M hcal hrows) hB
      (explicitModelControlOfSource M hcal hrows control)
  refine ⟨A, C, hA, hC, ?_⟩
  intro Z T i hZ hT hcap
  exact hbound Z T i hZ hT
    (selectedLength_le_slots_mul_mesh_of_pairedCapacity i hcap)

/-- The corrected MI-P-PRIME-CANCELLATION-BELOW-ONE theorem.  It has the exact
original `PairedPrimeProductBound` conclusion for any model satisfying the
explicit corrected structural contract.  `momentModels` is never invoked.
-/
theorem paired_primes_below_one_of_models
    (M : ActualSourceModels K c) (hB : c.family.B < 1)
    (hcal : SourcePolynomialCalibrationFor (momentRowCharacters K c) M)
    (hrows : SourceRowEligibilityFor M) (control : PrimeSlotModelControl M) :
    PairedPrimeProductBoundFor M (2 * c.family.B - 1) := by
  obtain ⟨A, ceiling, hA, hceiling, hbound⟩ :=
    PrimeCancellationExplicit.paired_primes_below_one_of_explicit_models
      (explicitModelFamilyOfSource M hcal hrows) hB
      (explicitModelControlOfSource M hcal hrows control)
  refine ⟨A, ceiling, hA, hceiling, ?_⟩
  intro τ hτ hτupper
  obtain ⟨Z₀, C, hZ₀, hC, hboundτ⟩ := hbound τ hτ hτupper
  refine ⟨Z₀, C, hZ₀, hC, ?_⟩
  intro Z hZ i _hbin hcap
  exact hboundτ Z hZ i (selectedLength_le_slots_mul_mesh_of_pairedCapacity i hcap)

#print axioms primePolynomial_bound_of_analytic_data
#print axioms exists_uniform_paired_prime_bound
#print axioms paired_primes_below_one_of_models

end HeckeSkeleton.PrimeCancellationWiring
