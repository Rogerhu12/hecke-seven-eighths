import HeckeGeneral.Analysis.MomentInputs
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.FiniteSectorCore

/-!
# Finite sector reindexing for the original moment polynomials

An injective encoding by `(ideal, sector)` embeds the physical rows into
the disjoint union of the sector row sets.  Pointwise calibration therefore
compares each physical energy with the sum of the corresponding original
`MomentData` energies.  All sectors, both plain factors, and the original
row predicates are retained.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}
variable {ι S : Type*} [Fintype S]

/-- The marked inverse energy uses the original masked inverse polynomial
and the exact selected slot product. -/
theorem inverse_finite_sector_reindex
    (R : Finset ι) (ideal : ι → NonzeroIdeal K) (sector : ι → S)
    (d : S → MomentData K ω ψ) (a : RealParameters) (Z t : ℝ)
    (inverseValue slots : ι → ℂ)
    (hinj : Function.Injective (fun u => (ideal u, sector u)))
    (hrows : ∀ u ∈ R, ideal u ∈ (d (sector u)).rows (Z ^ a.m))
    (hinverse : ∀ u ∈ R, inverseValue u =
      inversePolynomial (d (sector u)) (ideal u) (Z ^ a.r) t)
    (hslots : ∀ u ∈ R, slots u = slotProduct (d (sector u)) (ideal u) Z t) :
    ∑ u ∈ R, ‖inverseValue u * slots u‖ ^ 2 ≤
      ∑ s, inverseEnergy (d s) a Z t := by
  apply finite_sector_sum_le R (fun s => (d s).rows (Z ^ a.m))
    ideal sector hinj hrows
    (fun u => ‖inverseValue u * slots u‖ ^ 2)
    (fun s u => ‖inversePolynomial (d s) u (Z ^ a.r) t *
      slotProduct (d s) u Z t‖ ^ 2)
  · intro u hu
    exact le_of_eq (by rw [hinverse u hu, hslots u hu])
  · intro s u
    exact sq_nonneg _

/-- The paired energy keeps both independently calibrated plain profiles.
The row premise is precisely `pairedRows`, including its zero-slot branch. -/
theorem paired_finite_sector_reindex
    (R : Finset ι) (ideal : ι → NonzeroIdeal K) (sector : ι → S)
    (d : S → MomentData K ω ψ) (a : RealParameters) (Z t : ℝ)
    (plainValue slots : ι → ℂ)
    (hinj : Function.Injective (fun u => (ideal u, sector u)))
    (hrows : ∀ u ∈ R, ideal u ∈ pairedRows (d (sector u)) a Z)
    (hplain₁ : ∀ u ∈ R, plainValue u =
      plainPolynomial (d (sector u)) (d (sector u)).plainTest₁
        (ideal u) (Z ^ a.n₁) t)
    (hplain₂ : ∀ u ∈ R, plainValue u =
      plainPolynomial (d (sector u)) (d (sector u)).plainTest₂
        (ideal u) (Z ^ a.n₂) t)
    (hslots : ∀ u ∈ R, slots u = slotProduct (d (sector u)) (ideal u) Z t) :
    ∑ u ∈ R, ‖plainValue u ^ 2 * slots u‖ ^ 2 ≤
      ∑ s, pairedEnergy (d s) a Z t := by
  apply finite_sector_sum_le R (fun s => pairedRows (d s) a Z)
    ideal sector hinj hrows
    (fun u => ‖plainValue u ^ 2 * slots u‖ ^ 2)
    (fun s u => ‖plainPolynomial (d s) (d s).plainTest₁ u (Z ^ a.n₁) t *
      plainPolynomial (d s) (d s).plainTest₂ u (Z ^ a.n₂) t *
      slotProduct (d s) u Z t‖ ^ 2)
  · intro u hu
    have hvalue : plainValue u ^ 2 * slots u =
        plainPolynomial (d (sector u)) (d (sector u)).plainTest₁
          (ideal u) (Z ^ a.n₁) t *
        plainPolynomial (d (sector u)) (d (sector u)).plainTest₂
          (ideal u) (Z ^ a.n₂) t *
        slotProduct (d (sector u)) (ideal u) Z t := by
      rw [← hplain₁ u hu, ← hplain₂ u hu, ← hslots u hu, pow_two]
    exact le_of_eq (congrArg (fun z : ℂ => ‖z‖ ^ 2) hvalue)
  · intro s u
    exact sq_nonneg _

/-- Unmarked reindexing retains the sixth-power-free filter on the target
ball.  No dyadic lower cut-off or missing sector is introduced. -/
theorem unmarked_finite_sector_reindex
    (R : Finset ι) (ideal : ι → NonzeroIdeal K) (sector : ι → S)
    (d : S → MomentData K ω ψ) (U D t : ℝ) (inverseValue : ι → ℂ)
    (hinj : Function.Injective (fun u => (ideal u, sector u)))
    (hrows : ∀ u ∈ R, ideal u ∈ (d (sector u)).rows (2 * U) ∧
      SixthPowerFreeIdeal (ideal u))
    (hinverse : ∀ u ∈ R, inverseValue u =
      inversePolynomial (d (sector u)) (ideal u) D t) :
    ∑ u ∈ R, ‖inverseValue u‖ ^ 2 ≤
      ∑ s, ∑ u ∈ ((d s).rows (2 * U)).filter SixthPowerFreeIdeal,
        ‖inversePolynomial (d s) u D t‖ ^ 2 := by
  apply finite_sector_sum_le R
    (fun s => ((d s).rows (2 * U)).filter SixthPowerFreeIdeal)
    ideal sector hinj (fun u hu => Finset.mem_filter.mpr (hrows u hu))
    (fun u => ‖inverseValue u‖ ^ 2)
    (fun s u => ‖inversePolynomial (d s) u D t‖ ^ 2)
  · intro u hu
    exact le_of_eq (by rw [hinverse u hu])
  · intro s u
    exact sq_nonneg _

end HeckeSkeleton.Moments.UniformAmplify
