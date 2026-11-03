import ArithmeticFrequencyRowCharacterFibers
import HeckeSkeleton.HeckeHighRowLRatio

/-!
Actual arithmetic row-character specialization of the high-row L-ratio bound.

The pointwise calibration here is equality of whole Hecke characters for every
actual FrequencyRow. A coefficient equality on a finite prime set would not
provide this hypothesis. The finite-fiber input is proved by transporting the
identity map on rows into the actual arithmetic character fiber, whose finite
sector injection was constructed in ArithmeticFrequencyRowCharacterFibers.

The L-ratio conclusion keeps the original detector, height conditions, and
actual conductor scales. The target is an arbitrary continuous unitary Hecke
character. This file does not assume a conductor bound, classify every row
provider as the arithmetic constructor, or perform the later profile integral.
Prepared as a new isolated source; native checking remains separate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.ActualHighRowLRatio

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Bridge HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Exact character calibration transfers the proved arithmetic fibers along
the identity on the original row type. No finite-fiber assumption is added. -/
theorem rowCharacter_fiber_finite_of_actual_calibration
    (P : ProbeData K S) (E : RowEulerData K S P)
    (hChar : ∀ u : FrequencyRow K S,
      E.rows.character u = arithmeticRowCharacter K S P u)
    (χ : HeckeCharacter K) :
    Finite {u : FrequencyRow K S // E.rows.character u = χ} := by
  letI : Finite {u : FrequencyRow K S // arithmeticRowCharacter K S P u = χ} :=
    arithmeticRowCharacter_fiber_finite K S P χ
  let transport : {u : FrequencyRow K S // E.rows.character u = χ} →
      {u : FrequencyRow K S // arithmeticRowCharacter K S P u = χ} :=
    fun u => ⟨u.val, (hChar u.val).symm.trans u.property⟩
  apply Finite.of_injective transport
  intro u v huv
  apply Subtype.ext
  exact congrArg
    (fun w : {u : FrequencyRow K S // arithmeticRowCharacter K S P u = χ} => w.val)
    huv

/-- Literal equality with the actual constructor gives its global character
calibration, hence finite fibers, without any ideal/sector identification. -/
theorem rowCharacter_fiber_finite_of_rows_eq
    (P : ProbeData K S) (E : RowEulerData K S P)
    (hRows : E.rows = arithmeticRowCharacterInput K S P)
    (χ : HeckeCharacter K) :
    Finite {u : FrequencyRow K S // E.rows.character u = χ} := by
  apply rowCharacter_fiber_finite_of_actual_calibration K S P E
  intro u
  exact congrArg (fun R : RowCharacterInput K S P => R.character u) hRows

/-- The high-row L-ratio theorem with its finite-fiber premise discharged by
the actual arithmetic construction. The remaining calibration is global. -/
theorem exists_uniform_actual_high_row_LRatio_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ)
    (P : ProbeData K S) (E : RowEulerData K S P)
    (hChar : ∀ u : FrequencyRow K S,
      E.rows.character u = arithmeticRowCharacter K S P u)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hesmall : e ≤ 1 / 10000) (hε : 0 < ε) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S,
      Z ^ d ≤ frequencyRowNorm K S u → ∀ a H Hupper : ℝ,
      51 / 100 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ Hupper →
      rowZeroBelow K S ψ Θ P E u Hupper (a + 2 * e) →
      ∀ s w : ℂ, s.re = a + 16 * e → w.re = 1 - a - 6 * e →
      |s.im| ≤ H → |w.im| ≤ H →
        ‖heckeContinuation K (E.rows.character u) w‖ *
          ‖(heckeContinuation K (ψ * conjugate (E.rows.character u)) s)⁻¹‖ ≤
            C * heckeConductorScale K (E.rows.character u) ^ (a - 1 / 2 + 6 * e) *
              heckeConductorScale K ((E.rows.character u)⁻¹) ^ ε *
              heckeConductorScale K (ψ * conjugate (E.rows.character u)) ^ ε *
              (2 + Hupper) ^
                (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
                  2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * ε) := by
  exact HeckeSkeleton.HeckeHighRowLRatio.exists_uniform_high_row_LRatio_bound
    K S hcomplex ψ Θ hΘ P E
    (rowCharacter_fiber_finite_of_actual_calibration K S P E hChar)
    he he' hesmall hε

/-- A simpler literal-constructor specialization of the same numerical bound.
All detector and conductor terms continue to refer to the supplied E. -/
theorem exists_uniform_actual_high_row_LRatio_bound_of_rows_eq
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ)
    (P : ProbeData K S) (E : RowEulerData K S P)
    (hRows : E.rows = arithmeticRowCharacterInput K S P)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hesmall : e ≤ 1 / 10000) (hε : 0 < ε) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S,
      Z ^ d ≤ frequencyRowNorm K S u → ∀ a H Hupper : ℝ,
      51 / 100 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ Hupper →
      rowZeroBelow K S ψ Θ P E u Hupper (a + 2 * e) →
      ∀ s w : ℂ, s.re = a + 16 * e → w.re = 1 - a - 6 * e →
      |s.im| ≤ H → |w.im| ≤ H →
        ‖heckeContinuation K (E.rows.character u) w‖ *
          ‖(heckeContinuation K (ψ * conjugate (E.rows.character u)) s)⁻¹‖ ≤
            C * heckeConductorScale K (E.rows.character u) ^ (a - 1 / 2 + 6 * e) *
              heckeConductorScale K ((E.rows.character u)⁻¹) ^ ε *
              heckeConductorScale K (ψ * conjugate (E.rows.character u)) ^ ε *
              (2 + Hupper) ^
                (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
                  2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * ε) := by
  apply exists_uniform_actual_high_row_LRatio_bound K S hcomplex ψ Θ hΘ P E
  · intro u
    exact congrArg (fun R : RowCharacterInput K S P => R.character u) hRows
  · exact he
  · exact he'
  · exact hesmall
  · exact hε

end HeckeSkeleton.ActualHighRowLRatio
