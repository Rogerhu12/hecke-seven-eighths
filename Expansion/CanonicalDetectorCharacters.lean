import HeckeSkeleton.ExpansionModels.SharedWitnessRecipe
import HeckeGeneral.Analysis.HeckeConjugateZeros
import HeckeGeneral.Analysis.TInputRanges
import HeckeSkeleton.HeckeBufferedReciprocal

/-!
# Two actual presentations for the identity companion family

The physical numerator and denominator require the row, its inverse,
psi times its inverse, and inverse psi times the row. Selecting companions
{1} retains these four characters. Genuine zero orders are reflected before
running the source detector, yielding a single forward row character with
background 1 or inverse psi. Both inverse and plain factors therefore use
the same character allowed by the existing MomentData definition.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HeckeBufferedReciprocal
open scoped Classical ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (ψ : HeckeCharacter K)

def canonicalDetectorBackground (i : Fin 2) : HeckeCharacter K :=
  if i = 0 then 1 else ψ⁻¹

/-- The full positive-slot model excludes every finite-order background
that can cancel its plain character, including inverse psi when applicable.
This filter is separate from the four physical zero-detection characters. -/
def canonicalDetectorTheta : Finset (HeckeCharacter K) :=
  if FiniteOrder ψ then {1, ψ, ψ⁻¹} else {1}

theorem one_mem_canonicalDetectorTheta : (1 : HeckeCharacter K) ∈
    canonicalDetectorTheta K ψ := by
  by_cases hψ : FiniteOrder ψ <;> simp [canonicalDetectorTheta, hψ]

theorem canonicalDetectorTheta_finiteOrder (θ : HeckeCharacter K)
    (hθ : θ ∈ canonicalDetectorTheta K ψ) : FiniteOrder θ := by
  by_cases hψ : FiniteOrder ψ
  · simp only [canonicalDetectorTheta, if_pos hψ, Finset.mem_insert,
      Finset.mem_singleton] at hθ
    rcases hθ with rfl | rfl | rfl
    · exact (finiteOrder_iff _).mpr ⟨1, by norm_num, by simp⟩
    · exact hψ
    · exact hψ.inv
  · have heq : θ = 1 := by simpa [canonicalDetectorTheta, hψ] using hθ
    subst θ
    exact (finiteOrder_iff _).mpr ⟨1, by norm_num, by simp⟩

/-- Both polynomial backgrounds agree, and every field of the original
presentation type is proved without extending its permitted characters. -/
def canonicalDetectorPresentation (i : Fin 2) : PolynomialPresentation K ψ where
  theta := canonicalDetectorTheta K ψ
  theta_finite := canonicalDetectorTheta_finiteOrder K ψ
  inverseBackground := canonicalDetectorBackground K ψ i
  direction := 1
  direction_spec := Or.inr rfl
  directed_background := by
    by_cases hi : i = 0
    · left
      simpa [canonicalDetectorBackground, hi] using one_mem_canonicalDetectorTheta K ψ
    · right
      refine ⟨1, one_mem_canonicalDetectorTheta K ψ, ?_⟩
      simp [canonicalDetectorBackground, hi]
  plainBackground := canonicalDetectorBackground K ψ i
  plain_background_spec := by
    by_cases hi : i = 0
    · left
      simp [canonicalDetectorBackground, hi]
    · right; right
      simp [canonicalDetectorBackground, hi]

/-- The finite-order cancellation character is in the actual model filter. -/
theorem canonicalDetectorPresentation_plain_inverse_mem (i : Fin 2)
    (h : FiniteOrder (canonicalDetectorPresentation K ψ i).plainBackground) :
    (canonicalDetectorPresentation K ψ i).plainBackground⁻¹ ∈
      (canonicalDetectorPresentation K ψ i).theta := by
  by_cases hi : i = 0
  · simpa [canonicalDetectorPresentation, canonicalDetectorBackground, hi] using
      one_mem_canonicalDetectorTheta K ψ
  · have hψ : FiniteOrder ψ := by
      simpa [canonicalDetectorPresentation, canonicalDetectorBackground, hi] using h.inv
    simp [canonicalDetectorPresentation, canonicalDetectorBackground, hi,
      canonicalDetectorTheta, hψ]

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (E : RowEulerData K S P)

def canonicalDetectorCharacter (i : Fin 2) (u : FrequencyRow K S) : HeckeCharacter K :=
  canonicalDetectorBackground K ψ i * E.rows.character u

/-- The two finite model coefficients are the same actual source character. -/
theorem canonicalDetectorPresentation_characters (i : Fin 2) (u : FrequencyRow K S) :
    (canonicalDetectorPresentation K ψ i).inverseBackground *
        E.rows.character u ^ (canonicalDetectorPresentation K ψ i).direction =
      canonicalDetectorCharacter K ψ S P E i u ∧
    (canonicalDetectorPresentation K ψ i).plainBackground * E.rows.character u =
      canonicalDetectorCharacter K ψ S P E i u := by
  simp only [canonicalDetectorPresentation, canonicalDetectorCharacter, zpow_one, and_self]

theorem canonicalDetectorCharacter_mem_family (i : Fin 2) (u : FrequencyRow K S) :
    canonicalDetectorCharacter K ψ S P E i u ∈
      physicalRowFamily K S ψ {1} P E u := by
  by_cases hi : i = 0 <;>
    simp [canonicalDetectorCharacter, canonicalDetectorBackground, hi,
      physicalRowFamily, conjugate]

/-- Reflecting the selected zero preserves its real part and absolute
height. This precedes both source extraction and upper-bound estimates. -/
theorem exists_canonicalDetector_zero (u : FrequencyRow K S) (height a : ℝ)
    (h : rowZeroAbove K S ψ {1} P E u height a) :
    ∃ i : Fin 2, ∃ ρ : ℂ,
      0 < meromorphicOrderAt
        (heckeContinuation K (canonicalDetectorCharacter K ψ S P E i u)) ρ ∧
      a ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ height := by
  obtain ⟨χ, hχ, ρ, hz, hlo, hhi, ht⟩ := h
  have hc : χ = E.rows.character u ∨ χ = (E.rows.character u)⁻¹ ∨
      χ = ψ * (E.rows.character u)⁻¹ ∨ χ = ψ⁻¹ * E.rows.character u := by
    simpa [physicalRowFamily, conjugate] using hχ
  rcases hc with rfl | rfl | rfl | rfl
  · refine ⟨0, ρ, ?_, hlo, hhi, ht⟩
    simpa [canonicalDetectorCharacter, canonicalDetectorBackground] using hz
  · have hr : 0 < meromorphicOrderAt
        (heckeContinuation K ((E.rows.character u)⁻¹)⁻¹) (conj ρ) := by
      rw [meromorphicOrderAt_heckeContinuation_inv]
      exact hz
    refine ⟨0, conj ρ, ?_, ?_, ?_, ?_⟩
    · simpa [canonicalDetectorCharacter, canonicalDetectorBackground] using hr
    · simpa using hlo
    · simpa using hhi
    · simpa only [Complex.conj_im, abs_neg] using ht
  · have hr : 0 < meromorphicOrderAt
        (heckeContinuation K (ψ * (E.rows.character u)⁻¹)⁻¹) (conj ρ) := by
      rw [meromorphicOrderAt_heckeContinuation_inv]
      exact hz
    refine ⟨1, conj ρ, ?_, ?_, ?_, ?_⟩
    · simpa [canonicalDetectorCharacter, canonicalDetectorBackground,
        mul_comm, mul_left_comm] using hr
    · simpa using hlo
    · simpa using hhi
    · simpa only [Complex.conj_im, abs_neg] using ht
  · refine ⟨1, ρ, ?_, hlo, hhi, ht⟩
    simpa [canonicalDetectorCharacter, canonicalDetectorBackground] using hz

/-- The reflected choice remains inside the same original upper-zero
family, so it uses the same buffered rectangle and bin. -/
theorem canonicalDetector_zero_upper (u : FrequencyRow K S) (height a : ℝ)
    (h : rowZeroBelow K S ψ {1} P E u height a) (i : Fin 2) :
    ZeroUpperBound K (canonicalDetectorCharacter K ψ S P E i u) height a :=
  h _ (canonicalDetectorCharacter_mem_family K ψ S P E i u)

end Expansion.Project

#print axioms Expansion.Project.canonicalDetectorPresentation
#print axioms Expansion.Project.canonicalDetectorPresentation_plain_inverse_mem
#print axioms Expansion.Project.canonicalDetectorPresentation_characters
#print axioms Expansion.Project.exists_canonicalDetector_zero
#print axioms Expansion.Project.canonicalDetector_zero_upper
