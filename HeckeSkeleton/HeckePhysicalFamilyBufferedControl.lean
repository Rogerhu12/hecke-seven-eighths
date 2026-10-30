import HeckeSkeleton.HeckeFiniteBackgroundControl
import HeckeSkeleton.HighNormBackgroundExclusion

/-!
Buffered control of the actual physical row family. The finite background
set includes every orientation appearing literally in physicalRowFamily.
The target/background may have arbitrary continuous infinity type.
Pure norm exclusion is explicit and can be supplied, above a constructed
row cutoff, by HighNormBackgroundExclusion after actual finite-fiber
calibration. No analytic estimate is assumed in this wrapper.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HeckePhysicalFamilyBufferedControl

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Bridge HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeBufferedReciprocal
open HeckeSkeleton.HeckeFiniteBackgroundControl
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Three finite background lists cover all four physical orientations,
without requiring the companion set to be closed under inversion. -/
def physicalBackgrounds (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K)) :
    Finset (HeckeCharacter K) :=
  (Θ ∪ Θ.image (fun θ => ψ * θ)) ∪ Θ.image (fun θ => conjugate ψ * θ)

theorem physical_member_background_decomposition
    (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
    (P : ProbeData K S) (E : RowEulerData K S P) (u : FrequencyRow K S)
    (η : HeckeCharacter K) (hη : η ∈ physicalRowFamily K S ψ Θ P E u) :
    ∃ β ∈ physicalBackgrounds K ψ Θ,
      η = β * E.rows.character u ∨ η = β * conjugate (E.rows.character u) := by
  obtain ⟨θ, hθ, hη⟩ := Finset.mem_biUnion.mp hη
  simp only [Finset.mem_insert, Finset.mem_singleton] at hη
  rcases hη with hη | hη | hη | hη
  · refine ⟨θ, ?_, Or.inl hη⟩
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hθ)
  · refine ⟨θ, ?_, Or.inr hη⟩
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hθ)
  · refine ⟨ψ * θ, ?_, Or.inr hη⟩
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨θ, hθ, rfl⟩))
  · refine ⟨conjugate ψ * θ, ?_, Or.inl hη⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨θ, hθ, rfl⟩)

/-- A single constant works for the whole actual physical row family.
The row-specific premises are the zero upper bound and pure norm exclusion;
fixed infinity type is derived from RowCharacterInput.finite_order. -/
theorem exists_uniform_physicalFamily_buffered_control
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
    (P : ProbeData K S) (E : RowEulerData K S P)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (u : FrequencyRow K S) (a H Hupper : ℝ),
      (∀ η ∈ physicalRowFamily K S ψ Θ P E u,
        ∀ t : ℝ, η ≠ heckeNormTwist K t) →
      1 / 2 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ Hupper →
      rowZeroBelow K S ψ Θ P E u Hupper (a + 2 * e) →
      ∀ η ∈ physicalRowFamily K S ψ Θ P E u,
      ∀ s : ℂ, a + 6 * e ≤ s.re → s.re ≤ 2 → |s.im| ≤ H →
        ‖heckeContinuation K η s‖ + ‖(heckeContinuation K η s)⁻¹‖ ≤
          D * heckeConductorScale K η ^ ε *
            (2 + Hupper) ^ ((2 * Fintype.card (InfinitePlace K) : ℕ) * ε) := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_finiteBackground_buffered_control K hcomplex
    (physicalBackgrounds K ψ Θ) he he' hε
  refine ⟨D, hD, ?_⟩
  intro u a H Hupper hnon ha ha' hH hpadding hbelow η hη s hs hs' hheight
  have hn := hnon η hη
  have hz : ZeroUpperBound K η Hupper (a + 2 * e) := hbelow η hη
  obtain ⟨β, hβ, hdecomp⟩ := physical_member_background_decomposition
    K S ψ Θ P E u η hη
  rcases hdecomp with hdecomp | hdecomp
  · subst η
    exact hbound β hβ (E.rows.character u) (E.rows.finite_order u)
      a H Hupper hn ha ha' hH hpadding hz s hs hs' hheight
  · subst η
    exact hbound β hβ (conjugate (E.rows.character u)) (E.rows.finite_order u).inv
      a H Hupper hn ha ha' hH hpadding hz s hs hs' hheight

/-- Finite actual row-character fibers remove the explicit non-norm
premise above a single threshold, uniformly over every shell d>=1/16.
This is eventual high-row control; it does not assert global HB-POLE. -/
theorem exists_uniform_high_physicalFamily_buffered_control
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
    (P : ProbeData K S) (E : RowEulerData K S P)
    (hFib : ∀ χ : HeckeCharacter K, Finite {u : FrequencyRow K S // E.rows.character u = χ})
    (v : InfinitePlace K)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε) :
    ∃ D Z₀ : ℝ, 0 < D ∧ 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S,
      Z ^ d ≤ frequencyRowNorm K S u → ∀ a H Hupper : ℝ,
      1 / 2 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ Hupper →
      rowZeroBelow K S ψ Θ P E u Hupper (a + 2 * e) →
      ∀ η ∈ physicalRowFamily K S ψ Θ P E u,
      ∀ s : ℂ, a + 6 * e ≤ s.re → s.re ≤ 2 → |s.im| ≤ H →
        ‖heckeContinuation K η s‖ + ‖(heckeContinuation K η s)⁻¹‖ ≤
          D * heckeConductorScale K η ^ ε *
            (2 + Hupper) ^ ((2 * Fintype.card (InfinitePlace K) : ℕ) * ε) := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_physicalFamily_buffered_control
    K S hcomplex ψ Θ P E he he' hε
  obtain ⟨Z₀, hZ₀, hnon⟩ :=
    HeckeSkeleton.HighNormBackgroundExclusion.high_rows_exclude_background_norm_twists
      K S P E.rows hFib v (physicalBackgrounds K ψ Θ)
  refine ⟨D, Z₀, hD, hZ₀, ?_⟩
  intro Z hZ d hd u hu a H Hupper ha ha' hH hpadding hbelow
  have hn := hnon Z hZ d hd u hu
  have hfamily : ∀ η ∈ physicalRowFamily K S ψ Θ P E u,
      ∀ t : ℝ, η ≠ heckeNormTwist K t := by
    intro η hη
    obtain ⟨β, hβ, hdecomp⟩ := physical_member_background_decomposition
      K S ψ Θ P E u η hη
    rcases hdecomp with hdecomp | hdecomp
    · rw [hdecomp]
      exact (hn β hβ).1
    · rw [hdecomp]
      exact (hn β hβ).2
  exact hbound u a H Hupper hfamily ha ha' hH hpadding hbelow

end HeckeSkeleton.HeckePhysicalFamilyBufferedControl
