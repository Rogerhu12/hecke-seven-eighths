import HeckeGeneral.Analysis.HeckeEulerDeletion
import HeckeGeneral.Analysis.HeckeEulerProduct
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Finite Euler deletion and convergent products of the actual Hecke functions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Descent.DeletedProducts

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The original local factor with precisely the specified finite set removed. -/
def deletedLocalEulerFactor (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  if v ∈ S then 1 else heckeLocalEulerFactor K χ v s

/-- Actual finite deletion, derived from the proved full Euler product. -/
theorem hasProd_heckeDeletedContinuation (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v => deletedLocalEulerFactor K χ S v s)
      (heckeDeletedContinuation K χ S s) := by
  have h := (hasProd_heckeLSeries K χ hs).congr_cofinite₀
    (s := S)
    (fun v _ => heckeLocalEulerFactor_ne_zero K χ v
      (lt_trans zero_lt_one hs))
    (g := fun v => deletedLocalEulerFactor K χ S v s)
    (fun v hv => by simp only [deletedLocalEulerFactor, if_neg hv])
  have hremoved : (∏ v ∈ S, deletedLocalEulerFactor K χ S v s) = 1 := by
    apply Finset.prod_eq_one
    intro v hv
    simp only [deletedLocalEulerFactor, if_pos hv]
  have hlocal : (∏ v ∈ S, heckeLocalEulerFactor K χ v s) =
      (heckeEulerDeletionPolynomial K χ S s)⁻¹ := by
    simp only [heckeLocalEulerFactor, heckeEulerDeletionPolynomial,
      finiteEulerPolynomial, Finset.prod_inv_distrib]
  rw [hremoved, hlocal, one_div, inv_inv] at h
  simpa only [heckeDeletedContinuation, heckeContinuation_eq_series K χ hs,
    mul_comm] using h

/-- The Euler product over the literal complement of S has the same value. -/
theorem hasProd_heckeDeletedContinuation_compl (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      heckeLocalEulerFactor K χ v.val s) (heckeDeletedContinuation K χ S s) := by
  apply (hasProd_subtype_iff_mulIndicator
    (s := {v : HeightOneSpectrum (𝓞 K) | v ∉ S})
    (f := fun v => heckeLocalEulerFactor K χ v s)).mpr
  apply (hasProd_heckeDeletedContinuation K χ S hs).congr_fun
  intro v
  by_cases hv : v ∈ S <;> simp [deletedLocalEulerFactor, Set.mulIndicator, hv]

theorem heckeDeletedContinuation_eq_eulerProduct (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    heckeDeletedContinuation K χ S s =
      ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        heckeLocalEulerFactor K χ v.val s :=
  (hasProd_heckeDeletedContinuation_compl K χ S hs).tprod_eq.symm

/-- Finite products of actual deleted Hecke functions may be taken prime by
prime. Convergence and the interchange are derived, not additional premises. -/
theorem hasProd_finset_heckeDeletedContinuation
    (C : Finset (HeckeCharacter K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v => ∏ χ ∈ C, deletedLocalEulerFactor K χ S v s)
      (∏ χ ∈ C, heckeDeletedContinuation K χ S s) := by
  exact hasProd_prod (fun χ (_ : χ ∈ C) =>
    hasProd_heckeDeletedContinuation K χ S hs)

/-- Version on the literal undeleted prime subtype. -/
theorem hasProd_finset_heckeDeletedContinuation_compl
    (C : Finset (HeckeCharacter K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      ∏ χ ∈ C, heckeLocalEulerFactor K χ v.val s)
      (∏ χ ∈ C, heckeDeletedContinuation K χ S s) := by
  exact hasProd_prod (fun χ (_ : χ ∈ C) =>
    hasProd_heckeDeletedContinuation_compl K χ S hs)

end HeckeSkeleton.Descent.DeletedProducts
