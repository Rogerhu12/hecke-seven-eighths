import FLTReuse.M1d4e501986eb161a
import FLTReuse.Mdfdfd9c07e31f9bd
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The standard finite additive character is the product of its local restrictions

The box-triviality and finite-support decomposition argument follows
`P2M/Sol/S_LanglandsTunnell_HeckeTate_isNicePinned_heckeDatum.lean`,
lines 224–302, in anthropics/fermats-last-theorem at
`6e837e75355538c7f80bab5b956861e86c4eacc2` (Apache-2.0).
The proof is reorganized into public reusable statements and uses Mathlib's
actual restricted-product evaluation homomorphism. It does not import the
large solution module or reference its private declarations.

The standard character and every `psiLocal` are unchanged. A finite adèle is
the sum of its finitely many nonintegral coordinates and an integral box
element; the actual standard trace character is trivial on that box.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain NumberField.StandardAddChar
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- Restriction of the actual standard character to the finite adèles. -/
def standardFiniteAddCharacter : AddChar (FiniteAdeleRing (𝓞 K) K) ℂ :=
  (stdAddChar K).compAddMonoidHom
    (AddMonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

@[simp] theorem standardFiniteAddCharacter_apply (x : FiniteAdeleRing (𝓞 K) K) :
    standardFiniteAddCharacter K x = stdAddChar K ((0 : InfiniteAdeleRing K), x) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual finite trace preserves the integral box, on which `psiFin` is one. -/
theorem standardFiniteAddCharacter_eq_one_of_integral (x : FiniteAdeleRing (𝓞 K) K)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), x v ∈ v.adicCompletionIntegers K) :
    standardFiniteAddCharacter K x = 1 := by
  have hbox : x = RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite
      (fun v => ⟨x v, hx v⟩) :=
    FiniteAdeleRing.ext K fun v => by
      exact (RestrictedProduct.structureMap_apply
        (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
        (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
        (x := fun v => ⟨x v, hx v⟩) v).symm
  change psiQ ((adelicTraceData K).traceInf 0, traceFinHom K x) = 1
  rw [psiQ_apply, map_zero, AddChar.map_zero_eq_one, one_mul, hbox,
    traceFinHom_structureMap]
  exact psiFin_eq_one_of_forall_mem _ fun v => (AdelicTrace.traceInt K _ v).2

/-- The finite part obtained by retaining only coordinates in a finite set. -/
def finiteAdeleSupportPart (x : FiniteAdeleRing (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : FiniteAdeleRing (𝓞 K) K :=
  ∑ v ∈ S, finAdeleSingleAt K v (x v)

theorem finiteAdeleSupportPart_apply (x : FiniteAdeleRing (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : HeightOneSpectrum (𝓞 K)) :
    finiteAdeleSupportPart K x S w = if w ∈ S then x w else 0 := by
  let ev : FiniteAdeleRing (𝓞 K) K →+ w.adicCompletion K :=
    RestrictedProduct.evalAddMonoidHom
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) w
  change ev (∑ v ∈ S, finAdeleSingleAt K v (x v)) = _
  rw [map_sum]
  change (∑ v ∈ S, finAdeleSingleAt K v (x v) w) = _
  split_ifs with hw
  · rw [Finset.sum_eq_single w]
    · exact finAdeleSingleAt_apply_self K w (x w)
    · intro v _ hvw
      exact finAdeleSingleAt_apply_of_ne K v (x v) hvw.symm
    · intro hn
      exact absurd hw hn
  · exact Finset.sum_eq_zero fun v hv =>
      finAdeleSingleAt_apply_of_ne K v (x v) (fun h => hw (h ▸ hv))

/-- After removing all nonintegral coordinates, the remainder lies in the actual box. -/
theorem finiteAdele_sub_supportPart_integral (x : FiniteAdeleRing (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → x v ∈ v.adicCompletionIntegers K) :
    ∀ v : HeightOneSpectrum (𝓞 K),
      (x - finiteAdeleSupportPart K x S) v ∈ v.adicCompletionIntegers K := by
  intro v
  change x v - finiteAdeleSupportPart K x S v ∈ v.adicCompletionIntegers K
  rw [finiteAdeleSupportPart_apply]
  split_ifs with hv
  · rw [sub_self]
    exact zero_mem _
  · rw [sub_zero]
    exact hS v hv

/-- Apply an additive character to a finite sum using its addition law. -/
theorem finiteAddCharacter_sum {ι : Type*} (χ : AddChar (FiniteAdeleRing (𝓞 K) K) ℂ)
    (S : Finset ι) (f : ι → FiniteAdeleRing (𝓞 K) K) :
    χ (∑ v ∈ S, f v) = ∏ v ∈ S, χ (f v) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- A finite product formula for any set containing all nonintegral coordinates. -/
theorem standardFiniteAddCharacter_eq_prod (x : FiniteAdeleRing (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → x v ∈ v.adicCompletionIntegers K) :
    standardFiniteAddCharacter K x = ∏ v ∈ S, psiLocal K v (x v) := by
  have hb := finiteAdele_sub_supportPart_integral K x S hS
  calc
    standardFiniteAddCharacter K x =
        standardFiniteAddCharacter K
          ((x - finiteAdeleSupportPart K x S) + finiteAdeleSupportPart K x S) := by
      rw [sub_add_cancel]
    _ = standardFiniteAddCharacter K (x - finiteAdeleSupportPart K x S) *
        standardFiniteAddCharacter K (finiteAdeleSupportPart K x S) :=
      AddChar.map_add_eq_mul _ _ _
    _ = standardFiniteAddCharacter K (finiteAdeleSupportPart K x S) := by
      rw [standardFiniteAddCharacter_eq_one_of_integral K _ hb, one_mul]
    _ = ∏ v ∈ S, standardFiniteAddCharacter K (finAdeleSingleAt K v (x v)) :=
      finiteAddCharacter_sum K _ S _
    _ = ∏ v ∈ S, psiLocal K v (x v) := rfl

/-- Integrality is the actual local box-triviality criterion, including different primes. -/
theorem mulSupport_psiLocal_subset_nonintegral (x : FiniteAdeleRing (𝓞 K) K) :
    Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) => psiLocal K v (x v)) ⊆
      {v : HeightOneSpectrum (𝓞 K) | x v ∉ v.adicCompletionIntegers K} := by
  intro v hv
  rw [Function.mem_mulSupport] at hv
  intro hint
  exact hv (LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers K v (x v) hint)

/-- The restricted-product condition is exactly finiteness of nonintegral places. -/
theorem finite_nonintegralPlaces (x : FiniteAdeleRing (𝓞 K) K) :
    {v : HeightOneSpectrum (𝓞 K) | x v ∉ v.adicCompletionIntegers K}.Finite :=
  Filter.eventually_cofinite.mp (RestrictedProduct.eventually _ _ x)

/-- Every actual finite adèle has a finite local-character support. -/
theorem finite_mulSupport_psiLocal (x : FiniteAdeleRing (𝓞 K) K) :
    (Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) => psiLocal K v (x v))).Finite :=
  (finite_nonintegralPlaces K x).subset (mulSupport_psiLocal_subset_nonintegral K x)

/-- Public factorization with the exact standard global and local normalization. -/
theorem stdAddChar_finite_eq_finprod_psiLocal (x : FiniteAdeleRing (𝓞 K) K) :
    stdAddChar K ((0 : InfiniteAdeleRing K), x) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), psiLocal K v (x v) := by
  have hbad := finite_nonintegralPlaces K x
  let S := hbad.toFinset
  have hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → x v ∈ v.adicCompletionIntegers K := by
    intro v hv
    by_contra hint
    exact hv ((hbad.mem_toFinset).mpr hint)
  have hsupp : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) => psiLocal K v (x v)) ⊆ ↑S := by
    intro v hv
    exact (hbad.mem_toFinset).mpr (mulSupport_psiLocal_subset_nonintegral K x hv)
  change standardFiniteAddCharacter K x = _
  rw [standardFiniteAddCharacter_eq_prod K x S hS]
  exact (finprod_eq_prod_of_mulSupport_subset _ hsupp).symm

end HeckeGeneral.Characters
