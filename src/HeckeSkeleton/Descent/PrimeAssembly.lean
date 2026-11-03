import HeckeSkeleton.Descent.DeletedProducts
import HeckeSkeleton.Descent.ArtinFactors
import ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal

/-! Finite prime fibres and the local-to-global deleted Euler identity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Descent.PrimeAssembly

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
open AlgebraicNumberTheory.Valuations
open HeckeGeneral.Characters.NormPullbackDraft
open HeckeSkeleton.Descent.Artin
open HeckeSkeleton.Descent.DeletedProducts
open scoped Classical BigOperators

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
variable [Algebra F K] [FiniteDimensional F K]

/-- Actual finite-place fibres, with finiteness proved by the existing
ideal-contraction theorem. No assumed finite-fibre instance is supplied. -/
noncomputable instance primeFiberFintype (v : HeightOneSpectrum (𝓞 F)) :
    Fintype {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v} := by
  exact (_root_.finite_finitePlaceBelow_fibre (K := F) (L := K) v).fintype

/-- The entire actual inverse image of a finite downstairs deletion set. -/
def primesAboveDeletion (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Set.Finite.preimage_finitePlaceBelow (K := F) (L := K) S.finite_toSet).toFinset

@[simp] theorem mem_primesAboveDeletion
    (S : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ primesAboveDeletion F K S ↔ _root_.finitePlaceBelow (K := F) w ∈ S := by
  exact Set.Finite.mem_toFinset _

/-- Group the actual upstairs product by the actual prime contraction map. -/
theorem hasProd_deleted_primeFibers (χK : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 F))) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
      ∏ W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v},
        deletedLocalEulerFactor K χK (primesAboveDeletion F K S) W.val s)
      (heckeDeletedContinuation K χK (primesAboveDeletion F K S) s) := by
  have h := (Equiv.sigmaFiberEquiv
    (_root_.finitePlaceBelow (K := F) (L := K))).hasProd_iff.mpr
      (hasProd_heckeDeletedContinuation K χK (primesAboveDeletion F K S) hs)
  exact h.sigma (fun v => hasProd_fintype _)

variable [IsAbelianGalois F K]

/-- The local good-prime arithmetic identity is sufficient: all convergence,
prime regrouping, finite deletions and finite-character interchange are
derived for the actual Hecke functions. -/
theorem deleted_artin_identity_of_good_prime_factors (χ : HeckeCharacter F)
    (S : Finset (HeightOneSpectrum (𝓞 F))) {s : ℂ} (hs : 1 < s.re)
    (hlocal : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      (∏ W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v},
        heckeLocalEulerFactor K (heckeNormPullback F K χ) W.val s) =
      ∏ ψ ∈ artinFactors F K χ, heckeLocalEulerFactor F ψ v s) :
    heckeDeletedContinuation K (heckeNormPullback F K χ) (primesAboveDeletion F K S) s =
      ∏ ψ ∈ artinFactors F K χ, heckeDeletedContinuation F ψ S s := by
  have hgroup := hasProd_deleted_primeFibers F K (heckeNormPullback F K χ) S hs
  have heq : ∀ v : HeightOneSpectrum (𝓞 F),
      (∏ W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v},
        deletedLocalEulerFactor K (heckeNormPullback F K χ)
          (primesAboveDeletion F K S) W.val s) =
      ∏ ψ ∈ artinFactors F K χ, deletedLocalEulerFactor F ψ S v s := by
    intro v
    have hmem (W : {w : HeightOneSpectrum (𝓞 K) //
        _root_.finitePlaceBelow (K := F) w = v}) :
        W.val ∈ primesAboveDeletion F K S ↔ v ∈ S := by
      rw [mem_primesAboveDeletion, W.property]
    by_cases hv : v ∈ S
    · trans (1 : ℂ)
      · apply Finset.prod_eq_one
        intro W _
        simp only [deletedLocalEulerFactor, if_pos ((hmem W).mpr hv)]
      · symm
        apply Finset.prod_eq_one
        intro ψ _
        simp only [deletedLocalEulerFactor, if_pos hv]
    · calc
        _ = ∏ W : {w : HeightOneSpectrum (𝓞 K) //
              _root_.finitePlaceBelow (K := F) w = v},
              heckeLocalEulerFactor K (heckeNormPullback F K χ) W.val s := by
          apply Finset.prod_congr rfl
          intro W _
          exact if_neg (fun h => hv ((hmem W).mp h))
        _ = ∏ ψ ∈ artinFactors F K χ, heckeLocalEulerFactor F ψ v s := hlocal v hv
        _ = _ := by
          apply Finset.prod_congr rfl
          intro ψ _
          exact (if_neg hv).symm
  exact (hgroup.congr_fun (fun v => (heq v).symm)).unique
    (hasProd_finset_heckeDeletedContinuation F (artinFactors F K χ) S hs)

end HeckeSkeleton.Descent.PrimeAssembly
