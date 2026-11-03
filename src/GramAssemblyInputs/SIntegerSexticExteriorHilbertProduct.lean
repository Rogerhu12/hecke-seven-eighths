import SIntegerSexticSPlaceCorrectionPeriod
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity

/-! SOURCE ONLY, UNRUN. Exact global Hilbert product split into ALL S-places
and an explicit finite exterior set. This uses the actual upstream global
product formula and its concrete support bound. It is valid for any finite S;
when S contains the exponent primes, every exterior factor is tame. No
residue-symbol reciprocity identity is assumed. -/
noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.Reciprocity
open scoped Classical BigOperators
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6)

/-- The explicit finite support, enlarged by S before splitting. -/
def sIntegerSexticHilbertTotalSupport (a b : Kˣ) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  powerResidueBadFinitePlaces K ⟨6, by norm_num⟩ a b ∪ S.toFinset

def sIntegerSexticExteriorHilbertProduct (a b : Kˣ) : nthRootsSubgroup K 6 :=
  ∏ v ∈ sIntegerSexticHilbertTotalSupport K S a b \ S.toFinset,
    finitePlaceHilbertSymbol K ⟨6, by norm_num⟩ (by norm_num)
      (sPlaceCorrectionSexticRoots K ζ hζ) v a b

/-- Every exterior factor is in the exact common global root group; its
product is the inverse of the actual all-S correction. -/
theorem sIntegerSexticExteriorHilbertProduct_eq_SPlaceCorrection_inv (a b : Kˣ) :
    sIntegerSexticExteriorHilbertProduct K S ζ hζ a b =
      (sIntegerSexticSPlaceCorrection K S ζ hζ a b)⁻¹ := by
  let f : HeightOneSpectrum (𝓞 K) → nthRootsSubgroup K 6 := fun v =>
    finitePlaceHilbertSymbol K ⟨6, by norm_num⟩ (by norm_num)
      (sPlaceCorrectionSexticRoots K ζ hζ) v a b
  let T := sIntegerSexticHilbertTotalSupport K S a b
  have hsupp : Function.mulSupport f ⊆ (T : Set (HeightOneSpectrum (𝓞 K))) := by
    intro v hv
    exact Finset.mem_union_left _
      (finitePlaceHilbertSymbol_mulSupport_subset_powerResidueBadFinitePlaces K
        ⟨6, by norm_num⟩ (by norm_num) (sPlaceCorrectionSexticRoots K ζ hζ) a b hv)
  have hinfinite : (∏ v : InfinitePlace K,
      infinitePlaceHilbertSymbol K ⟨6, by norm_num⟩ v a b) =
      (1 : nthRootsSubgroup K (((⟨6, by norm_num⟩ : ℕ+)) : ℕ)) := by
    apply Finset.prod_eq_one
    intro v _
    exact infinitePlaceHilbertSymbol_eq_one_of_ne_two K ⟨6, by norm_num⟩ v a b
      (by norm_num)
  have hbad := powerResidueBadFinitePlaces_product_eq_infinitePlaceProduct_inv K
    ⟨6, by norm_num⟩ (by norm_num) (sPlaceCorrectionSexticRoots K ζ hζ) a b
  replace hbad := hbad.trans ((congrArg Inv.inv hinfinite).trans inv_one)
  have htotal : (∏ v ∈ T, f v) = 1 := by
    rw [← finprod_eq_prod_of_mulSupport_subset f hsupp]
    exact (finitePlaceHilbertSymbol_finprod_eq_prod_powerResidueBadFinitePlaces K
      ⟨6, by norm_num⟩ (by norm_num) (sPlaceCorrectionSexticRoots K ζ hζ) a b).trans hbad
  have hS : sIntegerSexticSPlaceCorrection K S ζ hζ a b =
      ∏ v ∈ S.toFinset, f v := by
    exact Finset.prod_set_coe (f := f) S
  have hsplit : (∏ v ∈ T \ S.toFinset, f v) * ∏ v ∈ S.toFinset, f v =
      ∏ v ∈ T, f v :=
    Finset.prod_sdiff (f := f) (show S.toFinset ⊆ T from Finset.subset_union_right)
  apply (eq_inv_iff_mul_eq_one).mpr
  change (∏ v ∈ T \ S.toFinset, f v) *
    sIntegerSexticSPlaceCorrection K S ζ hζ a b = 1
  rw [hS]
  exact hsplit.trans htotal
end HeckeGeneral.Arithmetic
