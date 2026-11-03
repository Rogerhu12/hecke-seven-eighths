import SIntegerSexticRIdentification
import FinitePlaceHilbertBilinear
import HeckeGeneral.Arithmetic.SIntegerOrbitEnumeration

/-!
UNCOMPILED / native 0. Independent sixth-power multiplication in the two
arguments of the actual ALL-S Hilbert correction. The resulting theorem
for actual nonzero S-integers includes the common-prime locus. It does not
identify R with RCandidate and does not alter any frequency: RCorrection
has no frequency argument. No coprimality, active-fibre or congruence
condition is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Characters.ActualRCorrectionSixthUnitDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open KummerTheory GlobalClassFieldTheory.Reciprocity
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- A homomorphism into the actual sixth-root subgroup kills sixth powers. -/
private theorem sixthRootValuedHom_sixth_power
    (f : Kˣ →* nthRootsSubgroup K 6) (u : Kˣ) : f (u ^ 6) = 1 := by
  rw [map_pow]
  apply Subtype.ext
  change (f u).val ^ 6 = 1
  exact (f u).property

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6)

/-- Every actual S-place Hilbert factor, including places added to S,
is unchanged by independent sixth powers of arbitrary global field units. -/
theorem sIntegerSexticSPlaceCorrection_mul_sixth_powers (u v a b : Kˣ) :
    sIntegerSexticSPlaceCorrection K S ζ hζ (u ^ 6 * a) (v ^ 6 * b) =
      sIntegerSexticSPlaceCorrection K S ζ hζ a b := by
  unfold sIntegerSexticSPlaceCorrection
  apply Finset.prod_congr rfl
  intro p _
  have hleft : finitePlaceHilbertSymbol K ⟨6, by norm_num⟩ (by norm_num)
      (sPlaceCorrectionSexticRoots K ζ hζ) p.val (u ^ 6) (v ^ 6 * b) = 1 :=
    sixthRootValuedHom_sixth_power K
      (finitePlaceHilbertFirstHom K ⟨6, by norm_num⟩ (by norm_num)
        (sPlaceCorrectionSexticRoots K ζ hζ) p.val (v ^ 6 * b)) u
  have hright : finitePlaceHilbertSymbol K ⟨6, by norm_num⟩ (by norm_num)
      (sPlaceCorrectionSexticRoots K ζ hζ) p.val a (v ^ 6) = 1 :=
    sixthRootValuedHom_sixth_power K
      (finitePlaceHilbertSecondHom K ⟨6, by norm_num⟩ (by norm_num)
        (sPlaceCorrectionSexticRoots K ζ hζ) p.val a) v
  have e1 := finitePlaceHilbertSymbol_mul_left K ⟨6, by norm_num⟩ (by norm_num)
    (sPlaceCorrectionSexticRoots K ζ hζ) p.val (u ^ 6) a (v ^ 6 * b)
  have e2 := finitePlaceHilbertSymbol_mul_right K ⟨6, by norm_num⟩ (by norm_num)
    (sPlaceCorrectionSexticRoots K ζ hζ) p.val a (v ^ 6) b
  rw [hleft, one_mul] at e1
  rw [hright, one_mul] at e2
  exact e1.trans e2

variable (σ : K →+* ℂ)
local notation "NZ" => NonzeroRingElements (S.integer K)
-- This is definitionally the original `sixthPowerUnits K S`.
local notation "Γ" => MonoidHom.range (powMonoidHom 6 : S.unit K →* S.unit K)

/-- Actual R, rather than its coprime symbol-product candidate, is
invariant under the original two independent sixth-unit column actions.
The statement has no frequency transport or restriction on shared primes. -/
theorem sIntegerSexticRCorrection_sixthPower_translate
    (u v : Γ) (a b : NZ) :
    sIntegerSexticRCorrection K S ζ hζ σ
        (sIntegerOrbitTranslate K S Γ u a) (sIntegerOrbitTranslate K S Γ v b) =
      sIntegerSexticRCorrection K S ζ hζ σ a b := by
  obtain ⟨u₀, hu₀⟩ := u.property
  obtain ⟨v₀, hv₀⟩ := v.property
  change u₀ ^ 6 = u.val at hu₀
  change v₀ ^ 6 = v.val at hv₀
  have hu : (u.val : Kˣ) = (u₀ : Kˣ) ^ 6 :=
    (congrArg (fun t : S.unit K => (t : Kˣ)) hu₀).symm
  have hv : (v.val : Kˣ) = (v₀ : Kˣ) ^ 6 :=
    (congrArg (fun t : S.unit K => (t : Kˣ)) hv₀).symm
  unfold sIntegerSexticRCorrection
  rw [nonzeroSIntegerFieldUnit_translate, nonzeroSIntegerFieldUnit_translate,
    hu, hv, sIntegerSexticSPlaceCorrection_mul_sixth_powers]

end HeckeGeneral.Characters.ActualRCorrectionSixthUnitDraft
