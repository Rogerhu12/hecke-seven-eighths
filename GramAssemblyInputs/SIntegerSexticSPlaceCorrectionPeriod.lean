import ExactFinitePlaceHilbertPrincipalUnitPeriod
import SIntegerUpstreamPrincipalUnitCongruence

/-! SOURCE ONLY, UNRUN. Period of the actual sextic Hilbert correction over
ALL S-places, in the upstream common nthRootsSubgroup target. This differs
from the exponent-prime correction B_6 when S contains additional places.
No S-integer reciprocity identity is assumed or asserted. The one-column
result leaves its fixed field-unit argument unrestricted. -/
noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
open GlobalClassFieldTheory.Reciprocity KummerTheory
open scoped Classical BigOperators
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6)
local notation "NZI" => NonzeroRingElements (S.integer K)
local notation "U" => nonzeroSIntegerFieldUnit K S

local instance sPlaceCorrectionPeriod_adicValuativeRel (w : S) :
    ValuativeRel (w.val.adicCompletion K) :=
  ActualFiniteCompletionDraft.adicCompletionValuativeRel K w.val

def sPlaceCorrectionSexticRoots : (primitiveRoots 6 K).Nonempty :=
  ⟨ζ, (mem_primitiveRoots (by norm_num : 0 < 6)).mpr hζ⟩

/-- Every finite S-factor is retained in the exact upstream root group. -/
def sIntegerSexticSPlaceCorrection (a b : Kˣ) : nthRootsSubgroup K 6 :=
  ∏ w : S, finitePlaceHilbertSymbol K ⟨6, by norm_num⟩ (by norm_num)
    (sPlaceCorrectionSexticRoots K ζ hζ) w.val a b

/-- A depth chosen before all arguments, on the completion used by the
upstream finite-place symbol. -/
def sPlaceSexticCorrectionDepth (w : S) : ℕ :=
  (exists_exact_finitePlaceHilbert_principalUnit_period K w.val
    ⟨6, by norm_num⟩ (by norm_num) (sPlaceCorrectionSexticRoots K ζ hζ)).choose

theorem sPlaceSexticCorrectionDepth_pos (w : S) :
    1 ≤ sPlaceSexticCorrectionDepth K S ζ hζ w :=
  (exists_exact_finitePlaceHilbert_principalUnit_period K w.val
    ⟨6, by norm_num⟩ (by norm_num) (sPlaceCorrectionSexticRoots K ζ hζ)).choose_spec.1

def sIntegerSexticSPlaceModulus : Ideal (𝓞 K) :=
  sIntegerPrincipalUnitModulus K S (sPlaceSexticCorrectionDepth K S ζ hζ)

theorem sIntegerSexticSPlaceModulus_ne_bot :
    sIntegerSexticSPlaceModulus K S ζ hζ ≠ ⊥ :=
  sIntegerPrincipalUnitModulus_ne_bot K S _

/-- Literal additive increments yield the required actual local ratio.
Only the moving denominator is required to lie in the original active box. -/
private theorem sPlaceCorrection_ratio_mem
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (w : S) (n m : NZI) (t : 𝓞 K)
    (ht : t ∈ sIntegerSexticSPlaceModulus K S ζ hζ)
    (he : n.val - m.val = algebraMap (𝓞 K) (S.integer K) t)
    (hm : (sLocalNonzeroIntegerDiagonal K S m).2 ∈
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    letI : ValuativeRel (w.val.adicCompletion K) :=
      ActualFiniteCompletionDraft.adicCompletionValuativeRel K w.val
    Units.map (algebraMap K (w.val.adicCompletion K)).toMonoidHom (U n / U m) ∈
      LocalFieldTheory.fieldPrincipalUnits (w.val.adicCompletion K)
        (sPlaceSexticCorrectionDepth K S ζ hζ w) := by
  have hr := sIntegerLocalQuotient_mem_upstream_fieldPrincipalUnits K S w
    (sPlaceSexticCorrectionDepth K S ζ hζ w)
    (sPlaceSexticCorrectionDepth_pos K S ζ hζ w) n m t
    (sIntegerPrincipalUnitModulus_le_prime_pow K S _ w ht) he
    (((mem_localValuationBox_iff_order_bounds K w.val
      (finiteIndexSUnitBoxWidth K S Γ) _).mp (hm w)).1)
  rw [map_div]
  exact hr

/-- The same ordinary modulus handles two independent active columns,
including all shared-prime zeros in any later symbol consumer. -/
theorem sIntegerSexticSPlaceCorrection_periodic
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (n₁ m₁ n₂ m₂ : NZI) (t₁ t₂ : 𝓞 K)
    (ht₁ : t₁ ∈ sIntegerSexticSPlaceModulus K S ζ hζ)
    (ht₂ : t₂ ∈ sIntegerSexticSPlaceModulus K S ζ hζ)
    (he₁ : n₁.val - m₁.val = algebraMap (𝓞 K) (S.integer K) t₁)
    (he₂ : n₂.val - m₂.val = algebraMap (𝓞 K) (S.integer K) t₂)
    (hm₁ : (sLocalNonzeroIntegerDiagonal K S m₁).2 ∈
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
    (hm₂ : (sLocalNonzeroIntegerDiagonal K S m₂).2 ∈
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    sIntegerSexticSPlaceCorrection K S ζ hζ (U n₁) (U n₂) =
        sIntegerSexticSPlaceCorrection K S ζ hζ (U m₁) (U m₂) ∧
      (sIntegerSexticSPlaceCorrection K S ζ hζ (U n₁) (U n₂))⁻¹ =
        (sIntegerSexticSPlaceCorrection K S ζ hζ (U m₁) (U m₂))⁻¹ := by
  have hB : sIntegerSexticSPlaceCorrection K S ζ hζ (U n₁) (U n₂) =
      sIntegerSexticSPlaceCorrection K S ζ hζ (U m₁) (U m₂) := by
    apply Finset.prod_congr rfl
    intro w _
    exact (exists_exact_finitePlaceHilbert_principalUnit_period K w.val
      ⟨6, by norm_num⟩ (by norm_num) (sPlaceCorrectionSexticRoots K ζ hζ)).choose_spec.2
      (U n₁) (U m₁) (U n₂) (U m₂)
      (sPlaceCorrection_ratio_mem K S ζ hζ Γ w n₁ m₁ t₁ ht₁ he₁ hm₁)
      (sPlaceCorrection_ratio_mem K S ζ hζ Γ w n₂ m₂ t₂ ht₂ he₂ hm₂)
  exact ⟨hB, congrArg Inv.inv hB⟩

/-- The fixed argument k can be ANY nonzero field element: it is not
required to be finite-active. In particular this applies independently to
k and -k in the raw fixed-frequency coefficient. -/
theorem sIntegerSexticSPlaceCorrection_fixed_first_periodic
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (k : Kˣ) (n m : NZI) (t : 𝓞 K)
    (ht : t ∈ sIntegerSexticSPlaceModulus K S ζ hζ)
    (he : n.val - m.val = algebraMap (𝓞 K) (S.integer K) t)
    (hm : (sLocalNonzeroIntegerDiagonal K S m).2 ∈
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    sIntegerSexticSPlaceCorrection K S ζ hζ k (U n) =
        sIntegerSexticSPlaceCorrection K S ζ hζ k (U m) ∧
      (sIntegerSexticSPlaceCorrection K S ζ hζ k (U n))⁻¹ =
        (sIntegerSexticSPlaceCorrection K S ζ hζ k (U m))⁻¹ := by
  have hB : sIntegerSexticSPlaceCorrection K S ζ hζ k (U n) =
      sIntegerSexticSPlaceCorrection K S ζ hζ k (U m) := by
    apply Finset.prod_congr rfl
    intro w _
    apply (exists_exact_finitePlaceHilbert_principalUnit_period K w.val
      ⟨6, by norm_num⟩ (by norm_num) (sPlaceCorrectionSexticRoots K ζ hζ)).choose_spec.2
      k k (U n) (U m)
    · rw [div_self', map_one]
      exact (LocalFieldTheory.fieldPrincipalUnits (w.val.adicCompletion K) _).one_mem
    · exact sPlaceCorrection_ratio_mem K S ζ hζ Γ w n m t ht he hm
  exact ⟨hB, congrArg Inv.inv hB⟩
end HeckeGeneral.Arithmetic
