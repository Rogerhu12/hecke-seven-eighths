import HeckeSkeleton.ActualHeckeNormPullback
import HeckeGeneral.Characters.FiniteCircleDual
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.TopologicalGlobalNormResidue

/-! Actual Artin characters of the finite norm quotient of a finite abelian extension. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Descent.Artin

open scoped NumberField IsMulCommutative Classical
open HeckeGeneral.Characters HeckeGeneral.Characters.NormPullbackDraft

@[instance_reducible]
private def artinFactorsIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] : CommGroup (_root_.IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (_root_.IdeleGroup.principalSubgroup F)

attribute [local instance] artinFactorsIdeleClassCommGroup

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
variable [Algebra F K] [FiniteDimensional F K] [IsAbelianGalois F K]

/-- The genuine ordinary relative-norm quotient, without replacing its map. -/
abbrev ArtinNormQuotient :=
  _root_.IdeleClassGroup F ⧸ (_root_.ideleClassNorm F K).range

local instance artinNormQuotientFinite : Finite (ArtinNormQuotient F K) :=
  Finite.of_equiv (K ≃ₐ[F] K)
    (GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMulEquiv F K).symm.toEquiv

local instance artinNormQuotientDiscrete : DiscreteTopology (ArtinNormQuotient F K) :=
  GlobalClassFieldTheory.Reciprocity.ideleClassNormQuotient_discreteTopology F K

/-- The full finite dual; no selected or incomplete list of Artin characters. -/
abbrev ArtinFactorIndex := ArtinNormQuotient F K →* Circle

local instance artinFactorIndexFintype : Fintype (ArtinFactorIndex F K) :=
  Fintype.ofFinite _

/-- Actual quotient map on Mathlib classes, transported by the actual comparison. -/
def artinNormClassMap : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ArtinNormQuotient F K :=
  (GlobalClassFieldTheory.Reciprocity.ideleClassNormQuotientContinuousMonoidHom F K).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib F).symm)

@[simp] theorem artinNormClassMap_apply (x : NumberField.IdeleClassGroup (𝓞 F) F) :
    artinNormClassMap F K x =
      QuotientGroup.mk' (_root_.ideleClassNorm F K).range
        ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib F).symm x) := rfl

/-- Every quotient-dual element produces a continuous unitary Hecke character. -/
def artinHeckeCharacter (ρ : ArtinFactorIndex F K) : HeckeCharacter F where
  toMonoidHom := ρ.comp (artinNormClassMap F K).toMonoidHom
  continuous_toFun :=
    (continuous_of_discreteTopology : Continuous ρ).comp (artinNormClassMap F K).continuous

@[simp] theorem artinHeckeCharacter_apply
    (ρ : ArtinFactorIndex F K) (x : NumberField.IdeleClassGroup (𝓞 F) F) :
    artinHeckeCharacter F K ρ x = ρ (artinNormClassMap F K x) := rfl

@[simp] theorem artinHeckeCharacter_one : artinHeckeCharacter F K 1 = 1 := by
  apply ContinuousMonoidHom.ext
  intro x
  rfl

/-- Norms have trivial class in this specific quotient. -/
@[simp] theorem artinNormClassMap_mathlibIdeleClassNorm
    (x : NumberField.IdeleClassGroup (𝓞 K) K) :
    artinNormClassMap F K (mathlibIdeleClassNorm F K x) = 1 := by
  rw [artinNormClassMap_apply, mathlibIdeleClassNorm_apply,
    (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib F).symm_apply_apply]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨(_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).symm x, rfl⟩

/-- Every genuinely constructed Artin character is killed by actual norm pullback. -/
@[simp] theorem heckeNormPullback_artinHeckeCharacter (ρ : ArtinFactorIndex F K) :
    heckeNormPullback F K (artinHeckeCharacter F K ρ) = 1 := by
  apply ContinuousMonoidHom.ext
  intro x
  change ρ (artinNormClassMap F K (mathlibIdeleClassNorm F K x)) = 1
  rw [artinNormClassMap_mathlibIdeleClassNorm, map_one]

/-- The actual quotient map is surjective, so distinct dual elements stay distinct. -/
theorem artinHeckeCharacter_injective : Function.Injective (artinHeckeCharacter F K) := by
  intro ρ σ h
  apply MonoidHom.ext
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (_root_.ideleClassNorm F K).range y
  have hz := congrArg
    (fun ψ : HeckeCharacter F =>
      ψ ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib F) z)) h
  simpa only [artinHeckeCharacter_apply, artinNormClassMap_apply,
    (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib F).symm_apply_apply] using hz

theorem artinHeckeCharacter_finiteOrder (ρ : ArtinFactorIndex F K) :
    FiniteOrder (artinHeckeCharacter F K ρ) := by
  apply (finiteOrder_iff_pointwise _).mpr
  refine ⟨Nat.card (ArtinNormQuotient F K), Nat.card_pos, ?_⟩
  intro x
  change ρ (artinNormClassMap F K x) ^ Nat.card (ArtinNormQuotient F K) = 1
  rw [← map_pow, pow_card_eq_one', map_one]

/-- All Artin twists, counted once each. -/
def artinCharacters : Finset (HeckeCharacter F) := by
  classical
  exact Finset.univ.image (artinHeckeCharacter F K)

theorem mem_artinCharacters_iff (ψ : HeckeCharacter F) :
    ψ ∈ artinCharacters F K ↔
      ∃ ρ : ArtinFactorIndex F K, artinHeckeCharacter F K ρ = ψ := by
  classical
  simp only [artinCharacters, Finset.mem_image, Finset.mem_univ, true_and]

theorem one_mem_artinCharacters : (1 : HeckeCharacter F) ∈ artinCharacters F K := by
  apply (mem_artinCharacters_iff F K 1).mpr
  exact ⟨1, artinHeckeCharacter_one F K⟩

/-- All Artin twists, counted once each. -/
def artinFactors (χ : HeckeCharacter F) : Finset (HeckeCharacter F) := by
  classical
  exact Finset.univ.image (fun ρ : ArtinFactorIndex F K => χ * artinHeckeCharacter F K ρ)

theorem artinFactors_eq_image (χ : HeckeCharacter F) :
    artinFactors F K χ = (artinCharacters F K).image (fun δ => χ * δ) := by
  classical
  simp only [artinFactors, artinCharacters, Finset.image_image, Function.comp_def]

theorem mem_artinFactors_iff (χ ψ : HeckeCharacter F) :
    ψ ∈ artinFactors F K χ ↔
      ∃ ρ : ArtinFactorIndex F K, χ * artinHeckeCharacter F K ρ = ψ := by
  classical
  simp only [artinFactors, Finset.mem_image, Finset.mem_univ, true_and]

theorem target_mem_artinFactors (χ : HeckeCharacter F) : χ ∈ artinFactors F K χ := by
  apply (mem_artinFactors_iff F K χ χ).mpr
  exact ⟨1, by rw [artinHeckeCharacter_one, mul_one]⟩

/-- Every member has the same actual norm pullback, with no common-fiber assumption. -/
theorem artinFactors_common_normPullback (χ : HeckeCharacter F)
    {ψ : HeckeCharacter F} (hψ : ψ ∈ artinFactors F K χ) :
    heckeNormPullback F K ψ = heckeNormPullback F K χ := by
  obtain ⟨ρ, rfl⟩ := (mem_artinFactors_iff F K χ ψ).mp hψ
  rw [heckeNormPullback_mul, heckeNormPullback_artinHeckeCharacter, mul_one]

theorem artinTwist_injective (χ : HeckeCharacter F) :
    Function.Injective (fun ρ : ArtinFactorIndex F K => χ * artinHeckeCharacter F K ρ) := by
  intro ρ σ h
  exact artinHeckeCharacter_injective F K (mul_left_cancel h)

/-- The entire Artin dual has the extension degree, proved using actual reciprocity. -/
theorem natCard_artinFactorIndex : Nat.card (ArtinFactorIndex F K) = Module.finrank F K := by
  calc
    Nat.card (ArtinFactorIndex F K) = Nat.card (ArtinNormQuotient F K) :=
      natCard_circleDual (ArtinNormQuotient F K)
    _ = Nat.card (K ≃ₐ[F] K) := Nat.card_congr
      (GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMulEquiv F K).toEquiv
    _ = Module.finrank F K := IsGalois.card_aut_eq_finrank F K

theorem card_artinFactors (χ : HeckeCharacter F) :
    (artinFactors F K χ).card = Module.finrank F K := by
  classical
  rw [artinFactors, Finset.card_image_of_injective _ (artinTwist_injective F K χ),
    Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact natCard_artinFactorIndex F K

end HeckeSkeleton.Descent.Artin
