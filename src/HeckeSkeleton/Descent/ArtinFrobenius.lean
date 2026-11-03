import HeckeSkeleton.Descent.ArtinFactors
import HeckeSkeleton.Descent.LocalNormCoefficients
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
import ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal
import ClassFieldTheory.AlgebraicNumberTheory.SUnit.Herbrand

/-!
Adapted from the 2026-10-11 cache candidate; see DESCENT_CODEX_REPORT_2.md for checks.

The element qprime is the class of the project's actual local uniformizer
in the genuine idele-class norm quotient. Its global norm-residue image
is proved to be the chosen finite-place Artin value. At an extension-
unramified place it generates the actual decomposition group, has order
equal to the actual prime inertia degree, and evaluates every Artin twist's
actual prime coefficient. No compatibility, order or generation hypothesis
is supplied.

No Euler-product identity, deleted continuation identity or FULL7/8 result
is asserted here. The word Frobenius refers to the reciprocity convention
of chosenFinitePlaceArtinMonoidHom; no separate arithmetic normalization
or residue-field power-map comparison is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Descent.ArtinFrobenius

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped NumberField IsMulCommutative Classical
open HeckeSkeleton.Descent.Artin
open HeckeSkeleton.Descent.LocalNorm
open GlobalClassFieldTheory.Reciprocity

@[instance_reducible]
private def frobeniusIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] : CommGroup (_root_.IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (_root_.IdeleGroup.principalSubgroup F)

attribute [local instance] frobeniusIdeleClassCommGroup

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
variable [Algebra F K] [FiniteDimensional F K] [IsAbelianGalois F K]

/-- Actual local insertion into the actual global norm quotient. -/
def localArtinNormClassMap (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* ArtinNormQuotient F K :=
  (artinNormClassMap F K).toMonoidHom.comp (localIdeleClassMap F v).toMonoidHom

@[simp] theorem localArtinNormClassMap_apply (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    localArtinNormClassMap F K v u =
      QuotientGroup.mk' (_root_.ideleClassNorm F K).range
        (_root_.IdeleGroup.finitePlaceIdeleClass v u) := by
  change artinNormClassMap F K (localIdeleClassMap F v u) = _
  rw [artinNormClassMap_apply, comparison_symm_localIdeleClassMap]

/-- The class of the project's genuine uniformizer, rather than an abstract
element of prescribed order. -/
def qprime (v : HeightOneSpectrum (𝓞 F)) : ArtinNormQuotient F K :=
  localArtinNormClassMap F K v (localUniformizerUnit F v)

/-- Actual local/global reciprocity on every local element. -/
theorem globalNormResidue_localArtinNormClassMap
    (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    globalNormResidueContinuousMulEquiv F K (localArtinNormClassMap F K v u) =
      chosenFinitePlaceArtinMonoidHom (K := F) (L := K) v u := by
  rw [localArtinNormClassMap_apply]
  change globalNormResidueContinuousMonoidHom F K
      (_root_.IdeleGroup.finitePlaceIdeleClass v u) = _
  rw [globalNormResidueContinuousMonoidHom_apply]
  exact DFunLike.congr_fun
    (globalNormResidueMonoidHom_comp_finitePlaceIdeleClass (K := F) (L := K) v) u

/-- Artin/Frobenius evaluation of the actual quotient uniformizer class. -/
theorem globalNormResidue_qprime (v : HeightOneSpectrum (𝓞 F)) :
    globalNormResidueContinuousMulEquiv F K (qprime F K v) =
      chosenFinitePlaceArtinMonoidHom (K := F) (L := K) v
        (localUniformizerUnit F v) :=
  globalNormResidue_localArtinNormClassMap F K v _

/-- Every quotient-dual character is evaluated on the actual local class. -/
@[simp] theorem localComponent_artinHeckeCharacter
    (ρ : ArtinFactorIndex F K) (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    localComponent F v (artinHeckeCharacter F K ρ) u =
      ρ (localArtinNormClassMap F K v u) := rfl

/-- Integral units have trivial actual quotient class at an unramified
extension place. The kernel statement is deduced from local reciprocity. -/
theorem localArtinNormClassMap_integerUnit_eq_one
    (v : HeightOneSpectrum (𝓞 F))
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v)
    (u : (v.adicCompletion F)ˣ)
    (hu : u ∈ (v.adicCompletionIntegers F).units) :
    localArtinNormClassMap F K v u = 1 := by
  have hker : u ∈ (chosenFinitePlaceArtinMonoidHom (K := F) (L := K) v).ker := by
    rw [chosenFinitePlaceArtinMonoidHom_ker]
    exact _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
      (K := F) (L := K) v hunram hu
  apply (globalNormResidueContinuousMulEquiv F K).injective
  rw [globalNormResidue_localArtinNormClassMap, map_one]
  exact MonoidHom.mem_ker.mp hker

/-- Thus all Artin factors are unramified wherever the actual extension is. -/
theorem unramifiedAt_artinHeckeCharacter
    (ρ : ArtinFactorIndex F K) (v : HeightOneSpectrum (𝓞 F))
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v) :
    UnramifiedAt F (artinHeckeCharacter F K ρ) v := by
  intro u hu
  rw [localComponent_artinHeckeCharacter,
    localArtinNormClassMap_integerUnit_eq_one F K v hunram u
      ((local_norm_one_iff_integral_unit F v u).mp hu), map_one]

/-- Local quotient classes depend only on normalized order. -/
theorem localArtinNormClassMap_eq_of_localOrder_eq
    (v : HeightOneSpectrum (𝓞 F))
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v)
    (u z : (v.adicCompletion F)ˣ)
    (horder : (_root_.FiniteIdeleGroup.localOrder v u).toAdd =
      (_root_.FiniteIdeleGroup.localOrder v z).toAdd) :
    localArtinNormClassMap F K v u = localArtinNormClassMap F K v z := by
  have hzero : (_root_.FiniteIdeleGroup.localOrder v (u * z⁻¹)).toAdd = 0 := by
    rw [map_mul, map_inv]
    change (_root_.FiniteIdeleGroup.localOrder v u).toAdd +
      -(_root_.FiniteIdeleGroup.localOrder v z).toAdd = 0
    rw [horder, add_neg_cancel]
  have hunit := (_root_.FiniteIdeleGroup.localOrder_eq_zero_iff v (u * z⁻¹)).mp hzero
  have h := localArtinNormClassMap_integerUnit_eq_one F K v hunram (u * z⁻¹) hunit
  rw [map_mul, map_inv] at h
  exact mul_inv_eq_one.mp h

/-- Every local class is an integral power of this literal qprime. -/
theorem localArtinNormClassMap_eq_qprime_zpow
    (v : HeightOneSpectrum (𝓞 F))
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v)
    (u : (v.adicCompletion F)ˣ) :
    localArtinNormClassMap F K v u =
      qprime F K v ^ (_root_.FiniteIdeleGroup.localOrder v u).toAdd := by
  let n := (_root_.FiniteIdeleGroup.localOrder v u).toAdd
  calc
    localArtinNormClassMap F K v u =
        localArtinNormClassMap F K v ((localUniformizerUnit F v) ^ n) := by
      apply localArtinNormClassMap_eq_of_localOrder_eq F K v hunram
      rw [map_zpow, Int.toAdd_zpow, upstreamLocalOrder_localUniformizerUnit]
      simp only [n, one_mul]
    _ = qprime F K v ^ n := map_zpow _ _ n

/-- The local Artin image is generated by the actual uniformizer's image. -/
theorem chosenFinitePlaceArtin_eq_uniformizer_zpow
    (v : HeightOneSpectrum (𝓞 F))
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v)
    (u : (v.adicCompletion F)ˣ) :
    chosenFinitePlaceArtinMonoidHom (K := F) (L := K) v u =
      chosenFinitePlaceArtinMonoidHom (K := F) (L := K) v
        (localUniformizerUnit F v) ^ (_root_.FiniteIdeleGroup.localOrder v u).toAdd := by
  calc
    chosenFinitePlaceArtinMonoidHom (K := F) (L := K) v u =
        globalNormResidueContinuousMulEquiv F K (localArtinNormClassMap F K v u) :=
      (globalNormResidue_localArtinNormClassMap F K v u).symm
    _ = globalNormResidueContinuousMulEquiv F K
        (qprime F K v ^ (_root_.FiniteIdeleGroup.localOrder v u).toAdd) :=
      congrArg (globalNormResidueContinuousMulEquiv F K)
        (localArtinNormClassMap_eq_qprime_zpow F K v hunram u)
    _ = globalNormResidueContinuousMulEquiv F K (qprime F K v) ^
        (_root_.FiniteIdeleGroup.localOrder v u).toAdd := map_zpow _ _ _
    _ = chosenFinitePlaceArtinMonoidHom (K := F) (L := K) v
        (localUniformizerUnit F v) ^ (_root_.FiniteIdeleGroup.localOrder v u).toAdd := by
      rw [globalNormResidue_qprime]

/-- Reconstructed in the 808 closure, without importing UnramifiedPrimeArtin. -/
theorem decompositionGroup_eq_zpowers_uniformizerArtin
    (v : HeightOneSpectrum (𝓞 F))
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v) :
    _root_.finitePlaceDecompositionGroup (K := F) (L := K) v =
      Subgroup.zpowers (chosenFinitePlaceArtinMonoidHom (K := F) (L := K) v
        (localUniformizerUnit F v)) := by
  rw [← chosenFinitePlaceArtinMonoidHom_range (K := F) (L := K) v]
  apply le_antisymm
  · rintro σ ⟨u, rfl⟩
    rw [chosenFinitePlaceArtin_eq_uniformizer_zpow F K v hunram u]
    exact Subgroup.zpow_mem_zpowers _ _
  · intro σ hσ
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
    exact ⟨localUniformizerUnit F v ^ n, map_zpow _ _ n⟩

/-- First exact order calibration: actual quotient order is local degree. -/
theorem orderOf_qprime_eq_localDegree
    (v : HeightOneSpectrum (𝓞 F))
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v) :
    orderOf (qprime F K v) = _root_.finitePlaceLocalDegree (K := F) (L := K) v := by
  calc
    orderOf (qprime F K v) = orderOf
        (chosenFinitePlaceArtinMonoidHom (K := F) (L := K) v
          (localUniformizerUnit F v)) := by
      rw [← globalNormResidue_qprime]
      exact ((globalNormResidueContinuousMulEquiv F K).toMulEquiv.orderOf_eq _).symm
    _ = Nat.card (Subgroup.zpowers
        (chosenFinitePlaceArtinMonoidHom (K := F) (L := K) v
          (localUniformizerUnit F v))) := (Nat.card_zpowers _).symm
    _ = Nat.card (_root_.finitePlaceDecompositionGroup (K := F) (L := K) v) := by
      rw [decompositionGroup_eq_zpowers_uniformizerArtin F K v hunram]
    _ = _root_.finitePlaceLocalDegree (K := F) (L := K) v :=
      _root_.finitePlaceDecompositionGroup_card_eq_localDegree (K := F) (L := K) v

/-- At an unramified extension place the local degree is the ordinary
residue degree. Both sides are actual ideal/completion invariants. -/
theorem localDegree_eq_inertiaDegIn
    (v : HeightOneSpectrum (𝓞 F))
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v) :
    _root_.finitePlaceLocalDegree (K := F) (L := K) v = v.asIdeal.inertiaDegIn (𝓞 K) := by
  let w := _root_.chosenFinitePlaceExtension (L := K) v
  let W := _root_.finitePlaceExtensionCentre (K := F) (L := K) v w
  letI : W.asIdeal.LiesOver v.asIdeal :=
    _root_.finitePlaceExtensionCentre_liesOver (K := F) (L := K) v w
  letI : IsGaloisGroup (K ≃ₐ[F] K) (𝓞 F) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (K ≃ₐ[F] K) (𝓞 F) (𝓞 K) F K
  letI : Algebra.IsUnramifiedAt (𝓞 F) W.asIdeal :=
    _root_.isUnramifiedAt_of_chosenFinitePlaceIsUnramified (K := F) (L := K) v hunram
  have he : v.asIdeal.ramificationIdxIn (𝓞 K) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal W.asIdeal (K ≃ₐ[F] K)]
    exact Ideal.ramificationIdx_eq_one W.asIdeal (𝓞 F)
  letI := _root_.finitePlaceMulAction F K
  calc
    _root_.finitePlaceLocalDegree (K := F) (L := K) v =
        Nat.card (_root_.finitePlaceDecompositionGroup (K := F) (L := K) v) :=
      (_root_.finitePlaceDecompositionGroup_card_eq_localDegree (K := F) (L := K) v).symm
    _ = Nat.card (MulAction.stabilizer (K ≃ₐ[F] K) W) := by
      rw [_root_.finitePlaceDecompositionGroup,
        _root_.absoluteValueDecompositionGroup_eq_finitePlaceStabilizer]
    _ = _root_.finiteLogPlaceLocalDegree F K W :=
      _root_.finitePlace_stabilizer_card_eq_localDegree F K W
    _ = v.asIdeal.inertiaDegIn (𝓞 K) := by
      unfold _root_.finiteLogPlaceLocalDegree
      rw [← W.asIdeal.over_def v.asIdeal]
      dsimp only
      rw [he, one_mul]

/-- The required exact order formula for every prime above v. -/
theorem orderOf_qprime_eq_inertiaDeg
    (v : HeightOneSpectrum (𝓞 F))
    (W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v})
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v) :
    orderOf (qprime F K v) = W.1.asIdeal.inertiaDeg (𝓞 F) := by
  letI : W.1.asIdeal.LiesOver v.asIdeal := by
    constructor
    have h := congrArg HeightOneSpectrum.asIdeal W.2
    simpa only [_root_.finitePlaceBelow_asIdeal] using h.symm
  letI : IsGaloisGroup (K ≃ₐ[F] K) (𝓞 F) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (K ≃ₐ[F] K) (𝓞 F) (𝓞 K) F K
  rw [orderOf_qprime_eq_localDegree F K v hunram,
    localDegree_eq_inertiaDegIn F K v hunram]
  exact Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal W.1.asIdeal (K ≃ₐ[F] K)

/-- Literal coefficient evaluation of each Artin character. -/
theorem primeCoefficient_artinHeckeCharacter
    (ρ : ArtinFactorIndex F K) (v : HeightOneSpectrum (𝓞 F))
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v) :
    primeCoefficient F (artinHeckeCharacter F K ρ) v = (ρ (qprime F K v) : ℂ) := by
  rw [primeCoefficient_of_unramified F _ v
    (unramifiedAt_artinHeckeCharacter F K ρ v hunram)]
  rfl

/-- Actual unramified Artin-twist prime coefficient, ready for finite-dual
Euler-factor multiplication outside the common finite bad set. -/
theorem primeCoefficient_artinTwist (χ : HeckeCharacter F)
    (ρ : ArtinFactorIndex F K) (v : HeightOneSpectrum (𝓞 F))
    (hχ : UnramifiedAt F χ v)
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v) :
    primeCoefficient F (χ * artinHeckeCharacter F K ρ) v =
      primeCoefficient F χ v * (ρ (qprime F K v) : ℂ) := by
  rw [primeCoefficient_of_unramified F _ v
      (hχ.mul F (unramifiedAt_artinHeckeCharacter F K ρ v hunram)),
    primeCoefficient_of_unramified F χ v hχ]
  rfl

end HeckeSkeleton.Descent.ArtinFrobenius
