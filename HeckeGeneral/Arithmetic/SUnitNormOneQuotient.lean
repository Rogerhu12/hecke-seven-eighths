import HeckeGeneral.Arithmetic.SUnitCompactRepresentatives
import HeckeGeneral.Arithmetic.SUnitDiscreteness
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The actual norm-one S-local group and its compact S-unit quotient

The product norm uses the mixed archimedean algebra and the actual finite
completions. Its positive values define a continuous homomorphism to real
units. The norm-one group is its kernel, and the diagonal subgroup consists
of the images of the given global S-units.

Compact representatives in the ambient local group are first intersected
with the closed norm-one level and lifted to that subgroup. Their images
cover the quotient by every finite-index subgroup of the global S-units.
No Haar measure or fundamental domain is selected by this construction.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField NumberField.mixedEmbedding IsDedekindDomain
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem sLocalProductNorm_pos (x : sLocalMultiplicativeGroup K S) :
    0 < sLocalProductNorm K S x := by
  apply mul_pos
  · exact lt_of_le_of_ne (mixedEmbedding.norm_nonneg (x.1 : mixedSpace K))
      (sLocal_archNorm_ne_zero K S x).symm
  · exact sFiniteProductNorm_pos K S x.2

theorem continuous_sLocalProductNorm : Continuous (sLocalProductNorm K S) := by
  exact ((mixedEmbedding.continuous_norm K).comp
    (Units.continuous_val.comp continuous_fst)).mul
      ((continuous_sFiniteProductNorm K S).comp continuous_snd)

@[simp] theorem sLocalProductNorm_one :
    sLocalProductNorm K S (1 : sLocalMultiplicativeGroup K S) = 1 := by
  simp [sLocalProductNorm]

/-- The actual positive product norm, retaining its real-unit value. -/
def sLocalProductNormHom : sLocalMultiplicativeGroup K S →* ℝˣ where
  toFun x := Units.mk0 (sLocalProductNorm K S x) (sLocalProductNorm_pos K S x).ne'
  map_one' := by
    apply Units.ext
    exact sLocalProductNorm_one K S
  map_mul' x y := by
    apply Units.ext
    exact sLocalProductNorm_mul K S x y

theorem continuous_sLocalProductNormHom : Continuous (sLocalProductNormHom K S) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_sLocalProductNorm K S
  · exact (continuous_sLocalProductNorm K S).inv₀
      (fun x => (sLocalProductNorm_pos K S x).ne')

/-- The norm-one subgroup carries its actual ambient induced topology. -/
def sLocalNormOneGroup : Subgroup (sLocalMultiplicativeGroup K S) :=
  (sLocalProductNormHom K S).ker

@[simp] theorem mem_sLocalNormOneGroup (x : sLocalMultiplicativeGroup K S) :
    x ∈ sLocalNormOneGroup K S ↔ sLocalProductNorm K S x = 1 := by
  change Units.mk0 (sLocalProductNorm K S x) (sLocalProductNorm_pos K S x).ne' = 1 ↔ _
  constructor
  · exact fun h => congrArg Units.val h
  · exact fun h => Units.ext h

theorem isClosed_sLocalNormOneGroup :
    IsClosed (sLocalNormOneGroup K S : Set (sLocalMultiplicativeGroup K S)) := by
  have hlevel : (sLocalNormOneGroup K S : Set (sLocalMultiplicativeGroup K S)) =
      {x | sLocalProductNorm K S x = 1} := by
    ext x
    exact mem_sLocalNormOneGroup K S x
  rw [hlevel]
  exact isClosed_eq (continuous_sLocalProductNorm K S) continuous_const

/-- The product formula puts every actual diagonal S-unit into the norm-one group. -/
def sLocalNormOneDiagonal : S.unit K →* sLocalNormOneGroup K S where
  toFun u := ⟨sLocalDiagonal K S u,
    (mem_sLocalNormOneGroup K S _).mpr (sLocalProductNorm_diagonal K S u)⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (sLocalDiagonal K S)
  map_mul' u v := by
    apply Subtype.ext
    exact map_mul (sLocalDiagonal K S) u v

theorem sLocalNormOneDiagonal_injective :
    Function.Injective (sLocalNormOneDiagonal K S) := by
  intro u v huv
  apply sLocalDiagonal_injective K S
  exact congrArg (fun x : sLocalNormOneGroup K S =>
    (x : sLocalMultiplicativeGroup K S)) huv

/-- The subgroup in the quotient is the literal diagonal image of Γ. -/
def sLocalNormOneGamma (Γ : Subgroup (S.unit K)) : Subgroup (sLocalNormOneGroup K S) :=
  Γ.map (sLocalNormOneDiagonal K S)

theorem sLocalNormOneGamma_eq_comap (Γ : Subgroup (S.unit K)) :
    sLocalNormOneGamma K S Γ =
      (Γ.map (sLocalDiagonal K S)).comap (sLocalNormOneGroup K S).subtype := by
  ext x
  change x ∈ Γ.map (sLocalNormOneDiagonal K S) ↔
    (x : sLocalMultiplicativeGroup K S) ∈ Γ.map (sLocalDiagonal K S)
  rw [Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, he⟩
    exact ⟨u, hu, congrArg (fun x : sLocalNormOneGroup K S =>
      (x : sLocalMultiplicativeGroup K S)) he⟩
  · rintro ⟨u, hu, he⟩
    exact ⟨u, hu, Subtype.ext he⟩

theorem isClosed_sLocalNormOneGamma (Γ : Subgroup (S.unit K)) :
    IsClosed (sLocalNormOneGamma K S Γ : Set (sLocalNormOneGroup K S)) := by
  rw [sLocalNormOneGamma_eq_comap]
  exact (isClosed_sLocalDiagonal_map K S Γ).preimage continuous_subtype_val

/-- Intersect the ambient representative set with norm one before lifting it. -/
theorem exists_compact_sLocalNormOne_representatives
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex] :
    ∃ D : Set (sLocalNormOneGroup K S), IsCompact D ∧
      ∀ x : sLocalNormOneGroup K S, ∃ g : Γ,
        sLocalNormOneDiagonal K S (g : S.unit K) * x ∈ D := by
  obtain ⟨C, hC, hrep⟩ := exists_compact_sUnit_normOne_representatives K S Γ
  let D : Set (sLocalNormOneGroup K S) :=
    Subtype.val ⁻¹' (C ∩ (sLocalNormOneGroup K S : Set (sLocalMultiplicativeGroup K S)))
  have hlevel := isClosed_sLocalNormOneGroup K S
  have hD : IsCompact D :=
    hlevel.isClosedEmbedding_subtypeVal.isCompact_preimage (hC.inter_right hlevel)
  refine ⟨D, hD, ?_⟩
  intro x
  obtain ⟨g, hg⟩ := hrep (x : sLocalMultiplicativeGroup K S)
    ((mem_sLocalNormOneGroup K S _).mp x.property)
  refine ⟨g, hg, ?_⟩
  exact (sLocalNormOneDiagonal K S (g : S.unit K) * x).property

abbrev SUnitNormOneQuotient (Γ : Subgroup (S.unit K)) :=
  sLocalNormOneGroup K S ⧸ sLocalNormOneGamma K S Γ

/-- Compactness follows from the actual compact representative set, although
the norm-one local group itself is generally noncompact. -/
instance compactSpace_sUnitNormOneQuotient (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex] :
    CompactSpace (SUnitNormOneQuotient K S Γ) := by
  obtain ⟨D, hD, hrep⟩ := exists_compact_sLocalNormOne_representatives K S Γ
  have hsurj : (QuotientGroup.mk : sLocalNormOneGroup K S →
      SUnitNormOneQuotient K S Γ) '' D = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, hg⟩ := hrep x
    have hmem : sLocalNormOneDiagonal K S (g : S.unit K) ∈ sLocalNormOneGamma K S Γ :=
      ⟨(g : S.unit K), g.property, rfl⟩
    have hq : (sLocalNormOneDiagonal K S (g : S.unit K) :
        SUnitNormOneQuotient K S Γ) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    refine ⟨sLocalNormOneDiagonal K S (g : S.unit K) * x, hg, ?_⟩
    rw [QuotientGroup.mk_mul, hq]
    exact one_mul (x : SUnitNormOneQuotient K S Γ)
  apply isCompact_univ_iff.mp
  rw [← hsurj]
  exact hD.image QuotientGroup.continuous_mk

/-- Closedness of the actual diagonal image gives the separated quotient. -/
instance t1Space_sUnitNormOneQuotient (Γ : Subgroup (S.unit K)) :
    T1Space (SUnitNormOneQuotient K S Γ) := by
  let : IsClosed (sLocalNormOneGamma K S Γ : Set (sLocalNormOneGroup K S)) :=
    isClosed_sLocalNormOneGamma K S Γ
  exact QuotientGroup.instT1Space

end HeckeGeneral.Arithmetic
