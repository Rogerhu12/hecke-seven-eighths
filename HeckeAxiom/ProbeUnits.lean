import HeckeGeneral.Analysis.PhysicalProbePrincipal
import DedekindZetaZeroFree.Nonvanishing.Mellin.NormOneFourierSheetEstimates
import DedekindZetaZeroFree.Adeles.Archimedean.MixedEmbeddingComparison

/-!
# The skeleton's local multiplicative group is Axiom's `A.G`

The skeleton writes the `S`-local multiplicative group as the units of the mixed
space times the local unit groups at `S`; Axiom writes it as the units at each
infinite place times the same local unit groups. The infinite adele ring
equivalence identifies the two as topological groups. Every infinite place is
complex, so it carries the skeleton's product norm to Axiom's norm, the norm-one
subgroups onto each other and the skeleton's radial section to Axiom's. Hence
Axiom's sheet point over `T` at a norm-one `t` is the skeleton's `t · section T`.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic

namespace ProbeUnits

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)

local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local notation "R" => InfiniteAdeleRing.ringEquiv_mixedSpace K

/-- Units of the mixed space are the units at each infinite place. -/
def archUnits : (mixedEmbedding.mixedSpace K)ˣ ≃* ((w : InfinitePlace K) → w.Completionˣ) :=
  (Units.mapEquiv (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toMulEquiv).trans
    MulEquiv.piUnits

omit [NumberField K] in
theorem val_archUnits (u : (mixedEmbedding.mixedSpace K)ˣ) (w : InfinitePlace K) :
    ((archUnits u w : w.Completionˣ) : w.Completion) = (R).symm (u : mixedEmbedding.mixedSpace K) w :=
  rfl

omit [NumberField K] in
theorem val_archUnits_symm (y : (w : InfinitePlace K) → w.Completionˣ) :
    ((archUnits.symm y : (mixedEmbedding.mixedSpace K)ˣ) : mixedEmbedding.mixedSpace K) =
      R (fun w => (y w : w.Completion)) :=
  rfl

/-- The skeleton's `S`-local multiplicative group is Axiom's `A.G`. -/
def toG : sLocalMultiplicativeGroup K S ≃* A.G :=
  archUnits.prodCongr (MulEquiv.refl _)

theorem continuous_archUnits : Continuous (archUnits (K := K)) := by
  obtain ⟨_, hsymm, _⟩ := sArchModel_comparison K
  refine continuous_pi fun w => Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_apply w).comp (hsymm.comp Units.continuous_val)
  · have h : (fun u : (mixedEmbedding.mixedSpace K)ˣ => (((archUnits u w)⁻¹ : w.Completionˣ) :
        w.Completion)) = fun u => (R).symm ((u⁻¹ : (mixedEmbedding.mixedSpace K)ˣ) :
          mixedEmbedding.mixedSpace K) w := by
      funext u
      rw [← Pi.inv_apply, ← map_inv]
      rfl
    rw [h]
    exact (continuous_apply w).comp (hsymm.comp Units.continuous_coe_inv)

theorem continuous_archUnits_symm : Continuous (archUnits (K := K)).symm := by
  obtain ⟨hR, _, _⟩ := sArchModel_comparison K
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact hR.comp (continuous_pi fun w => Units.continuous_val.comp (continuous_apply w))
  · have h : (fun y : (w : InfinitePlace K) → w.Completionˣ =>
        (((archUnits.symm y)⁻¹ : (mixedEmbedding.mixedSpace K)ˣ) : mixedEmbedding.mixedSpace K)) =
        fun y => R (fun w => (((y w)⁻¹ : w.Completionˣ) : w.Completion)) := by
      funext y
      rw [← map_inv]
      rfl
    rw [h]
    exact hR.comp (continuous_pi fun w => Units.continuous_coe_inv.comp (continuous_apply w))

theorem continuous_toG : Continuous (toG A) :=
  (continuous_archUnits.comp continuous_fst).prodMk continuous_snd

theorem continuous_toG_symm : Continuous (toG A).symm :=
  (continuous_archUnits_symm.comp continuous_fst).prodMk continuous_snd

/-- `toG` as an isomorphism of topological groups. -/
def toGHomeo : sLocalMultiplicativeGroup K S ≃ₜ* A.G where
  __ := toG A
  continuous_toFun := continuous_toG A
  continuous_invFun := continuous_toG_symm A

include A in
/-- The archimedean factor of Axiom's norm is the mixed norm. -/
theorem arch_norm (m : mixedEmbedding.mixedSpace K) :
    (∏ w : InfinitePlace K, ‖(R).symm m w‖ ^ (2 : ℕ)) = mixedEmbedding.norm m := by
  rw [mixedEmbedding.norm_apply]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw := A.complex_place w
  rw [InfinitePlace.mult_isComplex ⟨w, hw⟩, mixedEmbedding.normAtPlace_apply_of_isComplex hw]
  have h : m.2 ⟨w, hw⟩ = InfinitePlace.Completion.extensionEmbedding w ((R).symm m w) := by
    conv_lhs => rw [← RingEquiv.apply_symm_apply (InfiniteAdeleRing.ringEquiv_mixedSpace K) m]
    rfl
  rw [h, (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
    (map_zero _)]

theorem norm_toG (x : sLocalMultiplicativeGroup K S) :
    A.norm (toG A x) = sLocalProductNorm K S x := by
  unfold SArithmeticData.norm sLocalProductNorm
  rw [← arch_norm A (x.1 : mixedEmbedding.mixedSpace K)]
  rfl

theorem toG_mem_G1_iff (x : sLocalMultiplicativeGroup K S) :
    toG A x ∈ A.G1 ↔ x ∈ sLocalNormOneGroup K S := by
  rw [mem_sLocalNormOneGroup, ← norm_toG]
  rfl

/-- The norm-one subgroups correspond. -/
def normOneEquiv : sLocalNormOneGroup K S ≃ₜ* A.G1 where
  toFun t := ⟨toG A t, (toG_mem_G1_iff A t).mpr t.2⟩
  invFun s := ⟨(toG A).symm s, (toG_mem_G1_iff A _).mp (by simp)⟩
  left_inv t := by ext1; simp
  right_inv s := by ext1; simp
  map_mul' s t := by ext1; simp
  continuous_toFun := ((continuous_toG A).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_toG_symm A).comp continuous_subtype_val).subtype_mk _

@[simp] theorem val_normOneEquiv (t : sLocalNormOneGroup K S) :
    (normOneEquiv A t : A.G) = toG A t :=
  rfl

include A in
theorem finrank_inv :
    ((Module.finrank ℚ K : ℝ)⁻¹) = 1 / (2 * (InfinitePlace.nrComplexPlaces K : ℝ)) := by
  have hreal : InfinitePlace.nrRealPlaces K = 0 :=
    InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by decide : 2 < 12)
      A.primitive_zeta12
  have h := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [hreal, zero_add] at h
  rw [← h]
  push_cast
  ring

/-- The skeleton's radial section is Axiom's radial section. -/
theorem toG_section (T : ℝ) (hT : 0 < T) :
    toG A (sLocalNormSection K S ⟨T, hT⟩) = A.radialSection T hT := by
  refine Prod.ext ?_ rfl
  funext w
  apply Units.ext
  change (R).symm (algebraMap ℝ (mixedEmbedding.mixedSpace K)
    (T ^ ((Module.finrank ℚ K : ℝ)⁻¹))) w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm
        ((T ^ (1 / (2 * (InfinitePlace.nrComplexPlaces K : ℝ))) : ℝ) : ℂ)
  rw [finrank_inv A, RingEquiv.eq_symm_apply,
    InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
  set a := algebraMap ℝ (mixedEmbedding.mixedSpace K)
    (T ^ (1 / (2 * (InfinitePlace.nrComplexPlaces K : ℝ))))
  have h : InfinitePlace.Completion.extensionEmbedding w ((R).symm a w) =
      a.2 ⟨w, A.complex_place w⟩ := by
    conv_rhs => rw [← RingEquiv.apply_symm_apply (InfiniteAdeleRing.ringEquiv_mixedSpace K) a]
    rfl
  rw [h]
  rfl

/-- The skeleton's local multiplicative group inside Axiom's units. -/
def toUnits (x : sLocalMultiplicativeGroup K S) : (SLocalProduct K A.Sf)ˣ :=
  ProbeSheet.localUnits A (toG A x)

theorem val_toUnits (x : sLocalMultiplicativeGroup K S) :
    ((toUnits A x : (SLocalProduct K A.Sf)ˣ) : SLocalProduct K A.Sf) =
      ((R).symm (x.1 : mixedEmbedding.mixedSpace K), fun v => ((x.2 v : (v.val.adicCompletion K)ˣ) :
        v.val.adicCompletion K)) :=
  rfl

/-- Axiom's sheet point over `T` at a norm-one `t` is the skeleton's `t · section T`. -/
theorem sheetPoint_normOneEquiv (T : ℝ) (hT : 0 < T) (t : sLocalNormOneGroup K S) :
    ProbeSheet.sheetPoint A T (normOneEquiv A t) =
      toUnits A ((t : sLocalMultiplicativeGroup K S) * sLocalNormSection K S ⟨T, hT⟩) := by
  unfold ProbeSheet.sheetPoint ProbeSheet.ell toUnits
  simp only [hT, ↓reduceDIte]
  rw [← toG_section A T hT, ← map_mul, val_normOneEquiv, ← map_mul]

end ProbeUnits

end HeckeAxiom
