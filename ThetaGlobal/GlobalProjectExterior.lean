import ThetaGlobal.GlobalCoreSource
import ThetaGlobal.GlobalProjectRadial
import DedekindZetaZeroFree.Theta.Whittaker.ExteriorSlotExtraction
import DedekindZetaZeroFree.Theta.Digits.SUnitReindexing

/-!
# Exterior compact invariance for arbitrary tensors at the fixed bad places

Changing the archimedean K-type or the finite vectors in S preserves the
exterior spherical reference.  This file derives the resulting adelic
right invariance from `SourceFactorization.finite_intertwining` and
`spherical_reference`, including the full compact product by density.
No assumption that every vector of the residual module is spherical is
made: the theorem applies to the actual tensors supported on `D.bad`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section

namespace ThetaGlobal.GlobalProjectExterior

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open MeasureTheory
open scoped NumberField Classical Topology

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (D : SourceFactorization R Q T)

local notation "V" => actualLocal R D.finiteData

def badStage : RestrictedTensorSimple.Level D.bad := ⟨D.bad, le_rfl⟩

def badTensor (x : ∀ p : D.bad, V p) :
    RestrictedTensorSimple.Core V D.references D.bad :=
  RestrictedTensorSimple.stageInclusion V D.references D.bad (badStage R D)
    (PiTensorProduct.tprod ℂ x)

def badVector (x : ∀ p : D.bad, V p) : sameResidueModule T :=
  GlobalCoreSource.coreVector T D (badTensor R D x)

theorem exterior_not_in_bad (p : KPFinitePlace F) (hp : p ∉ R.A.Sf) :
    Sum.inr p ∉ D.bad := by
  rw [D.bad_exact]
  simp only [Sum.inr_ne_inl, false_and, exists_false, Sum.inr.injEq, false_or]
  rintro ⟨q, hq, hmem⟩
  subst q
  exact hp hmem

/-- Enlarge the actual pure tensor by a single exterior reference slot. -/
theorem badVector_stage_with_exterior (x : ∀ p : D.bad, V p)
    (p : KPFinitePlace F) (hp : p ∉ R.A.Sf) :
    ∃ (s : RestrictedTensorSimple.Level D.bad) (hq : Sum.inr p ∈ s.val)
      (y : ∀ w : s.val, V w),
      D.coreMap (RestrictedTensorSimple.stageInclusion V D.references D.bad s
        (PiTensorProduct.tprod ℂ y)) = (badVector R D x).val ∧
      y ⟨Sum.inr p, hq⟩ = D.references (Sum.inr p) := by
  let s := badStage R D
  have hn : Sum.inr p ∉ s.val := exterior_not_in_bad R D p hp
  let t : RestrictedTensorSimple.Level D.bad :=
    ⟨insert (Sum.inr p) s.val, s.property.trans (Finset.subset_insert _ _)⟩
  let y : ∀ w : t.val, V w := fun w =>
    if h : w.val ∈ s.val then x ⟨w.val, h⟩ else D.references w
  have he : RestrictedTensorSimple.stageInclusion V D.references D.bad t
      (PiTensorProduct.tprod ℂ y) =
      RestrictedTensorSimple.stageInclusion V D.references D.bad s
        (PiTensorProduct.tprod ℂ x) := by
    have h := LinearMap.congr_fun
      (RestrictedTensorSimple.inclusion_insert V D.references D.bad s t
        (Finset.subset_insert _ _)) (PiTensorProduct.tprod ℂ x)
    simp only [LinearMap.comp_apply, RestrictedTensorSimple.insert_pure] at h
    refine Eq.trans ?_ h
    congr 2
    funext w
    dsimp only [y]
    split_ifs <;> rfl
  refine ⟨t, Finset.mem_insert_self _ _, y, ?_, ?_⟩
  · rw [he]
    rfl
  · simp [y, hn]

theorem badVector_exterior_spherical (x : ∀ p : D.bad, V p)
    (p : KPFinitePlace F) (hp : p ∉ R.A.Sf)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (ha : a ∈ KPAdelicCoverRestrictedProduct.compact
      F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)) (g : Group R) :
    (badVector R D x).val
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection
          F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) a)) =
      (badVector R D x).val g := by
  obtain ⟨s, hq, y, hy, href⟩ := badVector_stage_with_exterior R D x p hp
  have ht := D.finite_intertwining p a s hq y g
  have hfixed := (D.spherical_reference p hp).2 a ha
  rw [href, hfixed] at ht
  have hu : Function.update y ⟨Sum.inr p, hq⟩ (D.references (Sum.inr p)) = y := by
    rw [← href, Function.update_eq_self]
  rw [hu, hy] at ht
  exact ht.symm

def FullExteriorInvariant (f : Functions R) : Prop :=
  ∀ (k : KPAdelicCoverRestrictedProduct.RestrictedCover
      F R.A.zeta12 R.A.primitive_zeta12),
    (∀ w, k w ∈ DigitMasks.exteriorFactor R w) → ∀ g,
    f (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 k)) = f g

/-- Local exterior reference invariance extends to the full compact
restricted-product subgroup by continuity and coordinate density. -/
theorem fullExteriorInvariant_of_local (f : Functions R) (hf : Continuous f)
    (hlocal : ∀ (p : KPFinitePlace F), p ∉ R.A.Sf →
      ∀ a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p),
      a ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) →
      ∀ g, f (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12
          (Sum.inr p) a)) = f g) :
    FullExteriorInvariant R f := by
  intro k hk g
  letI : ∀ w : KPHilbert.Place F,
      TopologicalSpace (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 w) :=
    KPAdelicCoverRestrictedProduct.localTopology F R.A.zeta12 R.A.primitive_zeta12
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover
      F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  let H := (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12).comp
    (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12)
  let C := KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12
  let J : Subgroup (KPAdelicCoverRestrictedProduct.RestrictedCover
      F R.A.zeta12 R.A.primitive_zeta12) :=
    { carrier := {a | ∀ h : Group R, f (h * H a) = f h}
      one_mem' := by intro h; simp
      mul_mem' := by
        intro a b ha hb h
        rw [map_mul, ← mul_assoc, hb, ha]
      inv_mem' := by
        intro a ha h
        have he := ha (h * H a⁻¹)
        simpa only [map_inv, mul_assoc, inv_mul_cancel, mul_one] using he.symm }
  have hclosed : IsClosed (J : Set _) := by
    change IsClosed {a | ∀ h : Group R, f (h * H a) = f h}
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro h
    exact isClosed_eq (hf.comp
      (continuous_const.mul (QuotientGroup.continuous_mk.comp QuotientGroup.continuous_mk)))
      continuous_const
  have hsingle : RestrictedProductDensity.singleSet C (DigitMasks.exteriorFactor R) ⊆
      (J : Set _) := by
    rintro a ⟨w, b, hb, rfl⟩ h
    cases w with
    | inl w =>
      have he : b = 1 := hb
      simp [he, H]
    | inr p =>
      by_cases hp : p ∉ R.A.Sf
      · exact hlocal p hp b (DigitMasks.exteriorFactor_le_compact R _ hb) h
      · have he : b = 1 := by
          simpa only [DigitMasks.exteriorFactor, dif_neg hp, Subgroup.mem_bot] using hb
        simp [he, H]
  have hle : Subgroup.closure (RestrictedProductDensity.singleSet C
      (DigitMasks.exteriorFactor R)) ≤ J := (Subgroup.closure_le J).mpr hsingle
  have hd := RestrictedProductDensity.closure_closure_singleSet_eq_forall_mem C
    (DigitMasks.exteriorFactor R) (DigitMasks.exteriorFactor_closed R)
  have hmem : k ∈ closure (Subgroup.closure (RestrictedProductDensity.singleSet C
      (DigitMasks.exteriorFactor R)) : Set _) := by
    rw [hd]
    exact hk
  exact (closure_minimal hle hclosed hmem) g

theorem badVector_fullExteriorInvariant (x : ∀ p : D.bad, V p) :
    FullExteriorInvariant R (badVector R D x).val :=
  fullExteriorInvariant_of_local R _ (badVector R D x).property.2.1
    (badVector_exterior_spherical R D x)

/-- The same result for any presentation of the fixed bad stage.  This
applies directly to `ProjectedFiniteMellin.frozenStage`, whose equality
with `D.bad` is stored by the actual selected source. -/
theorem fixedStage_fullExteriorInvariant
    (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (x : ∀ p : s.val, V p) :
    FullExteriorInvariant R (D.coreMap
      (RestrictedTensorSimple.stageInclusion V D.references D.bad s
        (PiTensorProduct.tprod ℂ x))) := by
  obtain rfl : s = badStage R D := Subtype.ext hs
  exact badVector_fullExteriorInvariant R D x

/-- Re-present an actual frozen pure tensor at the canonical bad stage.
Only subtype proof terms are transported; no local vector is changed. -/
theorem fixedStage_eq_badVector
    (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (x : ∀ p : s.val, V p) :
    D.coreMap (RestrictedTensorSimple.stageInclusion V D.references D.bad s
      (PiTensorProduct.tprod ℂ x)) =
      (badVector R D (fun p => x ⟨p.val, hs.symm ▸ p.property⟩)).val := by
  obtain rfl : s = badStage R D := Subtype.ext hs
  rfl

theorem upper_fullExteriorInvariant (f : Functions R) (hf : FullExteriorInvariant R f) :
    FullExteriorInvariant R (upper R Q.dq f) := by
  intro k hk g
  unfold upper
  apply integral_congr_ae
  filter_upwards [] with q
  rw [← mul_assoc, hf k hk]

end ThetaGlobal.GlobalProjectExterior
