import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.WordGeometry

/-!
# Finite matrix products for every frozen pure tensor

This is the finite counterpart of `FiniteArchProduct`: the vector need not
be the source's selected Gaussian or selected digit vector.  The proof
uses only the actual local actions, their stored intertwining with the
global core map, and the stored product of Whittaker functionals at one.

The normalized form retains the actual Fourier coefficient of this same
pure tensor at one.  This is the scalar that must be canceled, on both
sides, when forming the direct/reflected Mellin quotient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.FiniteCoreProduct

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.KPAdelicCoverRestrictedProduct
open DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open scoped Classical NumberField BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)

theorem arch_mem (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (w : InfinitePlace F) : Sum.inl w ∈ s.val := by
  rw [hs, D.bad_exact]
  exact Or.inl ⟨w, rfl⟩

theorem finite_mem (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (q : R.A.Sf) : Sum.inr q.val ∈ s.val := by
  rw [hs, D.bad_exact]
  exact Or.inr ⟨q.val, rfl, q.property⟩

theorem finite_of_mem (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val) : q ∈ R.A.Sf := by
  rw [hs, D.bad_exact] at hq
  simpa only [Sum.inr_ne_inl, false_and, exists_false, false_or,
    Sum.inr.injEq, exists_eq_left'] using hq

/-- The exact frozen-stage coordinate dictionary; all finite places of S
and all complex places occur once. -/
def placeEquiv (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad) :
    (InfinitePlace F ⊕ R.A.Sf) ≃ s.val where
  toFun p := match p with
    | Sum.inl w => ⟨Sum.inl w, arch_mem R D s hs w⟩
    | Sum.inr q => ⟨Sum.inr q.val, finite_mem R D s hs q⟩
  invFun p := match h : p.val with
    | Sum.inl w => Sum.inl w
    | Sum.inr q => Sum.inr ⟨q, finite_of_mem R D s hs q (h ▸ p.property)⟩
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨p, hp⟩; cases p <;> rfl

def stageFunction (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p.val) : Functions R :=
  D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
    (PiTensorProduct.tprod ℂ x))

def stageCoefficient (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p.val) (g : Group R) : ℂ :=
  fourier R Q.dq (stageFunction R D s x) g

theorem stageCoefficient_one (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p.val) :
    stageCoefficient R D s x 1 = ∏ p : s.val, D.ell p (x p) :=
  D.product_exact s x

variable (a : ∀ q : KPFinitePlace F,
  KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))

def finiteRaw (p : KPHilbert.Place F) :
    KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p :=
  match p with
  | Sum.inl _ => 1
  | Sum.inr q => a q

def finiteAction (p : KPHilbert.Place F) :
    actualLocal R D.finiteData p → actualLocal R D.finiteData p :=
  match p with
  | Sum.inl _ => id
  | Sum.inr q =>
    KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
      R.A.primitive_zeta12 q (D.finiteData q).inducing
      (D.finiteData q).inducing.polarization (D.finiteData q).haar
      (D.finiteData q).haar_integer
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) (a q))

theorem finite_intertwining (s : RestrictedTensorSimple.Level D.bad) (p : s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p.val) (g : Group R) :
    stageFunction R D s (Function.update x p (finiteAction R D a p.val (x p))) g =
      stageFunction R D s x
        (g * scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (localInjection F R.A.zeta12 R.A.primitive_zeta12 p.val (finiteRaw R a p.val))) := by
  rcases p with ⟨p, hp⟩
  cases p with
  | inl w =>
    simp only [finiteAction, id_eq, Function.update_eq_self, finiteRaw, map_one, mul_one]
  | inr q => exact D.finite_intertwining q (a q) s hp x g

def finiteWord (s : RestrictedTensorSimple.Level D.bad) : Group R :=
  (Finset.univ.toList.map (fun p : s.val =>
    scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (localInjection F R.A.zeta12 R.A.primitive_zeta12 p.val (finiteRaw R a p.val)))).prod

theorem finiteWord_eq_finiteBase (s : RestrictedTensorSimple.Level D.bad)
    (hs : s.val = D.bad) : finiteWord R D a s = (finiteBase (R := R) a).val := by
  let φ := (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12).comp
    (amalgamation F R.A.zeta12 R.A.primitive_zeta12)
  rw [finiteBase_val]
  change (Finset.univ.toList.map (fun p : s.val =>
    φ (localToRestricted F R.A.zeta12 R.A.primitive_zeta12 p.val
      (finiteRaw R a p.val)))).prod = φ (finiteTuple (R := R) a)
  have hm := map_list_prod φ (Finset.univ.toList.map (fun p : s.val =>
    localToRestricted F R.A.zeta12 R.A.primitive_zeta12 p.val (finiteRaw R a p.val)))
  simp only [List.map_map, Function.comp_def] at hm
  rw [← hm]
  apply congrArg φ
  apply RestrictedProduct.ext
  intro p
  rw [restricted_list_single_eval]
  have hin (i : s.val) := list_single_product
    (G := fun p => KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p)
    (fun p : s.val => p.val) Subtype.val_injective
    (fun p => finiteRaw R a p.val) Finset.univ.toList (Finset.nodup_toList _) i
  have hout (hp : p ∉ s.val) := list_single_product_off
    (G := fun p => KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p)
    (fun p : s.val => p.val) (fun p => finiteRaw R a p.val) Finset.univ.toList p
    (fun i _ h => hp (h ▸ i.property))
  cases p with
  | inl w =>
    rw [finiteTuple_off a (Sum.inl w) (fun _ => Sum.inl_ne_inr)]
    simpa only [Finset.mem_toList, Finset.mem_univ, ite_true, finiteRaw] using
      hin ⟨Sum.inl w, arch_mem R D s hs w⟩
  | inr q =>
    by_cases hq : q ∈ R.A.Sf
    · rw [finiteTuple_at a ⟨q, hq⟩]
      simpa only [Finset.mem_toList, Finset.mem_univ, ite_true, finiteRaw] using
        hin ⟨Sum.inr q, finite_mem R D s hs ⟨q, hq⟩⟩
    · rw [finiteTuple_off a (Sum.inr q) (fun p h => hq (Sum.inr.inj h ▸ p.property))]
      apply hout
      intro hp
      exact hq (finite_of_mem R D s hs q hp)

/-- Exact finite product at arbitrary local matrices for an arbitrary
frozen pure tensor, before choosing any normalization. -/
theorem matrix_product (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p.val) :
    stageCoefficient R D s x (finiteBase (R := R) a).val =
      ∏ p : s.val, D.ell p (finiteAction R D a p.val (x p)) := by
  let f := fun x => stageFunction R D s x
  let L := fun p : s.val => finiteAction R D a p.val
  let A := fun p : s.val => scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (localInjection F R.A.zeta12 R.A.primitive_zeta12 p.val (finiteRaw R a p.val))
  have ht (g : Group R) := independent_slot_word f L A
    (finite_intertwining R D a s) Finset.univ.toList.reverse
      (List.nodup_reverse.mpr (Finset.nodup_toList _)) x g
  simp only [List.mem_reverse, Finset.mem_toList, Finset.mem_univ, ite_true,
    List.reverse_reverse] at ht
  have hf : f (fun p => L p (x p)) =
      fun g => f x (g * finiteWord R D a s) := funext ht
  rw [← finiteWord_eq_finiteBase R D a s hs]
  rw [← D.product_exact s (fun p => L p (x p))]
  unfold stageCoefficient MomentSources.fourier
  apply integral_congr_ae
  filter_upwards [] with q
  change f x (_ * finiteWord R D a s) * _ =
    f (fun p => L p (x p)) (_ * 1) * _
  rw [hf, mul_one]

/-- The full scalar at one is exactly the product of the chosen
archimedean and finite local functionals, for this same pure tensor. -/
theorem scalar_product (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p.val) :
    stageCoefficient R D s x 1 =
      (∏ w : InfinitePlace F, D.ell (Sum.inl w) (x ⟨Sum.inl w, arch_mem R D s hs w⟩)) *
      ∏ q : R.A.Sf, D.ell (Sum.inr q.val) (x ⟨Sum.inr q.val, finite_mem R D s hs q⟩) := by
  rw [stageCoefficient_one]
  rw [← Equiv.prod_comp (placeEquiv R D s hs)
    (fun p : s.val => D.ell p (x p)), Fintype.prod_sum_type] <;> rfl

/-- The precise normalization formula needed when the archimedean
components have been replaced.  `stageCoefficient ... 1` is not borrowed
from a different selected vector. -/
theorem normalized_matrix_product
    (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p.val)
    (hx : stageCoefficient R D s x 1 ≠ 0) :
    stageCoefficient R D s x (finiteBase (R := R) a).val =
      stageCoefficient R D s x 1 *
        ∏ q : R.A.Sf,
          D.ell (Sum.inr q.val)
            (finiteAction R D a (Sum.inr q.val)
              (x ⟨Sum.inr q.val, finite_mem R D s hs q⟩)) /
            D.ell (Sum.inr q.val) (x ⟨Sum.inr q.val, finite_mem R D s hs q⟩) := by
  have hlocal (p : s.val) : D.ell p (x p) ≠ 0 := by
    have h := hx
    rw [stageCoefficient_one] at h
    exact (Finset.prod_ne_zero_iff.mp h) p (Finset.mem_univ _)
  rw [matrix_product R D a s hs x]
  have hprod :
      (∏ p : s.val, D.ell p (finiteAction R D a p.val (x p))) =
        (∏ p : s.val, D.ell p (x p)) *
          ∏ p : s.val, D.ell p (finiteAction R D a p.val (x p)) / D.ell p (x p) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    field_simp [hlocal p]
  rw [hprod, ← stageCoefficient_one]
  congr 1
  rw [← Equiv.prod_comp (placeEquiv R D s hs)
    (fun p : s.val => D.ell p (finiteAction R D a p.val (x p)) / D.ell p (x p)),
    Fintype.prod_sum_type]
  have ha :
      (∏ w : InfinitePlace F,
        D.ell (Sum.inl w) (finiteAction R D a (Sum.inl w)
          (x ⟨Sum.inl w, arch_mem R D s hs w⟩)) /
          D.ell (Sum.inl w) (x ⟨Sum.inl w, arch_mem R D s hs w⟩)) = 1 := by
    apply Finset.prod_eq_one
    intro w _
    exact div_self (hlocal ⟨Sum.inl w, arch_mem R D s hs w⟩)
  simpa only [placeEquiv, Equiv.coe_fn_mk, ha, one_mul]

end ThetaGlobal.FiniteCoreProduct

#print axioms ThetaGlobal.FiniteCoreProduct.matrix_product
#print axioms ThetaGlobal.FiniteCoreProduct.scalar_product
#print axioms ThetaGlobal.FiniteCoreProduct.normalized_matrix_product
