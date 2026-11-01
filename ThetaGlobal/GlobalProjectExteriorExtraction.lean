import ThetaGlobal.GlobalProjectExterior
import DedekindZetaZeroFree.Theta.Whittaker.FiniteExteriorProduct

/-!
# Exact exterior factors for arbitrary actual frozen pure tensors

The exterior reference vector is unchanged when archimedean K-types or
finite S-vectors are replaced.  The local Whittaker comparison therefore
extracts the same exterior scalar at every place for the new vector.
The proof retains the original global period of that exact vector at
its S-background and never substitutes a selected Gaussian period.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
noncomputable section

namespace ThetaGlobal.GlobalProjectExteriorExtraction

open NumberField MeasureTheory DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.OrbitExpansion GlobalProjectExterior
open scoped Classical NumberField

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (D : SourceFactorization R Q T)

local notation "V" => actualLocal R D.finiteData

theorem fourier_exterior_single (seed : ∀ p : D.bad, V p) (p : KPFinitePlace F)
    (hp : p ∉ R.A.Sf)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (g : Group R)
    (hg : ∀ t : p.adicCompletion F, Commute g (finitePeriodLift R p
      (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) t))) :
    fourier R Q.dq (badVector R D seed).val (g * finitePeriodLift R p a) =
      D.ell (Sum.inr p)
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
          p (D.finiteData p).inducing (D.finiteData p).inducing.polarization
          (D.finiteData p).haar (D.finiteData p).haar_integer
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) a)
          (D.references (Sum.inr p))) * fourier R Q.dq (badVector R D seed).val g := by
  obtain ⟨s, hq, x, hx, href⟩ := badVector_stage_with_exterior R D seed p hp
  have hn : Sum.inr p ∉ D.bad := by
    rw [D.bad_exact]
    simp only [Sum.inr_ne_inl, false_and, exists_false, Sum.inr.injEq, false_or]
    rintro ⟨q, hq, hmem⟩
    subst q
    exact hp hmem
  let b := KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
    p (D.finiteData p).inducing (D.finiteData p).inducing.polarization
    (D.finiteData p).haar (D.finiteData p).haar_integer
    (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) a)
    (D.references (Sum.inr p))
  have he := finiteSlotPeriod_exterior R D s x p hq (exterior_three_unit R p hp)
    (D.reference_value _ hn) g hg b
  have hu : Function.update x ⟨Sum.inr p, hq⟩ (D.references (Sum.inr p)) = x := by
    rw [← href, Function.update_eq_self]
  have ht := tensor_finite_translate R D s x p hq a g
  rw [href, hx] at ht
  rw [← ht]
  change finiteSlotPeriod R D s x p hq g b = _
  rw [he]
  simp only [finiteSlotPeriod, LinearMap.comp_apply, tensorPeriod, LinearMap.coe_mk,
    AddHom.coe_mk, MultilinearMap.toLinearMap_apply, hu, hx]
  rfl


theorem fourier_exterior_finite (seed : ∀ p : D.bad, V p)
    (P : Finset (ThetaBranch.ExteriorPrime R.A))
    (a : ∀ p : ThetaBranch.ExteriorPrime R.A,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
    (g : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (hg : ∀ p : ThetaBranch.ExteriorPrime R.A, g (Sum.inr p.val) = 1) :
    fourier R Q.dq (badVector R D seed).val (restrictedLift R g * restrictedLift R (exteriorFiniteTuple R P a)) =
      (∏ p ∈ P, exteriorSlotValue R D p.val (a p)) * fourier R Q.dq (badVector R D seed).val (restrictedLift R g) := by
  induction P using Finset.induction_on with
  | empty =>
    have he : exteriorFiniteTuple R ∅ a = 1 := by
      apply RestrictedProduct.ext
      intro w
      cases w <;> simp [exteriorFiniteTuple]
    rw [he, map_one, mul_one, Finset.prod_empty, one_mul]
  | @insert p P hp ih =>
    have hc : Commute (KPAdelicCoverRestrictedProduct.localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (a p))
        (exteriorFiniteTuple R P a) := by
      apply Commute.symm
      change exteriorFiniteTuple R P a * _ = _ * exteriorFiniteTuple R P a
      apply RestrictedProduct.ext
      intro w
      change exteriorFiniteTuple R P a w * Pi.mulSingle (Sum.inr p.val) (a p) w =
        Pi.mulSingle (Sum.inr p.val) (a p) w * exteriorFiniteTuple R P a w
      by_cases hw : w = Sum.inr p.val
      · subst w
        rw [exteriorFiniteTuple_off R P a _ (by
          intro q hq he
          apply hp
          have he' : p = q := Subtype.ext (Sum.inr_injective he)
          exact he' ▸ hq)]
        simp
      · change _ = Pi.mulSingle (Sum.inr p.val) (a p) w * exteriorFiniteTuple R P a w
        simp [Pi.mulSingle_eq_of_ne hw]
    have ho : exteriorFiniteTuple R P a (Sum.inr p.val) = 1 :=
      exteriorFiniteTuple_off R P a _ (by
        intro q hq he
        exact hp ((Subtype.ext (Sum.inr_injective he) : p = q) ▸ hq))
    have hroot (t : p.val.adicCompletion F) : Commute
        (restrictedLift R g * restrictedLift R (exteriorFiniteTuple R P a))
        (finitePeriodLift R p.val (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) t)) := by
      rw [← map_mul]
      apply restrictedLift_commute_single
      rw [RestrictedProduct.mul_apply, hg, ho, one_mul]
    have htuple : exteriorFiniteTuple R (insert p P) a = exteriorFiniteTuple R P a *
        KPAdelicCoverRestrictedProduct.localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (a p) := by
      apply RestrictedProduct.ext
      intro w
      change exteriorFiniteTuple R (insert p P) a w = exteriorFiniteTuple R P a w * Pi.mulSingle (Sum.inr p.val) (a p) w
      cases w with
      | inl w => simp [exteriorFiniteTuple]
      | inr q =>
        by_cases hq : q = p.val
        · subst q
          rw [ho]
          simp only [Pi.mulSingle_eq_same, one_mul]
          change (if h : p.val ∉ R.A.Sf then if (⟨p.val, h⟩ : ThetaBranch.ExteriorPrime R.A) ∈ insert p P then a ⟨p.val, h⟩ else 1 else 1) = a p
          simp [p.property]
        · have hqp : (Sum.inr q : KPHilbert.Place F) ≠ Sum.inr p.val := Sum.inr_injective.ne hq
          rw [Pi.mulSingle_eq_of_ne hqp, mul_one]
          change (if h : q ∉ R.A.Sf then if (⟨q, h⟩ : ThetaBranch.ExteriorPrime R.A) ∈ insert p P then a ⟨q, h⟩ else 1 else 1) =
            ((if h : q ∉ R.A.Sf then if (⟨q, h⟩ : ThetaBranch.ExteriorPrime R.A) ∈ P then a ⟨q, h⟩ else 1 else 1) : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
          by_cases h : q ∉ R.A.Sf
          · rw [dif_pos h, dif_pos h]
            have hn : (⟨q, h⟩ : ThetaBranch.ExteriorPrime R.A) ≠ p := fun he => hq (congrArg Subtype.val he)
            simp only [Finset.mem_insert, hn, false_or]
          · rw [dif_neg h, dif_neg h]
    rw [htuple, map_mul, ← mul_assoc]
    change fourier R Q.dq (badVector R D seed).val ((_ * _) * finitePeriodLift R p.val (a p)) = _
    rw [fourier_exterior_single R D seed p.val p.property (a p) _ hroot, ih, Finset.prod_insert hp]
    rw [mul_assoc]


theorem fourier_exterior_tuple (seed : ∀ p : D.bad, V p)
    (a g : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (hg : ∀ p : ThetaBranch.ExteriorPrime R.A, g (Sum.inr p.val) = 1)
    (ha : ∀ w, (¬ ∃ p : ThetaBranch.ExteriorPrime R.A, w = Sum.inr p.val) → a w = 1)
    (P : Finset (ThetaBranch.ExteriorPrime R.A))
    (hP : ∀ p : ThetaBranch.ExteriorPrime R.A, p ∉ P → a (Sum.inr p.val) ∈ DigitMasks.exteriorFactor R (Sum.inr p.val)) :
    Function.HasFiniteMulSupport (fun p : ThetaBranch.ExteriorPrime R.A => exteriorSlotValue R D p.val (a (Sum.inr p.val))) ∧
    fourier R Q.dq (badVector R D seed).val (restrictedLift R g * restrictedLift R a) =
      (∏ᶠ p : ThetaBranch.ExteriorPrime R.A, exteriorSlotValue R D p.val (a (Sum.inr p.val))) *
        fourier R Q.dq (badVector R D seed).val (restrictedLift R g) := by
  let b := exteriorFiniteTuple R P (fun p => a (Sum.inr p.val))
  let k := b⁻¹ * a
  have hk (w : KPHilbert.Place F) : k w ∈ DigitMasks.exteriorFactor R w := by
    change (b⁻¹ * a) w ∈ _
    rw [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply]
    by_cases hw : ∃ p : ThetaBranch.ExteriorPrime R.A, w = Sum.inr p.val
    · obtain ⟨p, rfl⟩ := hw
      change (exteriorFiniteTuple R P (fun p => a (Sum.inr p.val)) (Sum.inr p.val))⁻¹ * a (Sum.inr p.val) ∈ _
      rw [exteriorFiniteTuple_at]
      by_cases hp : p ∈ P
      · rw [if_pos hp, inv_mul_cancel]
        exact (DigitMasks.exteriorFactor R _).one_mem
      · rw [if_neg hp, inv_one, one_mul]
        exact hP p hp
    · rw [ha w hw]
      have hb : b w = 1 := exteriorFiniteTuple_off R P _ w (fun p _ he => hw ⟨p, he⟩)
      rw [hb, inv_one, one_mul]
      exact (DigitMasks.exteriorFactor R _).one_mem
  have hsupport : Function.mulSupport (fun p : ThetaBranch.ExteriorPrime R.A => exteriorSlotValue R D p.val (a (Sum.inr p.val))) ⊆ P := by
    intro p hp
    by_contra hn
    exact hp (exteriorSlotValue_compact R D p _ (hP p hn))
  have hs : Function.HasFiniteMulSupport (fun p : ThetaBranch.ExteriorPrime R.A => exteriorSlotValue R D p.val (a (Sum.inr p.val))) :=
    P.finite_toSet.subset hsupport
  refine ⟨hs, ?_⟩
  have he : b * k = a := mul_inv_cancel_left b a
  have hi (q : KPAdditiveQuotient F) := badVector_fullExteriorInvariant R D seed k hk
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * (restrictedLift R g * restrictedLift R b))
  have hfourier : fourier R Q.dq (badVector R D seed).val (restrictedLift R g * restrictedLift R a) =
      fourier R Q.dq (badVector R D seed).val (restrictedLift R g * restrictedLift R b) := by
    unfold MomentSources.fourier
    apply integral_congr_ae
    filter_upwards [] with q
    have h := hi q
    change (badVector R D seed).val ((_ * (restrictedLift R g * restrictedLift R b)) * restrictedLift R k) = _ at h
    rw [mul_assoc, mul_assoc, ← map_mul, he] at h
    rw [h]
  rw [hfourier, fourier_exterior_finite R D seed P _ g hg]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupport]


end ThetaGlobal.GlobalProjectExteriorExtraction
