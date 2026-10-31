import HeckeGeneral.Analysis.LocalThetaInput
import HeckeGeneral.Arithmetic.SIntegerModulusNorm
import HeckeGeneral.Arithmetic.SIntegerOrbitDilation

/-!
# Actual selected generators and all original unit sectors

Every original subgroup orbit is represented by the selected generator
of its full exterior ideal and one unit class. The construction uses
only the arithmetic generator data. It requires no moment estimate,
preferred sector, or row-identification assumption. In particular,
positive row ranges can be enlarged in ideal/sector coordinates without
discarding sixth-power descendants or original sectors.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalSectors

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K))
variable (D : ThetaArithmeticData K S)

abbrev UnitClasses := (S.unit K) ⧸ Γ

def sectorUnit (ξ : UnitClasses K S Γ) : S.unit K := Quotient.out ξ

theorem contraction_of_orbitRel
    (a b : NonzeroRingElements (Set.integer S K))
    (hab : MulAction.orbitRel (sIntegerUnitSubgroup K S Γ)
      (NonzeroRingElements (Set.integer S K)) a b) :
    sIntegerModulusContraction K S a.val = sIntegerModulusContraction K S b.val := by
  obtain ⟨γ, hγ⟩ := (sIntegerOrbitRelation_iff K S Γ a b).mp hab
  have heq : (S.unitEquivUnitsInteger K γ.val).val * b.val = a.val := Subtype.ext hγ
  unfold sIntegerModulusContraction
  rw [← heq, Ideal.span_singleton_mul_left_unit (S.unitEquivUnitsInteger K γ.val).isUnit]

def orbitContraction (q : SIntegerOrbits K S Γ) : Ideal (𝓞 K) :=
  Quotient.liftOn q (fun a => sIntegerModulusContraction K S a.val)
    (contraction_of_orbitRel K S Γ)

@[simp] theorem orbitContraction_mk (a : NonzeroRingElements (Set.integer S K)) :
    orbitContraction K S Γ (Quotient.mk _ a) = sIntegerModulusContraction K S a.val := rfl

def orbitExterior (q : SIntegerOrbits K S Γ) : ExteriorIdeal K S :=
  ⟨⟨orbitContraction K S Γ q, mem_nonZeroDivisors_of_ne_zero (by
      refine Quotient.inductionOn q ?_
      intro a
      exact sIntegerModulusContraction_ne_bot K S a.val a.property)⟩, by
    refine Quotient.inductionOn q ?_
    intro a p hp hpin
    have hc := sIntegerModulusContraction_coprime K S a.val a.property p hpin
    have hl := Ideal.dvd_iff_le.mp hp
    exact p.isPrime.ne_top ((sup_of_le_right hl).symm.trans hc)⟩

def rowElement (x : ExteriorIdeal K S × UnitClasses K S Γ) :
    NonzeroRingElements (Set.integer S K) :=
  ⟨(S.unitEquivUnitsInteger K (sectorUnit K S Γ x.2)).val * D.generator x.1,
    mul_ne_zero (Units.ne_zero _) (D.generator_ne_zero x.1)⟩

theorem rowElement_contraction (x : ExteriorIdeal K S × UnitClasses K S Γ) :
    sIntegerModulusContraction K S (rowElement K S Γ D x).val = x.1.val.val := by
  unfold rowElement sIntegerModulusContraction
  rw [Ideal.span_singleton_mul_left_unit
    (S.unitEquivUnitsInteger K (sectorUnit K S Γ x.2)).isUnit, D.generator_span]
  exact under_map_coprime_sIntegerIdeal K S x.1.val.val
    (sexticIdeal_coprime_S K S x.1.val.val x.1.property)

def rowOrbit (x : ExteriorIdeal K S × UnitClasses K S Γ) : SIntegerOrbits K S Γ :=
  Quotient.mk _ (rowElement K S Γ D x)

theorem rowOrbit_contraction (x : ExteriorIdeal K S × UnitClasses K S Γ) :
    orbitContraction K S Γ (rowOrbit K S Γ D x) = x.1.val.val :=
  rowElement_contraction K S Γ D x

theorem rowOrbit_norm (x : ExteriorIdeal K S × UnitClasses K S Γ) :
    (sIntegerOrbitNorm K S Γ (rowOrbit K S Γ D x)).val = (x.1.val.val.absNorm : ℝ) := by
  change (sIntegerElementNorm K S (rowElement K S Γ D x)).val = _
  rw [← natCard_sIntegerPrincipalResidue_eq_productNorm K S
      (rowElement K S Γ D x).val (rowElement K S Γ D x).property,
    natCard_sIntegerPrincipalResidue K S
      (rowElement K S Γ D x).val (rowElement K S Γ D x).property,
    rowElement_contraction]

theorem rowOrbit_injective : Function.Injective (rowOrbit K S Γ D) := by
  intro x y hxy
  have hI : x.1 = y.1 := by
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg (orbitContraction K S Γ) hxy
    simpa only [rowOrbit_contraction] using h
  obtain ⟨γ, hγ⟩ := (sIntegerOrbitRelation_iff K S Γ
    (rowElement K S Γ D x) (rowElement K S Γ D y)).mp (Quotient.exact hxy)
  have hg : (D.generator y.1 : K) ≠ 0 := by
    intro h
    exact D.generator_ne_zero y.1 (Subtype.ext h)
  have he : γ.val * sectorUnit K S Γ y.2 = sectorUnit K S Γ x.2 := by
    apply Subtype.ext
    apply Units.ext
    apply mul_right_cancel₀ hg
    change (((γ.val : Kˣ) : K) * (((sectorUnit K S Γ y.2 : S.unit K) : Kˣ) : K)) *
        (D.generator y.1 : K) =
      (((sectorUnit K S Γ x.2 : S.unit K) : Kˣ) : K) * (D.generator y.1 : K)
    change ((γ.val : Kˣ) : K) *
        ((((sectorUnit K S Γ y.2 : S.unit K) : Kˣ) : K) * (D.generator y.1 : K)) =
      (((sectorUnit K S Γ x.2 : S.unit K) : Kˣ) : K) * (D.generator x.1 : K) at hγ
    rw [hI] at hγ
    exact (mul_assoc _ _ _).trans hγ
  have hq : QuotientGroup.mk' Γ (sectorUnit K S Γ y.2) =
      QuotientGroup.mk' Γ (sectorUnit K S Γ x.2) := by
    apply (QuotientGroup.mk'_eq_mk' Γ).mpr
    exact ⟨γ.val, γ.property, (mul_comm _ _).trans he⟩
  have hx : QuotientGroup.mk' Γ (sectorUnit K S Γ x.2) = x.2 := Quotient.out_eq x.2
  have hy : QuotientGroup.mk' Γ (sectorUnit K S Γ y.2) = y.2 := Quotient.out_eq y.2
  exact Prod.ext hI (hx.symm.trans (hq.symm.trans hy))

theorem rowOrbit_surjective : Function.Surjective (rowOrbit K S Γ D) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro a
  let I := orbitExterior K S Γ (Quotient.mk _ a)
  have hspan : Ideal.span ({D.generator I} : Set (Set.integer S K)) =
      Ideal.span ({a.val} : Set (Set.integer S K)) := by
    rw [D.generator_span]
    change Ideal.map (algebraMap (𝓞 K) (Set.integer S K))
      (sIntegerModulusContraction K S a.val) = _
    exact map_sIntegerModulusContraction K S a.val
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  let u : S.unit K := (S.unitEquivUnitsInteger K).symm v
  let ξ : UnitClasses K S Γ := QuotientGroup.mk' Γ u
  have hξ : QuotientGroup.mk' Γ (sectorUnit K S Γ ξ) = QuotientGroup.mk' Γ u :=
    Quotient.out_eq ξ
  obtain ⟨γ, hγ, hγu⟩ := (QuotientGroup.mk'_eq_mk' Γ).mp hξ
  refine ⟨(I, ξ), ?_⟩
  symm
  apply Quotient.sound
  apply (sIntegerOrbitRelation_iff K S Γ _ _).mpr
  refine ⟨⟨γ, hγ⟩, ?_⟩
  have huv : S.unitEquivUnitsInteger K u = v := (S.unitEquivUnitsInteger K).apply_symm_apply v
  have hfield : (D.generator I : K) * ((u : Kˣ) : K) = (a.val : K) := by
    have h := congrArg (fun c : Set.integer S K => (c : K)) hv
    rw [← huv] at h
    exact h
  have hγfield : (((sectorUnit K S Γ ξ : S.unit K) : Kˣ) : K) * ((γ : Kˣ) : K) =
      ((u : Kˣ) : K) := congrArg (fun c : S.unit K => ((c : Kˣ) : K)) hγu
  change ((γ : Kˣ) : K) *
    ((((sectorUnit K S Γ ξ : S.unit K) : Kˣ) : K) * (D.generator I : K)) = (a.val : K)
  calc
    _ = (D.generator I : K) *
      ((((sectorUnit K S Γ ξ : S.unit K) : Kˣ) : K) * ((γ : Kˣ) : K)) := by ring
    _ = _ := by rw [hγfield, hfield]

/-- Complete orbit reindexing with the actual canonical generators. -/
def idealSectorsEquiv : (ExteriorIdeal K S × UnitClasses K S Γ) ≃ SIntegerOrbits K S Γ :=
  Equiv.ofBijective (rowOrbit K S Γ D)
    ⟨rowOrbit_injective K S Γ D, rowOrbit_surjective K S Γ D⟩

theorem tsum_eq_ideal_sectors (f : SIntegerOrbits K S Γ → ℂ) :
    (∑' q, f q) = ∑' x : ExteriorIdeal K S × UnitClasses K S Γ,
      f (rowOrbit K S Γ D x) := (idealSectorsEquiv K S Γ D).tsum_eq f |>.symm

/-- This is the original subgroup index, not a selected subset of sectors. -/
theorem card_sectors : Nat.card (UnitClasses K S Γ) = Γ.index := rfl

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalSectors

end
