import CubicSieve.ExteriorKernel
import HeckeGeneral.Arithmetic.SIntegerModulusNorm
import HeckeGeneral.Arithmetic.SIntegerIdealSaturation

/-! Every sixth-power S-unit orbit is retained in an ideal and a finite
unit-class sector. The chosen actual generators trivialize each fiber.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.OrbitRows

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)
local notation "OS" => S.integer K
abbrev Γ := (powMonoidHom 6 : S.unit K →* S.unit K).range
abbrev Orbits := SIntegerOrbits K S (Γ K S)

def elementIdeal (a : NonzeroRingElements OS) : ExteriorIdeal K S :=
  ⟨⟨sIntegerModulusContraction K S a.val,
    mem_nonZeroDivisors_of_ne_zero (sIntegerModulusContraction_ne_bot K S a.val a.property)⟩,
    by
      intro p hp hpS
      have hh := sIntegerModulusContraction_coprime K S a.val a.property p hpS
      have hle := Ideal.dvd_iff_le.mp hp
      rw [sup_eq_right.mpr hle] at hh
      exact p.isPrime.ne_top hh⟩

theorem elementIdeal_span (a : NonzeroRingElements OS) :
    (elementIdeal K S a).val.val.map (algebraMap (𝓞 K) OS) = Ideal.span {a.val} :=
  map_sIntegerModulusContraction K S a.val

theorem elementIdeal_generator (I : ExteriorIdeal K S) :
    elementIdeal K S ⟨D.generator I, D.generator_ne_zero I⟩ = I := by
  apply Subtype.ext
  apply Subtype.ext
  change (Ideal.span ({D.generator I} : Set OS)).under (𝓞 K) = I.val.val
  rw [D.generator_span I]
  exact under_map_coprime_sIntegerIdeal K S I.val.val
    (sexticIdeal_coprime_S K S I.val.val I.property)

theorem elementIdeal_unit_mul (u : S.unit K) (a : NonzeroRingElements OS) :
    elementIdeal K S ((S.unitEquivUnitsInteger K u) • a) = elementIdeal K S a := by
  apply Subtype.ext
  apply Subtype.ext
  change (Ideal.span ({(S.unitEquivUnitsInteger K u).val * a.val} : Set OS)).under (𝓞 K) = _
  rw [Ideal.span_singleton_mul_left_unit (S.unitEquivUnitsInteger K u).isUnit]
  rfl

def orbitIdeal (q : Orbits K S) : ExteriorIdeal K S :=
  Quotient.liftOn q (elementIdeal K S) (by
    intro a b hab
    obtain ⟨u, hu⟩ := (sIntegerOrbitRelation_iff K S (Γ K S) a b).mp hab
    have he : (S.unitEquivUnitsInteger K u.val) • b = a := by
      apply Subtype.ext
      exact Subtype.ext hu
    rw [← he, elementIdeal_unit_mul])

@[simp] theorem orbitIdeal_mk (a : NonzeroRingElements OS) :
    orbitIdeal K S (Quotient.mk _ a) = elementIdeal K S a := rfl

def scalarOrbit (I : ExteriorIdeal K S) (u : S.unit K) : Orbits K S :=
  Quotient.mk _ ((S.unitEquivUnitsInteger K u) •
    (⟨D.generator I, D.generator_ne_zero I⟩ : NonzeroRingElements OS))

@[simp] theorem orbitIdeal_scalarOrbit (I : ExteriorIdeal K S) (u : S.unit K) :
    orbitIdeal K S (scalarOrbit K S D I u) = I := by
  rw [scalarOrbit, orbitIdeal_mk, elementIdeal_unit_mul, elementIdeal_generator]

theorem scalarOrbit_eq_iff (I : ExteriorIdeal K S) (u v : S.unit K) :
    scalarOrbit K S D I u = scalarOrbit K S D I v ↔
      (QuotientGroup.mk u : SixthUnitClasses K S) = QuotientGroup.mk v := by
  constructor
  · intro h
    obtain ⟨γ, hγ⟩ := (sIntegerOrbitRelation_iff K S (Γ K S) _ _).mp (Quotient.exact h)
    have hc : (D.generator I : K) ≠ 0 := by
      intro hz
      exact D.generator_ne_zero I (Subtype.ext hz)
    change (((γ.val : Kˣ) : K) *
      (((v : Kˣ) : K) * (D.generator I : K))) =
        ((u : Kˣ) : K) * (D.generator I : K) at hγ
    have huv : u = γ.val * v := by
      apply Subtype.ext
      apply Units.ext
      apply mul_right_cancel₀ hc
      change ((u : Kˣ) : K) * (D.generator I : K) =
        (((γ.val * v : S.unit K) : Kˣ) : K) * (D.generator I : K)
      simpa only [Subgroup.coe_mul, Units.val_mul, mul_assoc] using hγ.symm
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [huv, mul_div_cancel_right]
    exact γ.property
  · intro h
    have hmem := QuotientGroup.eq_iff_div_mem.mp h
    let γ : Γ K S := ⟨u / v, hmem⟩
    apply Quotient.sound
    apply (sIntegerOrbitRelation_iff K S (Γ K S) _ _).mpr
    refine ⟨γ, ?_⟩
    change (((u / v : S.unit K) : Kˣ) : K) *
      (((v : Kˣ) : K) * (D.generator I : K)) =
        ((u : Kˣ) : K) * (D.generator I : K)
    rw [← mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, div_mul_cancel]

def classOrbit (p : ExteriorIdeal K S × SixthUnitClasses K S) : Orbits K S :=
  scalarOrbit K S D p.1 p.2.out

theorem classOrbit_injective : Function.Injective (classOrbit K S D) := by
  rintro ⟨I, u⟩ ⟨J, v⟩ h
  have hij := congrArg (orbitIdeal K S) h
  change orbitIdeal K S (scalarOrbit K S D I u.out) =
    orbitIdeal K S (scalarOrbit K S D J v.out) at hij
  rw [orbitIdeal_scalarOrbit, orbitIdeal_scalarOrbit] at hij
  subst J
  have huv := (scalarOrbit_eq_iff K S D I u.out v.out).mp h
  have heq : u = v := by simpa only [Quotient.out_eq] using huv
  exact Prod.ext rfl heq

theorem classOrbit_surjective : Function.Surjective (classOrbit K S D) := by
  intro q
  refine Quotient.inductionOn q (fun a => ?_)
  let I := elementIdeal K S a
  have hspan : Ideal.span ({D.generator I} : Set OS) = Ideal.span {a.val} :=
    (D.generator_span I).trans (elementIdeal_span K S a)
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  let v : S.unit K := (S.unitEquivUnitsInteger K).symm u
  have hv : scalarOrbit K S D I v = Quotient.mk _ a := by
    have he : (S.unitEquivUnitsInteger K v) •
        (⟨D.generator I, D.generator_ne_zero I⟩ : NonzeroRingElements OS) = a := by
      apply Subtype.ext
      change (S.unitEquivUnitsInteger K v).val * D.generator I = a.val
      simpa only [v, MulEquiv.apply_symm_apply, mul_comm] using hu
    exact congrArg (fun b : NonzeroRingElements OS =>
      (Quotient.mk _ b : Orbits K S)) he
  refine ⟨(I, QuotientGroup.mk v), ?_⟩
  apply Eq.trans _ hv
  apply (scalarOrbit_eq_iff K S D I _ v).mpr
  exact Quotient.out_eq _

def orbitEquiv : ExteriorIdeal K S × SixthUnitClasses K S ≃ Orbits K S :=
  Equiv.ofBijective (classOrbit K S D)
    ⟨classOrbit_injective K S D, classOrbit_surjective K S D⟩

theorem scalarOrbit_norm (I : ExteriorIdeal K S) (u : S.unit K) :
    (sIntegerOrbitNorm K S (Γ K S) (scalarOrbit K S D I u)).val = exteriorNorm K S I := by
  rw [scalarOrbit, sIntegerOrbitNorm_mk]
  change (sIntegerElementNorm K S ((S.unitEquivUnitsInteger K u) •
    (⟨D.generator I, D.generator_ne_zero I⟩ : NonzeroRingElements OS))).val = _
  have hn := sIntegerElementNorm_eq_of_orbitRel K S (⊤ : Subgroup (S.unit K))
    ((S.unitEquivUnitsInteger K u) •
      (⟨D.generator I, D.generator_ne_zero I⟩ : NonzeroRingElements OS))
    ⟨D.generator I, D.generator_ne_zero I⟩
    ((sIntegerOrbitRelation_iff K S ⊤ _ _).mpr ⟨⟨u, Subgroup.mem_top u⟩, rfl⟩)
  rw [hn]
  rw [← natCard_sIntegerPrincipalResidue_eq_productNorm K S (D.generator I)
    (D.generator_ne_zero I), natCard_sIntegerPrincipalResidue K S (D.generator I)
      (D.generator_ne_zero I)]
  have heq := congrArg (fun J : ExteriorIdeal K S => J.val.val)
    (elementIdeal_generator K S D I)
  change sIntegerModulusContraction K S (D.generator I) = I.val.val at heq
  change ((sIntegerModulusContraction K S (D.generator I)).absNorm : ℝ) = _
  rw [heq]
  rfl

end CubicSieve.OrbitRows
