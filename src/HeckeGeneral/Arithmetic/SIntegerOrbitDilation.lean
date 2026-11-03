import HeckeGeneral.Arithmetic.SIntegerOrbitEnumeration
import HeckeGeneral.Arithmetic.SIntegerOrbitNorm
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-! Multiplication by any actual nonzero S-integer on the original subgroup
orbits. Divisibility is independent of representatives, including every sector. -/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup (S.unit K))
local notation "N" => NonzeroRingElements (S.integer K)
local notation "Q" => SIntegerOrbits K S Γ

def sIntegerNonzeroMul (d a : N) : N :=
  ⟨d.val * a.val, mul_ne_zero d.property a.property⟩

private theorem orbitRel_nonzeroMul (d a b : N)
    (hab : MulAction.orbitRel (sIntegerUnitSubgroup K S Γ) N a b) :
    MulAction.orbitRel (sIntegerUnitSubgroup K S Γ) N
      (sIntegerNonzeroMul K S d a) (sIntegerNonzeroMul K S d b) := by
  obtain ⟨u, hu⟩ := (sIntegerOrbitRelation_iff K S Γ a b).mp hab
  apply (sIntegerOrbitRelation_iff K S Γ _ _).mpr
  refine ⟨u, ?_⟩
  change ((u.val : Kˣ) : K) * ((d.val : K) * (b.val : K)) =
    (d.val : K) * (a.val : K)
  calc
    _ = (d.val : K) * (((u.val : Kˣ) : K) * (b.val : K)) := by ring
    _ = _ := congrArg ((d.val : K) * ·) hu

def sIntegerOrbitDilation (d : N) (q : Q) : Q :=
  Quotient.liftOn q (fun a => Quotient.mk _ (sIntegerNonzeroMul K S d a))
    (fun a b hab => Quotient.sound (orbitRel_nonzeroMul K S Γ d a b hab))

@[simp] theorem sIntegerOrbitDilation_mk (d a : N) :
    sIntegerOrbitDilation K S Γ d (Quotient.mk _ a) =
      Quotient.mk _ (sIntegerNonzeroMul K S d a) := rfl

theorem sIntegerOrbitDilation_injective (d : N) :
    Function.Injective (sIntegerOrbitDilation K S Γ d) := by
  intro q q'
  refine Quotient.inductionOn₂ q q' ?_
  intro a b hab
  obtain ⟨u, hu⟩ := (sIntegerOrbitRelation_iff K S Γ _ _).mp (Quotient.exact hab)
  apply Quotient.sound
  apply (sIntegerOrbitRelation_iff K S Γ a b).mpr
  refine ⟨u, ?_⟩
  apply mul_left_cancel₀ (nonzeroSIntegerFieldUnit K S d).ne_zero
  change (d.val : K) * (((u.val : Kˣ) : K) * (b.val : K)) =
    (d.val : K) * (a.val : K)
  change ((u.val : Kˣ) : K) * ((d.val : K) * (b.val : K)) =
    (d.val : K) * (a.val : K) at hu
  calc
    _ = ((u.val : Kˣ) : K) * ((d.val : K) * (b.val : K)) := by ring
    _ = _ := hu

/-- Ordinary ring divisibility is unchanged by the actual Γ-unit relation. -/
theorem sIntegerOrbitDivisible_rep_iff (d a b : N)
    (hab : MulAction.orbitRel (sIntegerUnitSubgroup K S Γ) N a b) :
    d.val ∣ a.val ↔ d.val ∣ b.val := by
  obtain ⟨u, hu⟩ := (sIntegerOrbitRelation_iff K S Γ a b).mp hab
  let U := S.unitEquivUnitsInteger K u.val
  have hU : (U : S.integer K) * b.val = a.val := Subtype.ext hu
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(U⁻¹ : (S.integer K)ˣ) * z, ?_⟩
    calc
      b.val = (U⁻¹ : (S.integer K)ˣ) * a.val := by rw [← hU]; simp [mul_assoc]
      _ = (U⁻¹ : (S.integer K)ˣ) * (d.val * z) := by rw [← hz]
      _ = _ := by ring
  · rintro ⟨z, hz⟩
    refine ⟨(U : S.integer K) * z, ?_⟩
    rw [← hU, hz]
    ring

def sIntegerOrbitDivisible (d : N) (q : Q) : Prop :=
  Quotient.liftOn q (fun a => d.val ∣ a.val)
    (fun a b hab => propext (sIntegerOrbitDivisible_rep_iff K S Γ d a b hab))

@[simp] theorem sIntegerOrbitDivisible_mk (d a : N) :
    sIntegerOrbitDivisible K S Γ d (Quotient.mk _ a) ↔ d.val ∣ a.val := Iff.rfl

theorem sIntegerOrbitDivisible_iff_exists (d : N) (q : Q) :
    sIntegerOrbitDivisible K S Γ d q ↔ ∃ p : Q, sIntegerOrbitDilation K S Γ d p = q := by
  refine Quotient.inductionOn q ?_
  intro a
  constructor
  · rintro ⟨z, hz⟩
    have hz0 : z ≠ 0 := by intro h; apply a.property; simpa [h] using hz
    refine ⟨Quotient.mk _ (⟨z, hz0⟩ : N), ?_⟩
    apply congrArg (Quotient.mk _)
    exact Subtype.ext hz.symm
  · rintro ⟨p, hp⟩
    revert hp
    refine Quotient.inductionOn p ?_
    intro b hb
    have hrel := Quotient.exact hb
    exact (sIntegerOrbitDivisible_rep_iff K S Γ d
      (sIntegerNonzeroMul K S d b) a hrel).mp ⟨b.val, rfl⟩

/-- All and only the divisible sectors occur, without making d a unit. -/
def sIntegerOrbitDilationEquiv (d : N) :
    Q ≃ {q : Q // sIntegerOrbitDivisible K S Γ d q} :=
  Equiv.ofBijective
    (fun q => ⟨sIntegerOrbitDilation K S Γ d q,
      (sIntegerOrbitDivisible_iff_exists K S Γ d _).mpr ⟨q, rfl⟩⟩)
    ⟨fun _ _ h => sIntegerOrbitDilation_injective K S Γ d (congrArg Subtype.val h),
      fun q => by
        obtain ⟨p, hp⟩ := (sIntegerOrbitDivisible_iff_exists K S Γ d q.val).mp q.property
        exact ⟨p, Subtype.ext hp⟩⟩

theorem tsum_sIntegerOrbitDilation (d : N) (F : Q → ℂ)
    (hF : ∀ q, ¬ sIntegerOrbitDivisible K S Γ d q → F q = 0) :
    (∑' q : Q, F q) = ∑' q : Q, F (sIntegerOrbitDilation K S Γ d q) := by
  calc
    _ = ∑' q : {q : Q // sIntegerOrbitDivisible K S Γ d q}, F q.val := by
      exact (tsum_subtype_eq_of_support_subset
        (f := F) (s := {q : Q | sIntegerOrbitDivisible K S Γ d q}) (by
          intro q hq
          by_contra hnot
          exact hq (hF q hnot))).symm
    _ = _ := ((sIntegerOrbitDilationEquiv K S Γ d).tsum_eq (fun q => F q.val)).symm

theorem sLocalNonzeroIntegerDiagonal_nonzeroMul (d a : N) :
    sLocalNonzeroIntegerDiagonal K S (sIntegerNonzeroMul K S d a) =
      sLocalNonzeroIntegerDiagonal K S d * sLocalNonzeroIntegerDiagonal K S a := by
  have h : nonzeroSIntegerFieldUnit K S (sIntegerNonzeroMul K S d a) =
      nonzeroSIntegerFieldUnit K S d * nonzeroSIntegerFieldUnit K S a := Units.ext rfl
  unfold sLocalNonzeroIntegerDiagonal
  rw [h, map_mul]

variable [Fintype S]

theorem sIntegerElementNorm_nonzeroMul (d a : N) :
    (sIntegerElementNorm K S (sIntegerNonzeroMul K S d a)).val =
      (sIntegerElementNorm K S d).val * (sIntegerElementNorm K S a).val := by
  change sLocalProductNorm K S _ = _
  rw [sLocalNonzeroIntegerDiagonal_nonzeroMul, sLocalProductNorm_mul]
  rfl

theorem sIntegerOrbitNorm_dilation (d : N) (q : Q) :
    (sIntegerOrbitNorm K S Γ (sIntegerOrbitDilation K S Γ d q)).val =
      (sIntegerElementNorm K S d).val * (sIntegerOrbitNorm K S Γ q).val := by
  refine Quotient.inductionOn q ?_
  intro a
  exact sIntegerElementNorm_nonzeroMul K S d a

end HeckeGeneral.Arithmetic
