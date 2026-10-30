import HeckeGeneral.Arithmetic.SIntegerLocalDiagonal

/-!
# The actual positive S-local norm of an S-integer orbit

The norm is taken on the genuine diagonal element. The S-unit product
formula proves independence of the representative. All subgroup sectors
remain in the quotient; no ideal-norm identification is assumed here.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K))

theorem sLocalNonzeroIntegerDiagonal_eq_of_unit_mul
    (a b : NonzeroRingElements (S.integer K)) (u : S.unit K)
    (hab : ((u : Kˣ) : K) * (b.val : K) = (a.val : K)) :
    sLocalNonzeroIntegerDiagonal K S a =
      sLocalDiagonal K S u * sLocalNonzeroIntegerDiagonal K S b := by
  have heq : nonzeroSIntegerFieldUnit K S a =
      (u : Kˣ) * nonzeroSIntegerFieldUnit K S b := Units.ext hab.symm
  unfold sLocalNonzeroIntegerDiagonal
  rw [heq, map_mul, sLocalFieldUnitDiagonal_sUnit]

/-- The positive norm of every actual nonzero S-integer. -/
def sIntegerElementNorm (a : NonzeroRingElements (S.integer K)) : {r : ℝ // 0 < r} :=
  ⟨sLocalProductNorm K S (sLocalNonzeroIntegerDiagonal K S a),
    sLocalProductNorm_pos K S _⟩

theorem sIntegerElementNorm_eq_of_orbitRel
    (a b : NonzeroRingElements (S.integer K))
    (hab : MulAction.orbitRel (sIntegerUnitSubgroup K S Γ)
      (NonzeroRingElements (S.integer K)) a b) :
    sIntegerElementNorm K S a = sIntegerElementNorm K S b := by
  obtain ⟨u, hu⟩ := (sIntegerOrbitRelation_iff K S Γ a b).mp hab
  apply Subtype.ext
  change sLocalProductNorm K S (sLocalNonzeroIntegerDiagonal K S a) = _
  rw [sLocalNonzeroIntegerDiagonal_eq_of_unit_mul K S a b (u : S.unit K) hu]
  exact sLocalProductNorm_diagonal_mul K S (u : S.unit K) _

/-- Actual radial argument, on the full quotient of nonzero elements by Γ. -/
def sIntegerOrbitNorm (q : SIntegerOrbits K S Γ) : {r : ℝ // 0 < r} :=
  Quotient.liftOn q (sIntegerElementNorm K S)
    (sIntegerElementNorm_eq_of_orbitRel K S Γ)

@[simp] theorem sIntegerOrbitNorm_mk (a : NonzeroRingElements (S.integer K)) :
    sIntegerOrbitNorm K S Γ (Quotient.mk _ a) = sIntegerElementNorm K S a := rfl

theorem sIntegerOrbitNorm_out (q : SIntegerOrbits K S Γ) :
    sIntegerElementNorm K S q.out = sIntegerOrbitNorm K S Γ q := by
  simpa only [sIntegerOrbitNorm_mk] using
    congrArg (sIntegerOrbitNorm K S Γ) (Quotient.out_eq q)

end HeckeGeneral.Arithmetic
