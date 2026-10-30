import HeckeGeneral.Arithmetic.IdealMobiusMask
import HeckeGeneral.Arithmetic.SIntegerOrbitDilation
import HeckeGeneral.Arithmetic.SIntegerFiniteLocalization
import Mathlib.RingTheory.DedekindDomain.Dvr

/-! Actual ideal masks on the original Γ-orbits. Only the generator version
requires the actual S-integer ring to be principal. -/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K))
local notation "OS" => S.integer K
local notation "N" => NonzeroRingElements OS
local notation "Q" => SIntegerOrbits K S Γ

/-- The actual valuation-defined S-integer ring is Dedekind because it is
the localization of the ordinary integer ring at a nonzero denominator. -/
theorem sIntegerOrbitMask_isDedekindDomain : IsDedekindDomain OS := by
  letI := sInteger_isLocalizationAway_finiteDenominator K S
  exact IsLocalization.isDedekindDomain (𝓞 K)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (finiteSIntegerDenominator_ne_zero K S)) OS

local instance : IsDedekindDomain OS := sIntegerOrbitMask_isDedekindDomain K S

local instance : UniqueFactorizationMonoid (Ideal OS) := Ideal.uniqueFactorizationMonoid

/-- Membership in every actual ideal is invariant under the original units. -/
theorem sIntegerOrbitIdealMembership_rep_iff (I : Ideal OS) (a b : N)
    (hab : MulAction.orbitRel (sIntegerUnitSubgroup K S Γ) N a b) :
    a.val ∈ I ↔ b.val ∈ I := by
  obtain ⟨u, hu⟩ := (sIntegerOrbitRelation_iff K S Γ a b).mp hab
  let U := S.unitEquivUnitsInteger K u.val
  have hU : (U : OS) * b.val = a.val := Subtype.ext hu
  constructor
  · intro ha
    have hb : b.val = (U⁻¹ : OSˣ) * a.val := by rw [← hU]; simp [mul_assoc]
    rw [hb]
    exact I.mul_mem_left _ ha
  · intro hb
    rw [← hU]
    exact I.mul_mem_left _ hb

def sIntegerOrbitIdealMembership (I : Ideal OS) (q : Q) : Prop :=
  Quotient.liftOn q (fun a => a.val ∈ I)
    (fun a b hab => propext (sIntegerOrbitIdealMembership_rep_iff K S Γ I a b hab))

@[simp] theorem sIntegerOrbitIdealMembership_mk (I : Ideal OS) (a : N) :
    sIntegerOrbitIdealMembership K S Γ I (Quotient.mk _ a) ↔ a.val ∈ I := Iff.rfl

def sIntegerOrbitMembershipIndicator (I : Ideal OS) (q : Q) : ℂ :=
  if sIntegerOrbitIdealMembership K S Γ I q then 1 else 0

@[simp] theorem sIntegerOrbitMembershipIndicator_mk (I : Ideal OS) (a : N) :
    sIntegerOrbitMembershipIndicator K S Γ I (Quotient.mk _ a) =
      IdealMobiusMask.membershipIndicator I a.val := rfl

def sIntegerOrbitAvoidanceMask (M : Finset (HeightOneSpectrum OS)) (q : Q) : ℂ :=
  if ∀ p ∈ M, ¬ sIntegerOrbitIdealMembership K S Γ p.asIdeal q then 1 else 0

@[simp] theorem sIntegerOrbitAvoidanceMask_mk
    (M : Finset (HeightOneSpectrum OS)) (a : N) :
    sIntegerOrbitAvoidanceMask K S Γ M (Quotient.mk _ a) =
      IdealMobiusMask.avoidanceMask M a.val := rfl

theorem sIntegerOrbitAvoidanceMask_zero_or_one
    (M : Finset (HeightOneSpectrum OS)) (q : Q) :
    sIntegerOrbitAvoidanceMask K S Γ M q = 0 ∨
      sIntegerOrbitAvoidanceMask K S Γ M q = 1 := by
  unfold sIntegerOrbitAvoidanceMask
  split_ifs <;> simp

theorem norm_sIntegerOrbitAvoidanceMask_le_one
    (M : Finset (HeightOneSpectrum OS)) (q : Q) :
    ‖sIntegerOrbitAvoidanceMask K S Γ M q‖ ≤ 1 := by
  rcases sIntegerOrbitAvoidanceMask_zero_or_one K S Γ M q with h | h <;> rw [h] <;> simp

/-- Exact ideal Möbius expansion in every original subgroup sector. -/
theorem sIntegerOrbitAvoidanceMask_moebius_expansion
    (M : Finset (HeightOneSpectrum OS)) (q : Q) :
    sIntegerOrbitAvoidanceMask K S Γ M q = ∑ T ∈ M.powerset,
      (moebius (IdealMobiusMask.primeProduct T) : ℂ) *
        sIntegerOrbitMembershipIndicator K S Γ (IdealMobiusMask.primeProduct T) q := by
  refine Quotient.inductionOn q ?_
  intro a
  exact IdealMobiusMask.avoidanceMask_moebius_expansion M a.val

section Principal

variable [IsPrincipalIdealRing (S.integer K)]

/-- A genuine nonzero generator of the actual mask ideal in OS. -/
def sIntegerMaskGenerator (M : Finset (HeightOneSpectrum OS)) : N :=
  ⟨IdealMobiusMask.maskGenerator M, IdealMobiusMask.maskGenerator_ne_zero M⟩

theorem sIntegerOrbitMaskMembership_iff_divisible
    (M : Finset (HeightOneSpectrum OS)) (q : Q) :
    sIntegerOrbitIdealMembership K S Γ (IdealMobiusMask.primeProduct M) q ↔
      sIntegerOrbitDivisible K S Γ (sIntegerMaskGenerator K S M) q := by
  refine Quotient.inductionOn q ?_
  intro a
  exact (IdealMobiusMask.maskGenerator_dvd_iff M a.val).symm

theorem sIntegerOrbitMaskMembership_iff_dilation
    (M : Finset (HeightOneSpectrum OS)) (q : Q) :
    sIntegerOrbitIdealMembership K S Γ (IdealMobiusMask.primeProduct M) q ↔
      ∃ p : Q, sIntegerOrbitDilation K S Γ (sIntegerMaskGenerator K S M) p = q := by
  rw [sIntegerOrbitMaskMembership_iff_divisible,
    sIntegerOrbitDivisible_iff_exists]

/-- The generator form is derived from ideal membership, not substituted for it. -/
theorem sIntegerOrbitAvoidanceMask_generator_expansion
    (M : Finset (HeightOneSpectrum OS)) (q : Q) :
    sIntegerOrbitAvoidanceMask K S Γ M q = ∑ T ∈ M.powerset,
      (moebius (IdealMobiusMask.primeProduct T) : ℂ) *
        (if sIntegerOrbitDivisible K S Γ (sIntegerMaskGenerator K S T) q then 1 else 0) := by
  rw [sIntegerOrbitAvoidanceMask_moebius_expansion]
  apply Finset.sum_congr rfl
  intro T _hT
  rw [sIntegerOrbitMembershipIndicator, sIntegerOrbitMaskMembership_iff_divisible]

end Principal

end HeckeGeneral.Arithmetic
