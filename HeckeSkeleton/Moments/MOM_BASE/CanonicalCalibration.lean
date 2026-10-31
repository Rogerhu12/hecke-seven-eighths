import HeckeSkeleton.Base
import HeckeAxiom.GaussCalibration
import HeckeSkeleton.Moments.MOM_BASE.PairedPhases

/-!
# Actual canonical squarefree coefficients

The two calibration identities are specialized to the single arithmetic
choice already fixed by `TargetContext`. The canonical coefficient and its
first/second primitive transforms therefore need no additional arithmetic
calibration hypothesis.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local notation "S" => places K c
local notation "D" => arithmeticData K c
local notation "Λ" => (axiomChoice K c).Lambda
local notation "G" => (axiomChoice K c).G

/-- The coefficient a₀ = conjugate(Λ) γ₂ in the manuscript. -/
def canonicalCoefficient (I : ExteriorIdeal K S) : ℂ :=
  conj (heckeIdealCoefficient K Λ I.val) * thetaGamma K S D I 2

theorem canonical_cube_calibration (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    thetaGamma K S D I 2 ^ 3 =
      (moebius I.val.val : ℂ) * heckeIdealCoefficient K Λ I.val :=
  (axiomChoice K c).cube_calibration I hI

theorem canonical_first_transform (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    canonicalCoefficient K c I * thetaGamma K S D I 1 =
      (moebius I.val.val : ℂ) * heckeIdealCoefficient K G I.val :=
  (axiomChoice K c).mixed_calibration I hI

theorem canonical_lambda_norm (I : ExteriorIdeal K S) :
    ‖heckeIdealCoefficient K Λ I.val‖ = 1 :=
  Paired.norm_idealCoefficient_of_unramified K Λ I.val
    (fun p hp => (axiomChoice K c).Lambda_unramified p (I.property p hp))

theorem canonical_finite_character_norm (I : ExteriorIdeal K S) :
    ‖heckeIdealCoefficient K G I.val‖ = 1 :=
  Paired.norm_idealCoefficient_of_unramified K G I.val
    (fun p hp => (axiomChoice K c).G_unramified p (I.property p hp))

theorem canonical_G_finiteOrder : FiniteOrder G := (axiomChoice K c).G_finiteOrder

theorem squarefree_moebius_norm (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    ‖(moebius I.val.val : ℂ)‖ = 1 := by
  rw [hI.moebius_eq]
  simp

theorem squarefree_moebius_sq (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    (moebius I.val.val : ℂ) ^ 2 = 1 := by
  rw [hI.moebius_eq]
  push_cast
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

/-- Unit size of the actual normalized cubic Gauss coefficient on squarefree ideals. -/
theorem canonical_gamma_two_norm (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    ‖thetaGamma K S D I 2‖ = 1 := by
  have h := congrArg norm (canonical_cube_calibration K c I hI)
  rw [norm_pow, norm_mul, squarefree_moebius_norm K c I hI,
    canonical_lambda_norm K c I, one_mul] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3 : ℕ) ≠ 0)).mp h

theorem canonicalCoefficient_norm (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    ‖canonicalCoefficient K c I‖ = 1 := by
  rw [canonicalCoefficient, norm_mul, norm_conj, canonical_lambda_norm K c I,
    canonical_gamma_two_norm K c I hI, one_mul]

/-- The reverse primitive transform, with its finite-order correction. -/
theorem canonical_second_transform (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    (moebius I.val.val : ℂ) * conj (thetaGamma K S D I 1) =
      canonicalCoefficient K c I * conj (heckeIdealCoefficient K G I.val) := by
  have hm := squarefree_moebius_sq K c I hI
  have ha : canonicalCoefficient K c I * conj (canonicalCoefficient K c I) = 1 := by
    rw [Complex.mul_conj', canonicalCoefficient_norm K c I hI]
    norm_num
  have hconj := congrArg conj (canonical_first_transform K c I hI)
  simp only [map_mul, map_intCast] at hconj
  linear_combination (moebius I.val.val : ℂ) * canonicalCoefficient K c I * hconj -
    (moebius I.val.val : ℂ) * conj (thetaGamma K S D I 1) * ha +
    canonicalCoefficient K c I * conj (heckeIdealCoefficient K G I.val) * hm

/-- The live theta period is conjugate(Λ) times the original background. -/
def canonicalPeriod (ν : HeckeCharacter K) : HeckeCharacter K := Λ⁻¹ * ν

theorem canonicalPeriod_coefficient (ν : HeckeCharacter K) (I : ExteriorIdeal K S) :
    heckeIdealCoefficient K (canonicalPeriod K c ν) I.val =
      conj (heckeIdealCoefficient K Λ I.val) * heckeIdealCoefficient K ν I.val := by
  unfold canonicalPeriod
  rw [mul_comm Λ⁻¹ ν, Paired.idealCoefficient_character_mul K ν Λ⁻¹ I.val
    (fun p hp => ((axiomChoice K c).Lambda_unramified p (I.property p hp)).inv K),
    heckeIdealCoefficient_inv]
  ring

end HeckeSkeleton.Moments.MOM_BASE
