import Expansion.CanonicalDetectorCharacters
import ArithmeticFrequencyRowConductorNorm
import RowCharacterCanonicalUniqueness
import HeckeSkeleton.HeckeConductorNorm

/-!
# Uniform arithmetic inputs for the two actual detector presentations

Fixed infinity types and the conductor scale are derived from the original
finite-order arithmetic row character. No rowwise analytic conductor bound
or independent infinity-type identification is assumed. The constant uses
the genuine fixed S conductor budget and both finite background conductors.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Arithmetic.ConductorNormDraft
open HeckeSkeleton.HeckeConductorNorm HeckeSkeleton.ExplicitHeckeFunctionalEquation
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (E : RowEulerData K S P) (ψ : HeckeCharacter K)

theorem canonicalDetector_radial (i : Fin 2) (u : FrequencyRow K S) :
    (fun v => heckeRadialParameter K v (canonicalDetectorCharacter K ψ S P E i u)) =
      (fun v => heckeRadialParameter K v (canonicalDetectorBackground K ψ i)) := by
  funext v
  rw [canonicalDetectorCharacter, heckeRadialParameter_mul,
    heckeRadialParameter_finiteOrder K v (E.rows.finite_order u), add_zero]

theorem canonicalDetector_weight (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (i : Fin 2) (u : FrequencyRow K S) :
    heckeArchWeight K (canonicalDetectorCharacter K ψ S P E i u) =
      heckeArchWeight K (canonicalDetectorBackground K ψ i) := by
  funext v
  rw [heckeArchWeight_of_complex K _ v (hcomplex v),
    heckeArchWeight_of_complex K _ v (hcomplex v), canonicalDetectorCharacter,
    heckeComplexWeight_mul, heckeComplexWeight_finiteOrder K v (hcomplex v)
      (E.rows.finite_order u), add_zero]

/-- A single explicit scale constant for both arithmetic presentations. -/
def canonicalDetectorConductorConstant : ℝ :=
  1 + 2 * (∑ i : Fin 2,
    ((finiteConductor K (canonicalDetectorBackground K ψ i)).val.absNorm : ℝ)) *
      (NumberField.discr K).natAbs * sexticSConductorNormConstant K S

theorem canonicalDetectorConductorConstant_ge_one :
    1 ≤ canonicalDetectorConductorConstant K S ψ := by
  unfold canonicalDetectorConductorConstant
  exact le_add_of_nonneg_right (by positivity)

theorem row_conductorScale_le_original_norm (u : FrequencyRow K S) :
    heckeConductorScale K (E.rows.character u) ≤
      (NumberField.discr K).natAbs * (sexticSConductorNormConstant K S : ℝ) *
        HeckeGeneral.Analysis.idealNorm K u.ideal.val := by
  rw [rowCharacterInput_character_eq_arithmetic K S P E.rows u]
  have hn : ((finiteConductor K (arithmeticRowCharacter K S P u)).val.absNorm : ℝ) ≤
      (sexticSConductorNormConstant K S : ℝ) *
        HeckeGeneral.Analysis.idealNorm K u.ideal.val := by
    dsimp only [HeckeGeneral.Analysis.idealNorm]
    exact_mod_cast arithmeticRowCharacter_finiteConductor_absNorm_le_originalIdeal K S P u
  unfold heckeConductorScale
  exact (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)).trans_eq (by ring)

set_option maxHeartbeats 800000 in
/-- The actual conductor hypothesis of the zero and saturation theorems
holds uniformly for every original row of norm at most twice its shell. -/
theorem canonicalDetector_conductor (i : Fin 2) (u : FrequencyRow K S)
    (U : ℝ) (hU : 0 ≤ U)
    (hu : HeckeGeneral.Analysis.idealNorm K u.ideal.val ≤ 2 * U) :
    heckeConductorScale K (canonicalDetectorCharacter K ψ S P E i u) ≤
      canonicalDetectorConductorConstant K S ψ * U := by
  let M : ℝ := ∑ i : Fin 2,
    ((finiteConductor K (canonicalDetectorBackground K ψ i)).val.absNorm : ℝ)
  let A : ℝ := (NumberField.discr K).natAbs * (sexticSConductorNormConstant K S : ℝ)
  let b : ℝ := ((finiteConductor K (canonicalDetectorBackground K ψ i)).val.absNorm : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have hbM : b ≤ M := by
    dsimp only [b, M]
    apply Finset.single_le_sum _ (Finset.mem_univ i)
    intro j _hj
    exact Nat.cast_nonneg _
  have hrow : heckeConductorScale K (E.rows.character u) ≤ A * (2 * U) :=
    (row_conductorScale_le_original_norm K S P E u).trans
      (mul_le_mul_of_nonneg_left hu hA)
  calc
    _ ≤ b * heckeConductorScale K (E.rows.character u) :=
      conductorScale_mul_le K (canonicalDetectorBackground K ψ i) (E.rows.character u)
    _ ≤ b * (A * (2 * U)) := mul_le_mul_of_nonneg_left hrow hb
    _ ≤ M * (A * (2 * U)) := mul_le_mul_of_nonneg_right hbM (by positivity)
    _ ≤ M * (A * (2 * U)) + U := le_add_of_nonneg_right hU
    _ = canonicalDetectorConductorConstant K S ψ * U := by
      dsimp only [canonicalDetectorConductorConstant, M, A]
      ring

end Expansion.Project

#print axioms Expansion.Project.canonicalDetector_radial
#print axioms Expansion.Project.canonicalDetector_weight
#print axioms Expansion.Project.canonicalDetector_conductor
