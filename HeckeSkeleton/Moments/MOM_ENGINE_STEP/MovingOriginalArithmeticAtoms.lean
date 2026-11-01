import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalAtomPhases
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingEngineOutput

/-!
# Actual parent arithmetic atoms from the original moving-row recipe

The fixed correction and displayed moving character enter each original
column coefficient before the complete row varies.  The complete row
map, its unit sector and its actual zero-extended phase are unchanged.
Both fixed deletion ideals remain in the row-independent coefficient.

The arithmetic dictionary is constructed from the raw moving recipe;
it is not a further input to the child family.  Its transport uses the
same selected capacity child and the same removed slots as that family.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {ω ψ : HeckeCharacter K}

/-- The original representative contracts to the very ideal of its
actual sixth-unit orbit.  No normalized representative is substituted. -/
theorem principalExterior_out_eq_actualOrbitIdeal
    (q : ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) :
    (ProbeOrbitNormSum.principalExterior A q.out).val =
      (actualSIntegerOrbitIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) q).val := by
  rw [← generated_sIntegerModulusContraction
    (ProbeOrbitNormSum.principalExterior A q.out) q.out.val
      (ProbeOrbitNormSum.principalExterior_generates A q.out)]
  exact congrArg
    (actualSIntegerOrbitContraction K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (Quotient.out_eq q)

theorem completeIdealSectorRowMap_originalIdeal
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (sector : HeckeGeneral.Analysis.NonzeroIdeal K → SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : completeIdealIsExterior K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u) :
    (ProbeOrbitNormSum.principalExterior A
      (completeIdealSectorRowMap (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P sector u).out).val =
        u.val := by
  rw [principalExterior_out_eq_actualOrbitIdeal]
  change (actualSIntegerOrbitIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    (completeIdealSectorRowMap (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P sector
      (⟨u, hu⟩ : ExteriorIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))).val)).val = _
  rw [completeIdealSectorRowMap_exterior, decomposedIdealSectorOrbit_ideal]

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- The two fixed deletion ideals in the exact arithmetic coefficient.
This product is not a new displayed moving support or a new budget. -/
def arithmeticMask : HeckeGeneral.Analysis.NonzeroIdeal K :=
  ⟨Q.moving.support.val * Q.remaining.val,
    mem_nonZeroDivisors_of_ne_zero (mul_ne_zero Q.moving.support.property.1
      (nonZeroDivisors.ne_zero Q.remaining.property))⟩

theorem mask_eq_arithmeticMask (ξ : X) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    (data ξ).commonMask u I =
      (completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
        decide (IsCoprime I Q.arithmeticMask.val)) := by
  rw [Q.mask ξ u I]
  simp only [arithmeticMask, IsCoprime.mul_right_iff, decide_and, Bool.and_assoc]

/-- The same original complete row and actual phase, with the fixed
moving character computed in every background coefficient. -/
def arithmeticAtoms (ξ : X) :
    ParentArithmeticAtoms
      (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (data ξ) :=
  completeIdealFixedTwistArithmeticAtoms (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R
    Q.sector (data ξ) Q.arithmeticMask (Q.correction * Q.moving.character)
    (Q.exterior ξ) (Q.character ξ) (Q.mask_eq_arithmeticMask ξ)

theorem arithmeticAtoms_originalIdeal (ξ : X) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : (data ξ).allowedRow u) :
    (ProbeOrbitNormSum.principalExterior A ((Q.arithmeticAtoms ξ).rowMap u).out).val =
      u.val :=
  completeIdealSectorRowMap_originalIdeal P Q.sector u (Q.exterior ξ u hu)

theorem arithmeticAtoms_leftPhase
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ) (ξ : X)
    (q : ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (Q.arithmeticAtoms ξ).leftPhase q I =
      actualIdealResidue (A := A) (σ := σ) I.val q.out.val :=
  actualProbeOrbitSexticEvaluation_eq_actualIdealResidue P hroot hemb I q

theorem arithmeticAtoms_rightPhase
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ) (ξ : X)
    (q : ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (Q.arithmeticAtoms ξ).rightPhase q I =
      actualIdealResidue (A := A) (σ := σ) I.val q.out.val :=
  actualProbeOrbitSexticEvaluation_eq_actualIdealResidue P hroot hemb I q

theorem arithmeticAtoms_primePhase
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ) (ξ : X)
    (q : ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (i : Fin (data ξ).geometry.slotCount) (p : HeightOneSpectrum (𝓞 K)) :
    (Q.arithmeticAtoms ξ).primePhase q i p =
      actualIdealResidue (A := A) (σ := σ) p.asIdeal q.out.val :=
  actualProbeOrbitSexticEvaluation_eq_actualIdealResidue P hroot hemb
    (momentPrimeIdeal K p) q

end CompleteMovingRowRecipe

namespace ActualNormalizedPairFamily.MovingRowInputs

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}
variable {family : ActualNormalizedPairFamily A σ V Λ ω ψ Z} {labels : Finset Λ}
variable (raw : family.MovingRowInputs (P := P) (R := R) labels)

/-- Every original calibration now has computed arithmetic atoms.
Existing leftAtoms/rightAtoms transport these along exactly the
family's chosen child, rather than choosing another removal. -/
def arithmeticInputs : family.ArithmeticAtomInputs labels
    (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) where
  left b hb ξ := (raw.left b hb).arithmeticAtoms ξ
  right b hb ξ := (raw.right b hb).arithmeticAtoms ξ

end ActualNormalizedPairFamily.MovingRowInputs

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.principalExterior_out_eq_actualOrbitIdeal
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.arithmeticAtoms
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.arithmeticAtoms_originalIdeal
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.MovingRowInputs.arithmeticInputs
