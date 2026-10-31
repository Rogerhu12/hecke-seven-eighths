import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondBranchProduction
import Mathlib.Tactic.Abel

/-!
# Original log-norm locations and common row translations

The logarithm of the actual complete ideal norm is the sum of the two
plain logarithms and the logarithm of each original prime occurrence.
Thus the canonical log-radius Fourier kernel has literal single-atom
locations on the same Cartesian source.

A common translation of a complete row contributes one Fourier phase
of norm one.  The exact identities below remove it inside the original
squared energy, before a child profile or a capacity child is chosen.
No row-dependent norm profile or energy estimate is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

section RowTranslation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The complete column sum acquires just one unit-modulus row phase. -/
theorem jointFourierColumn_rowTranslation {ι : Type*}
    (columns : Finset ι) (c : ι → ℂ) (x : ι → V) (z ξ : V) :
    jointFourierColumn columns c (fun i => z + x i) ξ =
      jointPhase ξ z * jointFourierColumn columns c x ξ := by
  unfold jointFourierColumn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [jointPhase_add]
  ring

/-- The removal of a common row translation is exact for arbitrary
original coefficients, including complete centered coefficients. -/
theorem jointColumnEnergy_rowTranslation {H ι : Type*}
    (rows : Finset H) (columns : Finset ι) (q : H → ℂ)
    (c : H → ι → ℂ) (x : H → ι → V) (z : H → V) (ξ : V) :
    jointColumnEnergy rows columns q c (fun h i => z h + x h i) ξ =
      jointColumnEnergy rows columns q c x ξ := by
  unfold jointColumnEnergy
  apply Finset.sum_congr rfl
  intro h _
  rw [jointFourierColumn_rowTranslation, norm_mul, norm_jointPhase, one_mul]

end RowTranslation

section LogNorm

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

private theorem real_absNorm_ne_zero (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    (Ideal.absNorm I : ℝ) ≠ 0 := by
  exact_mod_cast Ideal.absNorm_ne_zero_of_nonZeroDivisors
    (⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ : (Ideal (𝓞 K))⁰)

/-- Each prime occurrence contributes once, including repeated primes
and the empty product when the original source has no slots. -/
theorem log_allocationColumnIdeal (i : AllocationColumn K k)
    (hleft : i.1.1 ≠ 0) (hright : i.1.2 ≠ 0) :
    Real.log (Ideal.absNorm (allocationColumnIdeal i) : ℝ) =
      Real.log (Ideal.absNorm i.1.1 : ℝ) + Real.log (Ideal.absNorm i.1.2 : ℝ) +
        ∑ j, Real.log (Ideal.absNorm (i.2 j).asIdeal : ℝ) := by
  have h₁ := real_absNorm_ne_zero i.1.1 hleft
  have h₂ := real_absNorm_ne_zero i.1.2 hright
  have hp (j : Fin k) : (Ideal.absNorm (i.2 j).asIdeal : ℝ) ≠ 0 :=
    real_absNorm_ne_zero _ (by simpa only [Ideal.zero_eq_bot] using (i.2 j).ne_bot)
  simp only [allocationColumnIdeal, map_mul, map_prod, Nat.cast_mul, Nat.cast_prod]
  rw [Real.log_mul (mul_ne_zero h₁ h₂) (Finset.prod_ne_zero_iff.mpr (fun j _ => hp j)),
    Real.log_mul h₁ h₂, Real.log_prod (fun j _ => hp j)]

/-- The actual complete log norm is exactly the raw single-factor
location used by the allocated source. -/
theorem rawSourceLocation_neg_log_norm (i : AllocationColumn K k)
    (hleft : i.1.1 ≠ 0) (hright : i.1.2 ≠ 0) :
    rawSourceLocation
        (fun I : NonzeroIdeal K => -Real.log (idealNorm K I))
        (fun I : NonzeroIdeal K => -Real.log (idealNorm K I))
        (fun (_ : Fin k) (p : HeightOneSpectrum (𝓞 K)) =>
          -Real.log (Ideal.absNorm p.asIdeal : ℝ)) i =
      -Real.log (Ideal.absNorm (allocationColumnIdeal i) : ℝ) := by
  simp only [rawSourceLocation, childCartesianLocation, idealNorm,
    sourceMomentIdeal_val_of_ne_zero _ hleft, sourceMomentIdeal_val_of_ne_zero _ hright,
    log_allocationColumnIdeal i hleft hright, neg_add, Finset.sum_neg_distrib]

/-- A literal exterior ideal label supplies the same location.  Only
the original ideal-product identity is needed. -/
theorem rawSourceLocation_neg_log_exterior {A : SArithmeticData K}
    (i : AllocationColumn K k) (hleft : i.1.1 ≠ 0) (hright : i.1.2 ≠ 0)
    (I : A.Exterior) (hI : I.val = allocationColumnIdeal i) :
    rawSourceLocation
        (fun J : NonzeroIdeal K => -Real.log (idealNorm K J))
        (fun J : NonzeroIdeal K => -Real.log (idealNorm K J))
        (fun (_ : Fin k) (p : HeightOneSpectrum (𝓞 K)) =>
          -Real.log (Ideal.absNorm p.asIdeal : ℝ)) i =
      -Real.log (A.exteriorNorm I) := by
  rw [rawSourceLocation_neg_log_norm i hleft hright]
  change -Real.log (Ideal.absNorm (allocationColumnIdeal i) : ℝ) =
    -Real.log (Ideal.absNorm I.val : ℝ)
  rw [hI]

end LogNorm

section Frames

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {side : SecondColumnSide} {k : ℕ}

namespace SecondSideFrame

variable (f : SecondSideFrame (V := V) C R Ray side k)

/-- Add common row translations at the individual original occurrences.
No coefficient, character, ideal, slot or scale is changed. -/
def translateLocations (z₁ z₂ : H → V) (z : H → Fin k → V) :
    SecondSideFrame (V := V) C R Ray side k :=
  { f with
    leftLocation := fun h I => z₁ h + f.leftLocation h I
    rightLocation := fun h I => z₂ h + f.rightLocation h I
    slotLocation := fun h j p => z h j + f.slotLocation h j p }

@[simp] theorem translateLocations_coefficient
    (z₁ z₂ : H → V) (z : H → Fin k → V) :
    (f.translateLocations z₁ z₂ z).coefficient = f.coefficient := by
  cases side <;> rfl

@[simp] theorem translateLocations_normalizationScale
    (z₁ z₂ : H → V) (z : H → Fin k → V) :
    (f.translateLocations z₁ z₂ z).normalizationScale = f.normalizationScale := rfl

theorem translateLocations_point
    (z₁ z₂ : H → V) (z : H → Fin k → V) (h : H)
    (i : AllocationColumn K k) :
    rawSourceLocation ((f.translateLocations z₁ z₂ z).leftLocation h)
        ((f.translateLocations z₁ z₂ z).rightLocation h)
        ((f.translateLocations z₁ z₂ z).slotLocation h) i =
      (z₁ h + z₂ h + ∑ j, z h j) +
        rawSourceLocation (f.leftLocation h) (f.rightLocation h) (f.slotLocation h) i := by
  simp only [translateLocations, rawSourceLocation, childCartesianLocation,
    Finset.sum_add_distrib]
  abel

/-- The two Fourier representations have exactly the same original
energy.  This equality is available before selecting any child. -/
theorem translateLocations_energy
    (z₁ z₂ : H → V) (z : H → Fin k → V) (ξ : V) :
    (f.translateLocations z₁ z₂ z).energy ξ = f.energy ξ := by
  unfold energy
  rw [f.translateLocations_coefficient]
  have hlocation :
      (fun h => rawSourceLocation ((f.translateLocations z₁ z₂ z).leftLocation h)
        ((f.translateLocations z₁ z₂ z).rightLocation h)
        ((f.translateLocations z₁ z₂ z).slotLocation h)) =
      (fun h i => (z₁ h + z₂ h + ∑ j, z h j) +
        rawSourceLocation (f.leftLocation h) (f.rightLocation h) (f.slotLocation h) i) := by
    funext h i
    exact f.translateLocations_point z₁ z₂ z h i
  rw [hlocation]
  exact jointColumnEnergy_rowTranslation R.rows f.allocation.columns
    (fun h => R.weight h * R.correlation h) f.coefficient
    (fun h => rawSourceLocation (f.leftLocation h) (f.rightLocation h) (f.slotLocation h))
    (fun h => z₁ h + z₂ h + ∑ j, z h j) ξ

end SecondSideFrame
end Frames

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.jointColumnEnergy_rowTranslation
#print axioms HeckeSkeleton.Moments.EngineStep.log_allocationColumnIdeal
#print axioms HeckeSkeleton.Moments.EngineStep.rawSourceLocation_neg_log_exterior
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.translateLocations_energy
