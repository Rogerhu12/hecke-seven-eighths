import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondAllocatedSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CenteredAllocatedChildren

/-!
# The complete centered second coefficient in the actual child source

Only the two original plain-factor dictionaries change in the comparison
rectangle.  Its characters, masks, prime slots, finite-ray labels,
extra Gauss normalizers, and Fourier locations remain those of the
original source.  The exact subtraction is retained inside each column
norm.  These identities apply before exceptional-row classification.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree HeckeGeneral.Characters
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum WholeAllocation

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {k : ℕ} {Ray : Type*} [CommGroup Ray]
variable {T : FixedChildCharacters F k} {phase : Ray →* Circle}
variable {S₁ S₂ : Finset (Ideal (𝓞 F))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 F))}

/-- The comparison has two single-ideal identities.  In particular no
identity for the centered coefficient or its polynomial is a field. -/
structure SecondCoefficientComparison
    (D : SecondCoefficientTermDictionary T phase S₁ S₂ S) where
  leftAtom : Ideal (𝓞 F) → ℂ
  rightAtom : Ideal (𝓞 F) → ℂ
  scale₁ : ℝ
  scale₂ : ℝ
  leftWeight : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ
  rightWeight : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ
  plain₁ : ∀ I ∈ S₁, leftAtom I * (phase (D.leftRay I) : ℂ) =
    (Real.sqrt scale₁ : ℂ)⁻¹ *
      (sourcePlainCoefficient T.plain T.plainTwist T.mask (sourceMomentIdeal I) *
        leftWeight (sourceMomentIdeal I))
  plain₂ : ∀ I ∈ S₂, rightAtom I * (phase (D.rightRay I) : ℂ) =
    (Real.sqrt scale₂ : ℂ)⁻¹ *
      (sourcePlainCoefficient T.plain T.plainTwist T.mask (sourceMomentIdeal I) *
        rightWeight (sourceMomentIdeal I))

namespace SecondCoefficientComparison

variable {D : SecondCoefficientTermDictionary T phase S₁ S₂ S}
variable (E : SecondCoefficientComparison D)

def dictionary : SecondCoefficientTermDictionary T phase S₁ S₂ S where
  leftAtom := E.leftAtom
  rightAtom := E.rightAtom
  slotAtom := D.slotAtom
  leftRay := D.leftRay
  rightRay := D.rightRay
  slotRay := D.slotRay
  scale₁ := E.scale₁
  scale₂ := E.scale₂
  base := D.base
  length := D.length
  leftWeight := E.leftWeight
  rightWeight := E.rightWeight
  slotWeight := D.slotWeight
  plain₁ := E.plain₁
  plain₂ := E.plain₂
  prime := D.prime

def centeredCoefficient (u v : ℂ) (t : Fin k → ℂ) (i : AllocationColumn F k) : ℂ :=
  D.normalizedCoefficient u v t i - E.dictionary.normalizedCoefficient u v t i

/-- The full subtraction is transported before taking any norm. -/
theorem centered_coefficient_residue (u v : ℂ) (t : Fin k → ℂ)
    (i : AllocationColumn F k) (hi : i ∈ childCartesianColumns S₁ S₂ S)
    (I : A.Exterior) (hI : I.val = allocationColumnIdeal i)
    (frequency g h : A.R) (hfrequency : frequency = g * h) :
    E.centeredCoefficient u v t i * (phase (D.ray i) : ℂ) *
        σ (A.sexticResidue I frequency) =
      SecondCoefficientTermDictionary.centralNormalizer u v t *
        (rawSourceCoefficient (σ := σ) T g h D.scale₁ D.scale₂ D.base D.length
          D.leftWeight D.rightWeight D.slotWeight i -
         rawSourceCoefficient (σ := σ) T g h E.scale₁ E.scale₂ D.base D.length
          E.leftWeight E.rightWeight D.slotWeight i) := by
  have hmain := D.normalized_coefficient_residue (σ := σ) u v t i hi I hI frequency g h hfrequency
  have hcomparison := E.dictionary.normalized_coefficient_residue (σ := σ) u v t i hi I hI
    frequency g h hfrequency
  change E.dictionary.normalizedCoefficient u v t i * (phase (D.ray i) : ℂ) *
    σ (A.sexticResidue I frequency) =
      SecondCoefficientTermDictionary.centralNormalizer u v t *
        rawSourceCoefficient (σ := σ) T g h E.scale₁ E.scale₂ D.base D.length
          E.leftWeight E.rightWeight D.slotWeight i at hcomparison
  rw [centeredCoefficient, sub_mul, sub_mul, hmain, hcomparison, mul_sub]

end SecondCoefficientComparison

private theorem centered_column_mem_source (B : ActualColumnAllocation F k)
    (i : AllocationColumn F k) (hi : i ∈ B.columns) :
    i ∈ childCartesianColumns B.plain₁ B.plain₂ B.slots := by
  rw [ActualColumnAllocation.columns, paired_allocated_columns_eq_filter] at hi
  exact (Finset.mem_filter.mp hi).1

section Sources

variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem centered_energy_congr {J : Type*}
    (rows : Finset H) (columns : Finset J) (q : H → ℂ)
    (c f : H → J → ℂ) (x : H → J → V) (ξ : V)
    (hc : ∀ h ∈ rows, ∀ i ∈ columns, c h i = f h i) :
    jointColumnEnergy rows columns q c x ξ = jointColumnEnergy rows columns q f x ξ := by
  unfold jointColumnEnergy
  apply Finset.sum_congr rfl
  intro h hh
  have hp : jointFourierColumn columns (c h) (x h) ξ =
      jointFourierColumn columns (f h) (x h) ξ := by
    unfold jointFourierColumn
    apply Finset.sum_congr rfl
    intro i hi
    rw [hc h hh i hi]
  rw [hp]

namespace ActualSecondCorrelationRows

variable (R : ActualSecondCorrelationRows A σ H ι)
variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]

/-- The literal centered left kernel energy, still with the whole
subtraction, is the actual centered allocated source energy. -/
theorem left_centered_energy_eq_source
    (C : A.GeneralArithmeticContext σ η hS)
    (B : ActualColumnAllocation F k) (T : FixedChildCharacters F k)
    (χ : (Ray × Ray) →* Circle)
    (D : SecondCoefficientTermDictionary T (fixedLeftPhase Ray χ)
      B.plain₁ B.plain₂ B.slots)
    (E : SecondCoefficientComparison D)
    (hbase : 1 < D.base) (hlength : ∀ i, 0 < D.length i)
    (IA : AllocationColumn F k → A.Exterior)
    (hIA : ∀ i ∈ childCartesianColumns B.plain₁ B.plain₂ B.slots,
      (IA i).val = allocationColumnIdeal i)
    (u v : ℂ) (t : Fin k → ℂ)
    (x₁ x₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : H → Fin k → HeightOneSpectrum (𝓞 F) → V) (ξ : V) :
    jointColumnEnergy R.rows B.columns (fun h => R.weight h * R.correlation h)
      (secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency D.ray χ
        (E.centeredCoefficient u v t))
      (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h)) ξ =
      ‖SecondCoefficientTermDictionary.centralNormalizer u v t‖ ^ 2 *
        (R.source C B T (fixedLeftPhase Ray χ) D hbase hlength x₁ x₂ x).centeredEnergy
          (σ := σ) E.scale₁ E.scale₂ (fun _ => E.leftWeight) (fun _ => E.rightWeight) ξ := by
  rw [R.energy_live]
  let c := fun h : R.live => fun i =>
    rawSourceCoefficient (σ := σ) T (R.factor C h.val) (R.extractedRow C h).element
        D.scale₁ D.scale₂ D.base D.length D.leftWeight D.rightWeight D.slotWeight i -
      rawSourceCoefficient (σ := σ) T (R.factor C h.val) (R.extractedRow C h).element
        E.scale₁ E.scale₂ D.base D.length E.leftWeight E.rightWeight D.slotWeight i
  have hc (h : R.live) (i : AllocationColumn F k) (hi : i ∈ B.columns) :
      secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency D.ray χ
        (E.centeredCoefficient u v t) h.val i =
      SecondCoefficientTermDictionary.centralNormalizer u v t * c h i :=
    E.centered_coefficient_residue u v t i (centered_column_mem_source B i hi)
      (IA i) (hIA i (centered_column_mem_source B i hi))
      (R.frequency h.val) (R.factor C h.val) (R.extractedRow C h).element
      (R.extractedRow C h).frequency
  calc
    _ = jointColumnEnergy Finset.univ B.columns
        (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h i => SecondCoefficientTermDictionary.centralNormalizer u v t * c h i)
        (fun h => rawSourceLocation (x₁ h.val) (x₂ h.val) (x h.val)) ξ :=
      centered_energy_congr _ _ _ _ _ _ _ (fun h _ i hi => hc h i hi)
    _ = _ := joint_energy_constant_coefficient _ _ _ c _ _ ξ

/-- The right centered column uses the same residual ideal and retains
its subtraction under the star until the complete norm is conjugated. -/
theorem right_centered_energy_eq_source
    (C : A.GeneralArithmeticContext σ η hS)
    (B : ActualColumnAllocation F k) (T : FixedChildCharacters F k)
    (χ : (Ray × Ray) →* Circle)
    (D : SecondCoefficientTermDictionary T (fixedRightPhase Ray χ)
      B.plain₁ B.plain₂ B.slots)
    (E : SecondCoefficientComparison D)
    (hbase : 1 < D.base) (hlength : ∀ i, 0 < D.length i)
    (IB : AllocationColumn F k → A.Exterior)
    (hIB : ∀ i ∈ childCartesianColumns B.plain₁ B.plain₂ B.slots,
      (IB i).val = allocationColumnIdeal i)
    (u v : ℂ) (t : Fin k → ℂ)
    (x₁ x₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : H → Fin k → HeightOneSpectrum (𝓞 F) → V) (ξ : V) :
    jointColumnEnergy R.rows B.columns (fun h => R.weight h * R.correlation h)
      (secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency D.ray χ
        (E.centeredCoefficient u v t))
      (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h)) ξ =
      ‖SecondCoefficientTermDictionary.centralNormalizer u v t‖ ^ 2 *
        (R.source C B T (fixedRightPhase Ray χ) D hbase hlength x₁ x₂ x).negativeSide.centeredEnergy
          (σ := σ) E.scale₁ E.scale₂ (fun _ => E.leftWeight) (fun _ => E.rightWeight) ξ := by
  rw [R.energy_live]
  let c := fun h : R.live => fun i =>
    rawSourceCoefficient (σ := σ) T (-R.factor C h.val) (R.extractedRow C h).element
        D.scale₁ D.scale₂ D.base D.length D.leftWeight D.rightWeight D.slotWeight i -
      rawSourceCoefficient (σ := σ) T (-R.factor C h.val) (R.extractedRow C h).element
        E.scale₁ E.scale₂ D.base D.length E.leftWeight E.rightWeight D.slotWeight i
  let ν := SecondCoefficientTermDictionary.centralNormalizer u v t
  have hc (h : R.live) (i : AllocationColumn F k) (hi : i ∈ B.columns) :
      secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency D.ray χ
        (E.centeredCoefficient u v t) h.val i = star ν * star (c h i) := by
    have he := E.centered_coefficient_residue (σ := σ) u v t i
      (centered_column_mem_source B i hi) (IB i)
      (hIB i (centered_column_mem_source B i hi))
      (-R.frequency h.val) (-R.factor C h.val) (R.extractedRow C h).element
      ((congrArg Neg.neg (R.extractedRow C h).frequency).trans (neg_mul _ _).symm)
    exact (congrArg star he).trans (star_mul' _ _)
  calc
    _ = jointColumnEnergy Finset.univ B.columns
        (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h i => star ν * star (c h i))
        (fun h => rawSourceLocation (x₁ h.val) (x₂ h.val) (x h.val)) ξ :=
      centered_energy_congr _ _ _ _ _ _ _ (fun h _ i hi => hc h i hi)
    _ = ‖ν‖ ^ 2 * jointColumnEnergy Finset.univ B.columns
        (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h i => star (c h i))
        (fun h => rawSourceLocation (x₁ h.val) (x₂ h.val) (x h.val)) ξ := by
      rw [joint_energy_constant_coefficient, norm_star]
    _ = _ := by
      rw [joint_energy_star_neg_locations]
      simp only [source, ActualAllocatedSource.negativeSide, ActualAllocatedSource.centeredEnergy,
        ActualChildRow.negative]
      apply congrArg (fun locations : R.live → AllocationColumn F k → V =>
        ‖ν‖ ^ 2 * jointColumnEnergy Finset.univ B.columns
          (fun h : R.live => R.weight h.val * R.correlation h.val) c locations ξ)
      funext h i
      exact (rawSourceLocation_neg (x₁ h.val) (x₂ h.val) (x h.val) i).symm

end ActualSecondCorrelationRows
end Sources
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondCoefficientComparison.centered_coefficient_residue
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.left_centered_energy_eq_source
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.right_centered_energy_eq_source
