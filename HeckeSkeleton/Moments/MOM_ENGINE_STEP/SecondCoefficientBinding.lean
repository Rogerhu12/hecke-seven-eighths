import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondAllocationKernel
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedChildProvider

/-!
# Actual second coefficients from the primitive factor dictionaries

Finite-ray phases are multiplied on the two plain occurrences and every
prime slot.  The complete residue symbol is then split by its proved
ideal multiplicativity, preserving all ramification zeros.  The right
coefficient keeps its star and its frequency -h; conjugating the whole
Fourier column changes only its Fourier locations to their negatives.

The primitive inputs are single-factor coefficient/normalization/phase
identities.  There is no whole-polynomial or energy comparison input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ} {k : ℕ}

theorem sourceMomentIdeal_val_of_ne_zero (I : Ideal (𝓞 F)) (hI : I ≠ 0) :
    (sourceMomentIdeal I).val = I := by
  simp only [sourceMomentIdeal, dif_pos hI]

namespace FixedChildCharacters

def bareCoefficient (T : FixedChildCharacters F k)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ) :
    (HeckeGeneral.Analysis.NonzeroIdeal F × HeckeGeneral.Analysis.NonzeroIdeal F) ×
      (Fin k → HeightOneSpectrum (𝓞 F)) → ℂ :=
  childCartesianCoefficient
    (fun I => (Real.sqrt N₁ : ℂ)⁻¹ * (sourcePlainCoefficient T.plain T.plainTwist T.mask I * w₁ I))
    (fun I => (Real.sqrt N₂ : ℂ)⁻¹ * (sourcePlainCoefficient T.plain T.plainTwist T.mask I * w₂ I))
    (fun i p => (Real.sqrt (Z ^ length i) : ℂ)⁻¹ *
      (sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask p * w i p))

theorem coefficient_eq_bare_mul_residue (T : FixedChildCharacters F k)
    (g h : A.R) (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (i : (HeckeGeneral.Analysis.NonzeroIdeal F × HeckeGeneral.Analysis.NonzeroIdeal F) ×
      (Fin k → HeightOneSpectrum (𝓞 F))) :
    T.coefficient (σ := σ) g h N₁ N₂ Z length w₁ w₂ w i =
      T.bareCoefficient N₁ N₂ Z length w₁ w₂ w i *
        actualIdealResidue (A := A) (σ := σ) (childIndexIdeal i) (g * h) := by
  simp only [coefficient, bareCoefficient, childCartesianCoefficient,
    sourcePlainTerm, sourcePrimeTerm, childIndexIdeal, actualIdealResidue_ideal_mul,
    actualIdealResidue_prod, Finset.prod_mul_distrib]
  ring

end FixedChildCharacters

def rawBareSourceCoefficient (T : FixedChildCharacters F k)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ) (i : AllocationColumn F k) : ℂ :=
  T.bareCoefficient N₁ N₂ Z length w₁ w₂ w
    ((sourceMomentIdeal i.1.1, sourceMomentIdeal i.1.2), i.2)

theorem raw_source_coefficient_eq_bare_mul_residue
    (T : FixedChildCharacters F k) (g h : A.R)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (i : AllocationColumn F k) (I : A.Exterior) (hI : I.val = allocationColumnIdeal i) :
    rawSourceCoefficient (σ := σ) T g h N₁ N₂ Z length w₁ w₂ w i =
      rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w i *
        σ (A.sexticResidue I (g * h)) := by
  have hleft : i.1.1 ≠ 0 := by
    intro hz
    apply I.property.1
    rw [hI, allocationColumnIdeal, hz, zero_mul, zero_mul]
  have hright : i.1.2 ≠ 0 := by
    intro hz
    apply I.property.1
    rw [hI, allocationColumnIdeal, hz, mul_zero, zero_mul]
  have he : childIndexIdeal ((sourceMomentIdeal i.1.1, sourceMomentIdeal i.1.2), i.2) = I.val := by
    simp only [childIndexIdeal, sourceMomentIdeal_val_of_ne_zero _ hleft,
      sourceMomentIdeal_val_of_ne_zero _ hright]
    exact hI.symm
  rw [rawSourceCoefficient, FixedChildCharacters.coefficient_eq_bare_mul_residue,
    he, actualIdealResidue_exterior] <;> rfl

section PrimitiveRecipe

variable {Ray : Type*} [CommGroup Ray]

/-- Three kinds of original single-factor dictionaries, with their exact
central normalizations and finite-ray phases.  The whole coefficient and
whole ray label are computed from these factors. -/
structure SecondCoefficientTermDictionary
    (T : FixedChildCharacters F k) (phase : Ray →* Circle)
    (S₁ S₂ : Finset (Ideal (𝓞 F)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 F))) where
  leftAtom : Ideal (𝓞 F) → ℂ
  rightAtom : Ideal (𝓞 F) → ℂ
  slotAtom : Fin k → HeightOneSpectrum (𝓞 F) → ℂ
  leftRay : Ideal (𝓞 F) → Ray
  rightRay : Ideal (𝓞 F) → Ray
  slotRay : Fin k → HeightOneSpectrum (𝓞 F) → Ray
  scale₁ : ℝ
  scale₂ : ℝ
  base : ℝ
  length : Fin k → ℝ
  leftWeight : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ
  rightWeight : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ
  slotWeight : Fin k → HeightOneSpectrum (𝓞 F) → ℂ
  plain₁ : ∀ I ∈ S₁, leftAtom I * (phase (leftRay I) : ℂ) =
    (Real.sqrt scale₁ : ℂ)⁻¹ *
      (sourcePlainCoefficient T.plain T.plainTwist T.mask (sourceMomentIdeal I) *
        leftWeight (sourceMomentIdeal I))
  plain₂ : ∀ I ∈ S₂, rightAtom I * (phase (rightRay I) : ℂ) =
    (Real.sqrt scale₂ : ℂ)⁻¹ *
      (sourcePlainCoefficient T.plain T.plainTwist T.mask (sourceMomentIdeal I) *
        rightWeight (sourceMomentIdeal I))
  prime : ∀ i, ∀ p ∈ S i, slotAtom i p * (phase (slotRay i p) : ℂ) =
    (Real.sqrt (base ^ length i) : ℂ)⁻¹ *
      (sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask p * slotWeight i p)

namespace SecondCoefficientTermDictionary

variable {T : FixedChildCharacters F k} {phase : Ray →* Circle}
variable {S₁ S₂ : Finset (Ideal (𝓞 F))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 F))}
variable (D : SecondCoefficientTermDictionary T phase S₁ S₂ S)

def coefficient : AllocationColumn F k → ℂ :=
  childCartesianCoefficient D.leftAtom D.rightAtom D.slotAtom

def ray (i : AllocationColumn F k) : Ray :=
  D.leftRay i.1.1 * D.rightRay i.1.2 * ∏ j, D.slotRay j (i.2 j)

theorem coefficient_phase (i : AllocationColumn F k)
    (hi : i ∈ childCartesianColumns S₁ S₂ S) :
    D.coefficient i * (phase (D.ray i) : ℂ) =
      rawBareSourceCoefficient T D.scale₁ D.scale₂ D.base D.length
        D.leftWeight D.rightWeight D.slotWeight i := by
  have hm := hi
  simp only [childCartesianColumns, Finset.product_eq_sprod, Finset.mem_product,
    Fintype.mem_piFinset] at hm
  let complexPhase : Ray →* ℂ := Circle.coeHom.comp phase
  have hphase : (phase (D.ray i) : ℂ) =
      (phase (D.leftRay i.1.1) : ℂ) * (phase (D.rightRay i.1.2) : ℂ) *
        ∏ j, (phase (D.slotRay j (i.2 j)) : ℂ) := by
    change complexPhase (D.leftRay i.1.1 * D.rightRay i.1.2 * ∏ j, D.slotRay j (i.2 j)) = _
    simp only [map_mul, map_prod] <;> rfl
  rw [hphase]
  calc
    _ = (D.leftAtom i.1.1 * (phase (D.leftRay i.1.1) : ℂ)) *
        (D.rightAtom i.1.2 * (phase (D.rightRay i.1.2) : ℂ)) *
          ∏ j, D.slotAtom j (i.2 j) * (phase (D.slotRay j (i.2 j)) : ℂ) := by
      simp only [coefficient, childCartesianCoefficient, Finset.prod_mul_distrib]
      ring
    _ = _ := by
      rw [D.plain₁ _ hm.1.1, D.plain₂ _ hm.1.2]
      unfold rawBareSourceCoefficient FixedChildCharacters.bareCoefficient
        childCartesianCoefficient
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      exact D.prime j (i.2 j) (hm.2 j)

/-- The entire actual sextic value is distributed internally; no
primitive/unit-frequency assumption is inserted. -/
theorem coefficient_residue (i : AllocationColumn F k)
    (hi : i ∈ childCartesianColumns S₁ S₂ S)
    (I : A.Exterior) (hI : I.val = allocationColumnIdeal i)
    (frequency g h : A.R) (hfrequency : frequency = g * h) :
    D.coefficient i * (phase (D.ray i) : ℂ) * σ (A.sexticResidue I frequency) =
      rawSourceCoefficient (σ := σ) T g h D.scale₁ D.scale₂ D.base D.length
        D.leftWeight D.rightWeight D.slotWeight i := by
  rw [D.coefficient_phase i hi, hfrequency,
    raw_source_coefficient_eq_bare_mul_residue T g h D.scale₁ D.scale₂ D.base D.length
      D.leftWeight D.rightWeight D.slotWeight i I hI]

/-- The additional Gauss normalizers belong to the original factors.
Their product is distinct from the central factors already present in
`rawSourceCoefficient`. -/
def centralNormalizer (u v : ℂ) (t : Fin k → ℂ) : ℂ := u * v * ∏ j, t j

def normalizedCoefficient (u v : ℂ) (t : Fin k → ℂ) : AllocationColumn F k → ℂ :=
  childCartesianCoefficient (fun I => u * D.leftAtom I)
    (fun I => v * D.rightAtom I) (fun j p => t j * D.slotAtom j p)

theorem normalizedCoefficient_eq (u v : ℂ) (t : Fin k → ℂ)
    (i : AllocationColumn F k) :
    D.normalizedCoefficient u v t i = centralNormalizer u v t * D.coefficient i := by
  simp only [normalizedCoefficient, coefficient, centralNormalizer,
    childCartesianCoefficient, Finset.prod_mul_distrib]
  ring

/-- Extra Gauss normalization is retained exactly once; the child
coefficient on the right still has all its own central factors. -/
theorem normalized_coefficient_residue (u v : ℂ) (t : Fin k → ℂ)
    (i : AllocationColumn F k) (hi : i ∈ childCartesianColumns S₁ S₂ S)
    (I : A.Exterior) (hI : I.val = allocationColumnIdeal i)
    (frequency g h : A.R) (hfrequency : frequency = g * h) :
    D.normalizedCoefficient u v t i * (phase (D.ray i) : ℂ) *
        σ (A.sexticResidue I frequency) =
      centralNormalizer u v t * rawSourceCoefficient (σ := σ) T g h
        D.scale₁ D.scale₂ D.base D.length D.leftWeight D.rightWeight D.slotWeight i := by
  rw [D.normalizedCoefficient_eq,
    ← D.coefficient_residue i hi I hI frequency g h hfrequency]
  ring

end SecondCoefficientTermDictionary
end PrimitiveRecipe

section ActualSides

variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
variable {T : FixedChildCharacters F k}
variable {S₁ S₂ : Finset (Ideal (𝓞 F))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 F))}
variable {H : Type*}

theorem second_allocated_left_coefficient_from_terms
    (χ : (Ray × Ray) →* Circle)
    (D : SecondCoefficientTermDictionary T (fixedLeftPhase Ray χ) S₁ S₂ S)
    (IA : AllocationColumn F k → A.Exterior)
    (hIA : ∀ i ∈ childCartesianColumns S₁ S₂ S, (IA i).val = allocationColumnIdeal i)
    (frequency g h : H → A.R) (hfrequency : ∀ r, frequency r = g r * h r)
    (r : H)
    (i : AllocationColumn F k) (hi : i ∈ childCartesianColumns S₁ S₂ S) :
    secondAllocatedLeftCoefficient (σ := σ) Ray IA frequency D.ray χ D.coefficient r i =
      rawSourceCoefficient (σ := σ) T (g r) (h r) D.scale₁ D.scale₂ D.base D.length
        D.leftWeight D.rightWeight D.slotWeight i :=
  D.coefficient_residue i hi (IA i) (hIA i hi) (frequency r) (g r) (h r) (hfrequency r)

theorem second_allocated_right_coefficient_from_terms
    (χ : (Ray × Ray) →* Circle)
    (D : SecondCoefficientTermDictionary T (fixedRightPhase Ray χ) S₁ S₂ S)
    (IB : AllocationColumn F k → A.Exterior)
    (hIB : ∀ i ∈ childCartesianColumns S₁ S₂ S, (IB i).val = allocationColumnIdeal i)
    (frequency g h : H → A.R) (hfrequency : ∀ r, frequency r = g r * h r)
    (r : H)
    (i : AllocationColumn F k) (hi : i ∈ childCartesianColumns S₁ S₂ S) :
    secondAllocatedRightCoefficient (σ := σ) Ray IB frequency D.ray χ D.coefficient r i =
      star (rawSourceCoefficient (σ := σ) T (-g r) (h r) D.scale₁ D.scale₂ D.base D.length
        D.leftWeight D.rightWeight D.slotWeight i) := by
  apply congrArg star
  exact D.coefficient_residue i hi (IB i) (hIB i hi) (-frequency r) (-g r) (h r)
    (by rw [hfrequency r, neg_mul])

end ActualSides

namespace ActualChildRow

def negative {Ih : A.Exterior} {h g : A.R} {Q : ℝ}
    (r : ActualChildRow Ih h g Q) : ActualChildRow Ih (-h) (-g) Q where
  ideal := r.ideal
  element := r.element
  generates := r.generates
  frequency := by rw [r.frequency, neg_mul]
  norm_factor := r.norm_factor

end ActualChildRow

section Conjugation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A constant extra column normalization moves outside the energy.
This identity does not remove or reuse any child central normalization. -/
theorem joint_energy_constant_coefficient {H ι : Type*}
    (rows : Finset H) (columns : Finset ι) (q : H → ℂ)
    (c : H → ι → ℂ) (x : H → ι → V) (u : ℂ) (ξ : V) :
    jointColumnEnergy rows columns q (fun h i => u * c h i) x ξ =
      ‖u‖ ^ 2 * jointColumnEnergy rows columns q c x ξ := by
  have hcolumn (h : H) : jointFourierColumn columns (fun i => u * c h i) (x h) ξ =
      u * jointFourierColumn columns (c h) (x h) ξ := by
    simp only [jointFourierColumn, Finset.mul_sum, mul_assoc]
  simp only [jointColumnEnergy, hcolumn, norm_mul, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- Right-column conjugation is removed only after summing the complete
column, including an entire centered difference if present. -/
theorem joint_energy_star_neg_locations {H ι : Type*}
    (rows : Finset H) (columns : Finset ι) (q : H → ℂ)
    (c : H → ι → ℂ) (x : H → ι → V) (ξ : V) :
    jointColumnEnergy rows columns q (fun h i => star (c h i)) x ξ =
      jointColumnEnergy rows columns q c (fun h i => -x h i) ξ := by
  have hphase (x : V) : jointPhase ξ (-x) = star (jointPhase ξ x) := by
    simp only [jointPhase, inner_neg_right, AddChar.map_neg_eq_inv,
      Circle.coe_inv_eq_conj, starRingEnd_apply]
  have hcolumn (h : H) : jointFourierColumn columns (fun i => star (c h i)) (x h) ξ =
      star (jointFourierColumn columns (c h) (fun i => -x h i) ξ) := by
    simp only [jointFourierColumn, star_sum, star_mul', hphase, star_star]
  simp only [jointColumnEnergy, hcolumn, norm_star]

theorem rawSourceLocation_neg
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : Fin k → HeightOneSpectrum (𝓞 F) → V) (i : AllocationColumn F k) :
    rawSourceLocation (fun I => -x₁ I) (fun I => -x₂ I) (fun j p => -x j p) i =
      -rawSourceLocation x₁ x₂ x i := by
  simp only [rawSourceLocation, childCartesianLocation, Finset.sum_neg_distrib, neg_add]

end Conjugation
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.second_allocated_left_coefficient_from_terms
#print axioms HeckeSkeleton.Moments.EngineStep.second_allocated_right_coefficient_from_terms
#print axioms HeckeSkeleton.Moments.EngineStep.joint_energy_star_neg_locations
