import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondAllocationLabels

/-!
# Original single factors bind every finite phase label

The original two plain factors, all prime factors, finite ray labels,
and extra Gauss normalizers are fixed before the divisor and phase sums.
Their identification with each phase dictionary is checked one factor
at a time.  The resulting whole allocated column identities are proved
here, including the complete centered prime factor and the right star.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum WholeAllocation

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {k l : ℕ}

/-- The literal original factors, including any complete centered
factor.  No Fourier variable or allocation label appears in this data. -/
structure SecondColumnFactors (F : Type) [Field F] [NumberField F]
    (Ray : Type*) (k : ℕ) where
  leftAtom : Ideal (𝓞 F) → ℂ
  rightAtom : Ideal (𝓞 F) → ℂ
  slotAtom : Fin k → HeightOneSpectrum (𝓞 F) → ℂ
  leftRay : Ideal (𝓞 F) → Ray
  rightRay : Ideal (𝓞 F) → Ray
  slotRay : Fin k → HeightOneSpectrum (𝓞 F) → Ray
  leftNormalizer : ℂ
  rightNormalizer : ℂ
  slotNormalizer : Fin k → ℂ

namespace SecondColumnFactors

variable (P : SecondColumnFactors F Ray k)

def coefficient : AllocationColumn F k → ℂ :=
  childCartesianCoefficient (fun I => P.leftNormalizer * P.leftAtom I)
    (fun I => P.rightNormalizer * P.rightAtom I)
    (fun i p => P.slotNormalizer i * P.slotAtom i p)

def ray (i : AllocationColumn F k) : Ray :=
  P.leftRay i.1.1 * P.rightRay i.1.2 * ∏ j, P.slotRay j (i.2 j)

def normalizer : ℂ :=
  SecondCoefficientTermDictionary.centralNormalizer
    P.leftNormalizer P.rightNormalizer P.slotNormalizer

end SecondColumnFactors

namespace SecondCoefficientTermDictionary

variable {T : FixedChildCharacters F k} {phase : Ray →* Circle}
variable {S₁ S₂ : Finset (Ideal (𝓞 F))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 F))}
variable (D : SecondCoefficientTermDictionary T phase S₁ S₂ S)
variable (P : SecondColumnFactors F Ray k)

/-- All six identities are single-factor data.  The original whole
coefficient, row energy and cost are not assumptions. -/
structure FactorIdentification : Prop where
  left_atom : ∀ I ∈ S₁, D.leftAtom I = P.leftAtom I
  right_atom : ∀ I ∈ S₂, D.rightAtom I = P.rightAtom I
  slot_atom : ∀ j, ∀ p ∈ S j, D.slotAtom j p = P.slotAtom j p
  left_ray : ∀ I ∈ S₁, D.leftRay I = P.leftRay I
  right_ray : ∀ I ∈ S₂, D.rightRay I = P.rightRay I
  slot_ray : ∀ j, ∀ p ∈ S j, D.slotRay j p = P.slotRay j p

namespace FactorIdentification

variable {D P} (h : D.FactorIdentification P)

include h in
theorem coefficient_eq (i : AllocationColumn F k)
    (hi : i ∈ childCartesianColumns S₁ S₂ S) :
    D.normalizedCoefficient P.leftNormalizer P.rightNormalizer P.slotNormalizer i =
      P.coefficient i := by
  have hm := hi
  simp only [childCartesianColumns, Finset.product_eq_sprod, Finset.mem_product,
    Fintype.mem_piFinset] at hm
  unfold normalizedCoefficient SecondColumnFactors.coefficient childCartesianCoefficient
  rw [h.left_atom _ hm.1.1, h.right_atom _ hm.1.2]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [h.slot_atom j _ (hm.2 j)]

include h in
theorem ray_eq (i : AllocationColumn F k)
    (hi : i ∈ childCartesianColumns S₁ S₂ S) : D.ray i = P.ray i := by
  have hm := hi
  simp only [childCartesianColumns, Finset.product_eq_sprod, Finset.mem_product,
    Fintype.mem_piFinset] at hm
  unfold SecondCoefficientTermDictionary.ray SecondColumnFactors.ray
  rw [h.left_ray _ hm.1.1, h.right_ray _ hm.1.2]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact h.slot_ray j _ (hm.2 j)

end FactorIdentification
end SecondCoefficientTermDictionary

variable {V H ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [Fintype ι] [DecidableEq ι]
variable {S₁ S₂ T₁ T₂ : Finset (Ideal (𝓞 F))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 F))}
variable {T : Fin l → Finset (HeightOneSpectrum (𝓞 F))}
variable {IB : AllocationColumn F l → A.Exterior}

private theorem identified_energy_congr {J : Type*}
    (rows : Finset H) (columns : Finset J) (q : H → ℂ)
    (c f : H → J → ℂ) (x : H → J → V) (ξ : V)
    (hc : ∀ h ∈ rows, ∀ i ∈ columns, c h i = f h i) :
    jointColumnEnergy rows columns q c x ξ = jointColumnEnergy rows columns q f x ξ := by
  unfold jointColumnEnergy
  apply Finset.sum_congr rfl
  intro h hh
  have he : jointFourierColumn columns (c h) (x h) ξ =
      jointFourierColumn columns (f h) (x h) ξ := by
    unfold jointFourierColumn
    apply Finset.sum_congr rfl
    intro i hi
    rw [hc h hh i hi]
  rw [he]

namespace SecondAllocationLabel

variable (z : SecondAllocationLabel Ray T₁ T₂ T IB k)

theorem leftColumns_subset : z.leftColumns S₁ S₂ S ⊆ childCartesianColumns S₁ S₂ S := by
  intro i hi
  rw [leftColumns, paired_allocated_columns_eq_filter] at hi
  exact (Finset.mem_filter.mp hi).1

theorem rightColumns_subset : z.rightColumns ⊆ childCartesianColumns T₁ T₂ T := by
  intro i hi
  rw [rightColumns, paired_allocated_columns_eq_filter] at hi
  exact (Finset.mem_filter.mp hi).1

/-- The same fixed original factors are used for every divisor and
finite phase.  The equality is derived only on the actual allocated
columns, using the individual atom and ray identities. -/
theorem pairEnergy_identified
    (R : ActualSecondCorrelationRows A σ H ι)
    (IA : AllocationColumn F k → A.Exterior)
    (PL : SecondColumnFactors F Ray k) (PR : SecondColumnFactors F Ray l)
    (leftCharacters : FixedChildCharacters F k) (rightCharacters : FixedChildCharacters F l)
    (DL : SecondCoefficientTermDictionary leftCharacters (fixedLeftPhase Ray z.2.1) S₁ S₂ S)
    (DR : SecondCoefficientTermDictionary rightCharacters (fixedRightPhase Ray z.2.1) T₁ T₂ T)
    (hL : DL.FactorIdentification PL) (hR : DR.FactorIdentification PR)
    (x : H → AllocationColumn F k → V) (y : H → AllocationColumn F l → V) (ξ : V) :
    z.pairEnergy (S₁ := S₁) (S₂ := S₂) (S := S)
      R IA PL.ray PR.ray PL.coefficient PR.coefficient x y ξ =
    z.pairEnergy (S₁ := S₁) (S₂ := S₂) (S := S) R IA DL.ray DR.ray
      (DL.normalizedCoefficient PL.leftNormalizer PL.rightNormalizer PL.slotNormalizer)
      (DR.normalizedCoefficient PR.leftNormalizer PR.rightNormalizer PR.slotNormalizer) x y ξ := by
  unfold pairEnergy
  apply congrArg₂ (fun a b : ℝ => Real.sqrt a * Real.sqrt b)
  · apply identified_energy_congr
    intro h _ i hi
    have hm := z.leftColumns_subset hi
    unfold secondAllocatedLeftCoefficient
    rw [hL.coefficient_eq i hm, hL.ray_eq i hm]
  · apply identified_energy_congr
    intro h _ i hi
    have hm := z.rightColumns_subset hi
    unfold secondAllocatedRightCoefficient
    rw [hR.coefficient_eq i hm, hR.ray_eq i hm]

end SecondAllocationLabel
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondAllocationLabel.pairEnergy_identified
