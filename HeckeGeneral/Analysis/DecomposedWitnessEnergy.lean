import HeckeGeneral.Analysis.DecomposedWitnessMomentData

/-!
Finite energy transport on a fixed sixth-unit sector, indexed by complete
exterior ideals. Every summand is an actual zero-extended sextic finite sum.
The row cutoff is assumed for the actual orbit norm and then proved to give
membership in the exhaustive MomentData rows. The paired consumer retains
an explicit nonprincipal-row-character condition; theta is {1} here.

Slots use the EMPTY ray filter. A nonempty ray indicator cannot be erased
from a prime sum by a pointwise norm bound: it may remove cancellation.
Its finite-character expansion is proved separately in RayMomentSelectedExpansion.
No detector existence, admissibility or moment estimate is asserted.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.Analysis.ActualSIntegerMoments HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)

/-- The genuine orbit subset represented by a finite complete-ideal list
in one sector. No orbit is counted twice. -/
def fixedSectorWitnessOrbits (ξ : SixthUnitClasses K S)
    (C : Finset (ExteriorIdeal K S)) : Finset (ActualSIntegerOrbit K S) :=
  C.image (fun I => decomposedIdealSectorOrbit K S P (I, ξ))

theorem fixedSectorWitnessOrbits_card (ξ : SixthUnitClasses K S)
    (C : Finset (ExteriorIdeal K S)) :
    (fixedSectorWitnessOrbits K S P ξ C).card = C.card := by
  apply Finset.card_image_of_injective
  intro I J h
  exact congrArg Prod.fst (decomposedIdealSectorOrbit_injective K S P h)

theorem sum_fixedSectorWitnessOrbits (ξ : SixthUnitClasses K S)
    (C : Finset (ExteriorIdeal K S)) (f : ActualSIntegerOrbit K S → ℝ) :
    (∑ q ∈ fixedSectorWitnessOrbits K S P ξ C, f q) =
      ∑ I ∈ C, f (decomposedIdealSectorOrbit K S P (I, ξ)) := by
  unfold fixedSectorWitnessOrbits
  apply Finset.sum_image
  intro I _hI J _hJ h
  exact congrArg Prod.fst (decomposedIdealSectorOrbit_injective K S P h)

/-- The original inverse finite sum for an actual complete-ideal orbit. -/
def actualWitnessInversePolynomial (η : HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (V : IdealTest K) (I : ExteriorIdeal K S) (D t : ℝ) : ℂ :=
  sIntegerSexticInverseIdealPolynomial K S P.arithmetic.root6
    P.arithmetic.primitive6 P.arithmetic.embedding η (V.support I.val t D)
    (decomposedIdealSectorOrbit K S P (I, ξ)).out.val D (V.profile I.val t)

theorem slotProduct_decomposedWitness_restrictSlots_actual
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (V W₁ W₂ : IdealTest K) (g : SlotGeometry K)
    (J : Finset (Fin g.slotCount)) (I : ExteriorIdeal K S) (Z t : ℝ) :
    slotProduct
      ((decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g).restrictSlots J)
      I.val Z t =
      ∏ i ∈ J, actualDecomposedPrimePolynomial K S P ξ g ∅ i I Z t := by
  calc
    _ = ∏ i ∈ J,
        primePolynomial (decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g)
          i I.val Z t :=
      slotProduct_restrictSlots
        (decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g) J I.val Z t
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _hi
      change primePolynomial (decomposedMomentDataWithSlots K S P R ω η ξ V g)
        i I.val Z t = _
      exact (rayMaskedPrimePolynomial_empty K
        (decomposedMomentDataWithSlots K S P R ω η ξ V g) i I.val Z t).symm.trans
          (rayMaskedPrimePolynomial_decomposed K S P R ω η ξ V g ∅ i I Z t)

private theorem sum_exteriorIdeal_subset_le (C : Finset (ExteriorIdeal K S))
    (F : Finset (NonzeroIdeal K)) (f : NonzeroIdeal K → ℝ)
    (hC : ∀ I ∈ C, I.val ∈ F) (hf : ∀ I, 0 ≤ f I) :
    (∑ I ∈ C, f I.val) ≤ ∑ I ∈ F, f I := by
  have hinj : ∀ I ∈ C, ∀ J ∈ C,
      (I : ExteriorIdeal K S).val = J.val → I = J :=
    fun _ _ _ _ h => Subtype.ext h
  rw [← Finset.sum_image hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro I hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact hC J hJ
  · intro I _hI _hnot
    exact hf I

theorem actualWitness_inverseEnergy_le
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (V W₁ W₂ : IdealTest K) (g : SlotGeometry K)
    (J : Finset (Fin g.slotCount)) (a : RealParameters) (Z t : ℝ)
    (C : Finset (ExteriorIdeal K S))
    (hC : ∀ I ∈ C,
      actualSIntegerOrbitNorm K S (decomposedIdealSectorOrbit K S P (I, ξ)) ≤ Z ^ a.m) :
    (∑ I ∈ C,
      ‖actualWitnessInversePolynomial K S P η ξ V I (Z ^ a.r) t *
        ∏ i ∈ J, actualDecomposedPrimePolynomial K S P ξ g ∅ i I Z t‖ ^ 2) ≤
      inverseEnergy
        ((decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g).restrictSlots J) a Z t := by
  let d := (decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g).restrictSlots J
  have hmem : ∀ I ∈ C, I.val ∈ d.rows (Z ^ a.m) := by
    intro I hI
    change I.val ∈ completeExteriorIdealRows K S (Z ^ a.m)
    apply (mem_completeExteriorIdealRows K S (Z ^ a.m) I.val).mpr
    refine ⟨I.property, ?_⟩
    simpa only [decomposedIdealSectorOrbit_norm] using hC I hI
  calc
    _ = ∑ I ∈ C,
        ‖inversePolynomial d I.val (Z ^ a.r) t * slotProduct d I.val Z t‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro I _hI
      change _ = ‖inversePolynomial
        ((decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g).restrictSlots J)
        I.val (Z ^ a.r) t * slotProduct
        ((decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g).restrictSlots J) I.val Z t‖ ^ 2
      rw [inversePolynomial_decomposedWitnessMomentData_restrictSlots,
        slotProduct_decomposedWitness_restrictSlots_actual]
      rfl
    _ ≤ ∑ u ∈ d.rows (Z ^ a.m),
        ‖inversePolynomial d u (Z ^ a.r) t * slotProduct d u Z t‖ ^ 2 :=
      sum_exteriorIdeal_subset_le K S C (d.rows (Z ^ a.m))
        (fun u => ‖inversePolynomial d u (Z ^ a.r) t * slotProduct d u Z t‖ ^ 2)
        hmem (fun _ => sq_nonneg _)
    _ = _ := rfl

theorem actualWitness_pairedEnergy_le
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (V W₁ W₂ : IdealTest K) (g : SlotGeometry K)
    (J : Finset (Fin g.slotCount)) (a : RealParameters) (Z t : ℝ)
    (C : Finset (ExteriorIdeal K S))
    (hC : ∀ I ∈ C,
      actualSIntegerOrbitNorm K S (decomposedIdealSectorOrbit K S P (I, ξ)) ≤ Z ^ (a.m + a.q))
    (hexcept : ∀ I ∈ C, R.character (decomposedFrequencyRow K S I ξ) ≠ 1) :
    (∑ I ∈ C,
      ‖actualDecomposedPlainPolynomial K S P ξ W₁ I (Z ^ a.n₁) t *
        actualDecomposedPlainPolynomial K S P ξ W₂ I (Z ^ a.n₂) t *
        ∏ i ∈ J, actualDecomposedPrimePolynomial K S P ξ g ∅ i I Z t‖ ^ 2) ≤
      pairedEnergy
        ((decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g).restrictSlots J) a Z t := by
  let d := (decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g).restrictSlots J
  have hmem : ∀ I ∈ C, I.val ∈ pairedRows d a Z := by
    intro I hI
    unfold pairedRows
    apply Finset.mem_filter.mpr
    constructor
    · change I.val ∈ completeExteriorIdealRows K S (Z ^ (a.m + a.q))
      apply (mem_completeExteriorIdealRows K S (Z ^ (a.m + a.q)) I.val).mpr
      refine ⟨I.property, ?_⟩
      simpa only [decomposedIdealSectorOrbit_norm] using hC I hI
    · change (if a.z = 0 then 1 * completeIdealRowCharacter K S P R ξ I.val ≠ 1
        else completeIdealRowCharacter K S P R ξ I.val ∉ ({1} : Finset (HeckeCharacter K)))
      rw [one_mul, completeIdealRowCharacter_exterior K S P R]
      by_cases hz : a.z = 0 <;> simp [hz, hexcept I hI]
  calc
    _ = ∑ I ∈ C,
        ‖plainPolynomial d d.plainTest₁ I.val (Z ^ a.n₁) t *
          plainPolynomial d d.plainTest₂ I.val (Z ^ a.n₂) t *
          slotProduct d I.val Z t‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro I _hI
      have h₁ := plainPolynomial_decomposedWitnessMomentData_restrictSlots K S P R
        ω η ξ V W₁ W₂ W₁ g J I (Z ^ a.n₁) t
      have h₂ := plainPolynomial_decomposedWitnessMomentData_restrictSlots K S P R
        ω η ξ V W₁ W₂ W₂ g J I (Z ^ a.n₂) t
      have hp := slotProduct_decomposedWitness_restrictSlots_actual K S P R
        ω η ξ V W₁ W₂ g J I Z t
      change plainPolynomial d d.plainTest₁ I.val (Z ^ a.n₁) t = _ at h₁
      change plainPolynomial d d.plainTest₂ I.val (Z ^ a.n₂) t = _ at h₂
      change slotProduct d I.val Z t = _ at hp
      rw [h₁, h₂, hp]
    _ ≤ ∑ u ∈ pairedRows d a Z,
        ‖plainPolynomial d d.plainTest₁ u (Z ^ a.n₁) t *
          plainPolynomial d d.plainTest₂ u (Z ^ a.n₂) t * slotProduct d u Z t‖ ^ 2 :=
      sum_exteriorIdeal_subset_le K S C (pairedRows d a Z)
        (fun u => ‖plainPolynomial d d.plainTest₁ u (Z ^ a.n₁) t *
          plainPolynomial d d.plainTest₂ u (Z ^ a.n₂) t * slotProduct d u Z t‖ ^ 2)
        hmem (fun _ => sq_nonneg _)
    _ = _ := rfl

end HeckeGeneral.ThetaSkeleton.Physical
