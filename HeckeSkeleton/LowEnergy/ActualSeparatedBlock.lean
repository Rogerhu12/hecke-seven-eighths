import HeckeSkeleton.LowEnergy.ActualHybridEntry
import HeckeSkeleton.LowEnergy.ActualFrozenCharges
import HeckeSkeleton.LowEnergy.ActualGeneratorClasses
import HeckeSkeleton.LowEnergy.ActualCommonMellinTail
import HeckeSkeleton.LowEnergy.MellinEnergy
import HeckeSkeleton.LowEnergy.FiniteHybridIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Literal finite reflected blocks with a common Mellin profile

Frozen, unit-sector and inactive-mark data are fixed before the moving row,
active marked ideal and the two dual columns.  The row--mark and mark--cube
conditions remain the two explicit hybrid masks.  The dual coefficient has
neither a row nor a marked-ideal argument.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.ActualSeparatedBlock

open NumberField IsDedekindDomain MeasureTheory
open HeckePort.CenteredMomentGenerator
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflection HeckeSkeleton.LowEnergy.ActualSymbolProducts
open HeckeSkeleton.LowEnergy.ActualFrozenCube HeckeSkeleton.LowEnergy.ActualFrozenMajorant
open HeckeSkeleton.LowEnergy.ActualFrozenIndependence
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualFrozenCharges HeckeSkeleton.LowEnergy.ActualHybridEntry
open HeckeSkeleton.LowEnergy.ActualSymbols HeckeSkeleton.LowEnergy.ActualGeneratorClasses
open HeckeSkeleton.LowEnergy.ClassSlices HeckeSkeleton.LowEnergy.ActualClassSlices
open scoped Classical BigOperators nonZeroDivisors NumberField

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

structure FixedData where
  frozen : ExteriorIdeal K S
  puncture : ExteriorIdeal K S
  puncture_squarefree : Squarefree puncture.val.val
  rowUnit : S.unit K
  inactive : Finset (ExteriorPrime K S)
  inactive_away : ∀ p ∈ inactive,
    ¬p.val.asIdeal ∣ frozen.val.val ∧ ¬p.val.asIdeal ∣ puncture.val.val

def baseDatum (f : FixedData K S) : MarkedDatum K S where
  moving := primeSetIdeal K S ∅
  frozen := f.frozen
  puncture := f.puncture
  moving_squarefree := by rw [emptyPrimeIdeal_val]; exact squarefree_one
  puncture_squarefree := f.puncture_squarefree
  moving_frozen_coprime := by rw [emptyPrimeIdeal_val]; exact isCoprime_one_left
  moving_puncture_coprime := by rw [emptyPrimeIdeal_val]; exact isCoprime_one_left
  rowUnit := f.rowUnit
  marks := ∅
  marks_coprime := by simp

structure RowAdmissible (f : FixedData K S) (k : ExteriorIdeal K S) : Prop where
  squarefree : Squarefree k.val.val
  frozen_coprime : IsCoprime k.val.val f.frozen.val.val
  puncture_coprime : IsCoprime k.val.val f.puncture.val.val
  inactive_away : ∀ p ∈ f.inactive, ¬p.val.asIdeal ∣ k.val.val

structure MarkAdmissible (f : FixedData K S) (P : ExteriorIdeal K S) : Prop where
  squarefree : Squarefree P.val.val
  prime_away : ∀ p ∈ exteriorSupport K S P,
    ¬p.val.asIdeal ∣ f.frozen.val.val ∧ ¬p.val.asIdeal ∣ f.puncture.val.val
  inactive_disjoint : Disjoint f.inactive (exteriorSupport K S P)

/-- Every admissible original row and marked ideal gives its actual datum.
The only two-variable row condition is the original coprimality mask. -/
def sourceDatum (f : FixedData K S) (k P : ExteriorIdeal K S)
    (hk : RowAdmissible K S f k) (hP : MarkAdmissible K S f P)
    (hkP : IsCoprime k.val.val P.val.val) : MarkedDatum K S where
  moving := k
  frozen := f.frozen
  puncture := f.puncture
  moving_squarefree := hk.squarefree
  puncture_squarefree := f.puncture_squarefree
  moving_frozen_coprime := hk.frozen_coprime
  moving_puncture_coprime := hk.puncture_coprime
  rowUnit := f.rowUnit
  marks := f.inactive ∪ exteriorSupport K S P
  marks_coprime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hi | ha
    · exact ⟨hk.inactive_away p hi, (f.inactive_away p hi).1, (f.inactive_away p hi).2⟩
    · refine ⟨?_, (hP.prime_away p ha).1, (hP.prime_away p ha).2⟩
      intro hpk
      exact p.val.prime.not_unit (hkP.isUnit_of_dvd' hpk
        ((mem_exteriorSupport_iff K S P p).mp ha))

def sourceCoordinates (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture) (k P : ExteriorIdeal K S)
    (hk : RowAdmissible K S f k) (hP : MarkAdmissible K S f P)
    (hkP : IsCoprime k.val.val P.val.val) (cb : FrozenColumn K S s)
    (hPb : IsCoprime P.val.val cb.val.2.val.val) :
    ReflectionCoordinates K S (sourceDatum K S f k P hk hP hkP) where
  state := s
  marks := exteriorSupport K S P
  marks_subset := Finset.subset_union_right
  c := cb.val.1
  b := cb.val.2
  column := cb.property
  marked_coprime := by rw [primeSetIdeal_support K S P hP.squarefree]; exact hPb

def sourceIndex (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture) (k P : ExteriorIdeal K S)
    (hk : RowAdmissible K S f k) (hP : MarkAdmissible K S f P)
    (hkP : IsCoprime k.val.val P.val.val) (cb : FrozenColumn K S s)
    (hPb : IsCoprime P.val.val cb.val.2.val.val) :
    ReflectionIndex K S (sourceDatum K S f k P hk hP hkP) :=
  fromCoordinates K S _ (sourceCoordinates K S f s k P hk hP hkP cb hPb)

variable (D : ThetaArithmeticData K S)

def frozenClass (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture) :
    SixthLocalClasses K S :=
  unitLocalClass K S (Quotient.out s.unitSector) * generatorLocalClass K S D s.minimum *
    generatorLocalClass K S D (primeSetIdeal K S s.active) ^ (-2 : ℤ)

def markCoefficient (θ : HeckeCharacter K) (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture) (P : ExteriorIdeal K S) : ℂ :=
  separatedMarkCoefficient K S D θ f.rowUnit f.frozen s.minimum s.active
    (exteriorSupport K S P) (Quotient.out s.unitSector)

def rowCoefficient (θ : HeckeCharacter K) (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture) (k : ExteriorIdeal K S) : ℂ :=
  separatedRowCoefficient K S D θ f.rowUnit f.frozen s.minimum s.active
    (Quotient.out s.unitSector) k

def columnCoefficient (θ : HeckeCharacter K) (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture) (c b : ExteriorIdeal K S) : ℂ :=
  extendColumn K S s (commonDualCoefficient K S D θ (baseDatum K S f) s) c b

def inactiveWeight (f : FixedData K S) : ℂ :=
  ∏ p ∈ f.inactive, (p.val.asIdeal.absNorm : ℂ)⁻¹

variable (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
variable (k P : ExteriorIdeal K S)
variable (hk : RowAdmissible K S f k) (hP : MarkAdmissible K S f P)
variable (hkP : IsCoprime k.val.val P.val.val) (cb : FrozenColumn K S s)
variable (hPb : IsCoprime P.val.val cb.val.2.val.val)

theorem source_inactive :
    (sourceDatum K S f k P hk hP hkP).marks \
        (sourceIndex K S f s k P hk hP hkP cb hPb).activeMarks = f.inactive := by
  change (f.inactive ∪ exteriorSupport K S P) \ exteriorSupport K S P = f.inactive
  rw [Finset.union_sdiff_distrib, Finset.sdiff_self, Finset.union_empty]
  exact hP.inactive_disjoint.sdiff_eq_left

theorem source_allmarks_norm :
    exteriorNorm K S (primeSetIdeal K S (sourceDatum K S f k P hk hP hkP).marks) =
      exteriorNorm K S (primeSetIdeal K S f.inactive) * exteriorNorm K S P := by
  change exteriorNorm K S (primeSetIdeal K S (f.inactive ∪ exteriorSupport K S P)) = _
  rw [primeSetIdeal_norm, Finset.prod_union hP.inactive_disjoint,
    ← primeSetIdeal_norm, ← primeSetIdeal_norm, primeSetIdeal_support K S P hP.squarefree]

theorem source_minimum :
    numeratorMinimum K S _ (sourceIndex K S f s k P hk hP hkP cb hPb) = s.minimum :=
  minimum_fromCoordinates K S _ _

theorem source_fullCube :
    fullCubeIdeal K S _ (sourceIndex K S f s k P hk hP hkP cb hPb) = cb.val.2 :=
  congrArg ReflectionCoordinates.b (to_fromCoordinates K S _
    (sourceCoordinates K S f s k P hk hP hkP cb hPb))

theorem source_markedIdeal :
    activeMarkedIdeal K S _ (sourceIndex K S f s k P hk hP hkP cb hPb) = P :=
  primeSetIdeal_support K S P hP.squarefree

theorem source_coefficient (θ : HeckeCharacter K) :
    fullCubeCoefficient K S D _ (sourceIndex K S f s k P hk hP hkP cb hPb) θ =
      commonDualCoefficient K S D θ (baseDatum K S f) s cb := by
  rw [fullCubeCoefficient_fromCoordinates]
  rfl

theorem source_frequency (hD : AllowedGeneratorInput K S D) :
    frequencyClass K S D _ (sourceIndex K S f s k P hk hP hkP cb hPb) =
      blockFrequency (frozenClass K S D f s) (generatorLocalClass K S D k)
        (generatorLocalClass K S D P) (generatorLocalClass K S D cb.val.1)
        (generatorLocalClass K S D cb.val.2) := by
  have h := frequencyClass_full_cube K S D hD _
    (sourceIndex K S f s k P hk hP hkP cb hPb) s.minimum
    (supportedExterior K S s.active cb.val.2) (by rfl)
  rw [source_markedIdeal K S f s k P hk hP hkP cb hPb] at h
  change _ = blockFrequency (frozenClass K S D f s) (generatorLocalClass K S D k)
    (generatorLocalClass K S D P) (generatorLocalClass K S D cb.val.1)
    (generatorLocalClass K S D (exteriorMul K S (supportedExterior K S s.active cb.val.2)
      (awayExterior K S s.active cb.val.2))) at h
  rw [supported_away_exterior] at h
  exact h

/-- The physical scale has already canceled exactly one active-mark norm. -/
def physicalBase (Z : ℝ) : ℝ :=
  Z * exteriorNorm K S (primeSetIdeal K S f.inactive) * exteriorNorm K S s.minimum /
    exteriorNorm K S (primeSetIdeal K S s.active) ^ 2

/-- The literal reflected term, with actual source datum and original
physical marked scale, is the common-coefficient hybrid atom. -/
theorem source_reflectedTerm (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ) (Z : ℝ) :
    reflectedTerm K S D (sourceDatum K S f k P hk hP hkP)
      (sourceIndex K S f s k P hk hP hkP cb hPb) F θ V
      (Z * exteriorNorm K S
        (primeSetIdeal K S (sourceDatum K S f k P hk hP hkP).marks)) =
    inactiveWeight K S f * rowCoefficient K S D θ f s k *
      hybridAtom K S D (markCoefficient K S D θ f s P)
        (commonDualCoefficient K S D θ (baseDatum K S f) s cb)
        k.val.val P.val.val cb.val.1.val.val cb.val.2.val.val *
      mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
        (blockFrequency (frozenClass K S D f s) (generatorLocalClass K S D k)
          (generatorLocalClass K S D P) (generatorLocalClass K S D cb.val.1)
          (generatorLocalClass K S D cb.val.2)) V 0
        (CommonMellin.physicalArgument (physicalBase K S f s Z)
          (exteriorNorm K S k) (exteriorNorm K S P)
          (exteriorNorm K S cb.val.1) (exteriorNorm K S cb.val.2)) := by
  rw [reflectedTerm_eq_hybridAtom K S D hD]
  rw [source_inactive K S f s k P hk hP hkP cb hPb,
    source_minimum K S f s k P hk hP hkP cb hPb,
    source_markedIdeal K S f s k P hk hP hkP cb hPb,
    source_fullCube K S f s k P hk hP hkP cb hPb,
    ← fullCubeCoefficient_frozenOnly,
    source_coefficient K S D f s k P hk hP hkP cb hPb θ,
    source_frequency K S D f s k P hk hP hkP cb hPb hD,
    source_allmarks_norm K S f k P hk hP hkP]
  have harg := CommonMellin.physical_argument_cancel_mark
    (X := Z * exteriorNorm K S (primeSetIdeal K S f.inactive))
    (A := exteriorNorm K S s.minimum) (F := exteriorNorm K S (primeSetIdeal K S s.active))
    (d := exteriorNorm K S k) (P := exteriorNorm K S P)
    (n := exteriorNorm K S cb.val.1) (b := exteriorNorm K S cb.val.2)
    (exteriorNorm_pos K S _) (exteriorNorm_pos K S _) (exteriorNorm_pos K S _)
  rw [← mul_assoc Z, harg]
  rfl

theorem unitPeriodValue_norm (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (u : S.unit K) (I : ExteriorIdeal K S) : ‖unitPeriodValue K S D θ u I‖ = 1 := by
  rw [unitPeriodValue, norm_mul, heckeIdealCoefficient_exterior_norm K S θ hθ I,
    idealSymbol_unit_norm, one_mul]

theorem markCoefficient_norm_le_one (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (P : ExteriorIdeal K S) : ‖markCoefficient K S D θ f s P‖ ≤ 1 := by
  unfold markCoefficient separatedMarkCoefficient
  apply mul_norm_le_one
  · apply mul_norm_le_one
    · rw [norm_pow, unitPeriodValue_norm K S D θ hθ, one_pow]
    · apply prod_norm_le_one
      intro p _
      apply mul_norm_le_one
      · exact (thetaGamma_exteriorPrime_two_norm K S D p).le
      · rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _)
          (prime_word_norm_le_one K S D p _ _ _ _ (-2) (-2))
  · apply prod_norm_le_one
    intro p _
    exact primeEvaluation_zpow_norm_le_one K S D p _ _

theorem rowCoefficient_norm_le_one (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (k : ExteriorIdeal K S) : ‖rowCoefficient K S D θ f s k‖ ≤ 1 := by
  unfold rowCoefficient separatedRowCoefficient
  apply mul_norm_le_one
  · apply mul_norm_le_one
    · rw [norm_pow, unitPeriodValue_norm K S D θ hθ, one_pow]
    · apply prod_norm_le_one
      intro p _
      apply mul_norm_le_one
      · rw [ActualLocalWeylTable.localWeylScalar_zero_norm]
        norm_num
      · exact prime_word_norm_le_one K S D p _ _ _ _ (-2) (-2)
  · apply prod_norm_le_one
    intro p _
    exact primeEvaluation_zpow_norm_le_one K S D p _ _

theorem columnCoefficient_norm_le (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (c b : ExteriorIdeal K S) :
    ‖columnCoefficient K S D θ f s c b‖ ≤ stateMajorant K S s /
      (Real.sqrt (exteriorNorm K S c) * exteriorNorm K S b) := by
  unfold columnCoefficient extendColumn
  split_ifs with h
  · exact commonDualCoefficient_norm_le K S D θ hθ (baseDatum K S f) s ⟨(c, b), h⟩
  · rw [norm_zero]
    exact div_nonneg (stateMajorant_nonneg K S s)
      (mul_nonneg (Real.sqrt_nonneg _) (exteriorNorm_pos K S b).le)

def slicedRow (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (k : ExteriorIdeal K S) : ℂ :=
  rowCoefficient K S D θ f s k * rowMask q (generatorLocalClass K S D k)

def slicedMark (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (P : ExteriorIdeal K S) : ℂ :=
  markCoefficient K S D θ f s P * markMask q (generatorLocalClass K S D P)

def slicedColumn (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (c b : ExteriorIdeal K S) : ℂ :=
  columnCoefficient K S D θ f s c b *
    columnMask q (generatorLocalClass K S D c) (generatorLocalClass K S D b)

theorem slicedRow_norm_le_one (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (q : FourClasses (SixthLocalClasses K S)) (k : ExteriorIdeal K S) :
    ‖slicedRow K S D f s θ q k‖ ≤ 1 :=
  mul_norm_le_one _ _ (rowCoefficient_norm_le_one K S D f s θ hθ k)
    (norm_rowMask_le_one _ _)

theorem slicedMark_norm_le_one (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (q : FourClasses (SixthLocalClasses K S)) (P : ExteriorIdeal K S) :
    ‖slicedMark K S D f s θ q P‖ ≤ 1 :=
  mul_norm_le_one _ _ (markCoefficient_norm_le_one K S D f s θ hθ P)
    (norm_markMask_le_one _ _)

theorem slicedColumn_norm_le (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (q : FourClasses (SixthLocalClasses K S)) (c b : ExteriorIdeal K S) :
    ‖slicedColumn K S D f s θ q c b‖ ≤ stateMajorant K S s /
      (Real.sqrt (exteriorNorm K S c) * exteriorNorm K S b) :=
  (norm_column_coefficient_le q _ _ _).trans (columnCoefficient_norm_le K S D f s θ hθ c b)

/-- Ordinary-ideal coefficient extensions preserve their allowed variables. -/
def ordinaryMark (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (P : Ideal (𝓞 K)) : ℂ :=
  if h : IsExterior K S P then slicedMark K S D f s θ q (toExterior K S P h) else 0

def ordinaryColumn (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (c b : Ideal (𝓞 K)) : ℂ :=
  if hc : IsExterior K S c then
    if hb : IsExterior K S b then
      slicedColumn K S D f s θ q (toExterior K S c hc) (toExterior K S b hb)
    else 0
  else 0

theorem ordinaryMark_norm_le_one (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (q : FourClasses (SixthLocalClasses K S)) (P : Ideal (𝓞 K)) :
    ‖ordinaryMark K S D f s θ q P‖ ≤ 1 := by
  unfold ordinaryMark
  split_ifs
  · exact slicedMark_norm_le_one K S D f s θ hθ q _
  · norm_num

theorem ordinaryColumn_norm_le (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (q : FourClasses (SixthLocalClasses K S)) (c b : Ideal (𝓞 K))
    (hc : IsExterior K S c) (hb : IsExterior K S b) :
    ‖ordinaryColumn K S D f s θ q c b‖ ≤ stateMajorant K S s /
      (Real.sqrt (c.absNorm : ℝ) * (b.absNorm : ℝ)) := by
  rw [ordinaryColumn, dif_pos hc, dif_pos hb]
  exact slicedColumn_norm_le K S D f s θ hθ q _ _

def ordinaryRow (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (k : Ideal (𝓞 K)) : ℂ :=
  if h : IsExterior K S k then slicedRow K S D f s θ q (toExterior K S k h) else 0

theorem ordinaryRow_norm_le_one (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (q : FourClasses (SixthLocalClasses K S)) (k : Ideal (𝓞 K)) :
    ‖ordinaryRow K S D f s θ q k‖ ≤ 1 := by
  unfold ordinaryRow
  split_ifs
  · exact slicedRow_norm_le_one K S D f s θ hθ q _
  · norm_num

/-- Only the unused zero ideal gets a harmless norm of one.  This makes
every mode a continuous function on all ordinary ideals. -/
def safeNorm {K : Type} [Field K] [NumberField K] (I : Ideal (𝓞 K)) : ℝ :=
  max 1 (I.absNorm : ℝ)

theorem safeNorm_pos (I : Ideal (𝓞 K)) : 0 < safeNorm (K := K) I :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem safeNorm_exterior (I : ExteriorIdeal K S) :
    safeNorm (K := K) I.val.val = exteriorNorm K S I := by
  apply max_eq_right
  have h : 1 ≤ I.val.val.absNorm := Ideal.absNorm_pos_of_nonZeroDivisors I.val
  exact_mod_cast h

def normalizedScale (Z Klo Plo Clo Blo : ℝ) : ℝ :=
  physicalBase K S f s Z * Clo * Blo ^ 3 / (Klo ^ 2 * Plo)

theorem normalizedScale_pos {Z Klo Plo Clo Blo : ℝ}
    (hZ : 0 < Z) (hK : 0 < Klo) (hP : 0 < Plo) (hC : 0 < Clo) (hB : 0 < Blo) :
    0 < normalizedScale K S f s Z Klo Plo Clo Blo := by
  have hI := exteriorNorm_pos K S (primeSetIdeal K S f.inactive)
  have hA := exteriorNorm_pos K S s.minimum
  have hF := exteriorNorm_pos K S (primeSetIdeal K S s.active)
  unfold normalizedScale physicalBase
  positivity

theorem argument_normalized (Z Klo Plo Clo Blo : ℝ) (k P c b : Ideal (𝓞 K))
    (hK : 0 < Klo) (hP : 0 < Plo) (hC : 0 < Clo) (hB : 0 < Blo) :
    CommonMellin.physicalArgument (physicalBase K S f s Z)
      (safeNorm k) (safeNorm P) (safeNorm c) (safeNorm b) =
    CommonMellin.physicalArgument (normalizedScale K S f s Z Klo Plo Clo Blo)
      (safeNorm k / Klo) (safeNorm P / Plo) (safeNorm c / Clo) (safeNorm b / Blo) := by
  have h := CommonMellin.physicalArgument_normalized
    (Y := physicalBase K S f s Z) (D := Klo) (L := Plo) (N := Clo) (B := Blo)
    (d := safeNorm k / Klo) (P := safeNorm P / Plo)
    (n := safeNorm c / Clo) (b := safeNorm b / Blo)
    hK hP (div_pos (safeNorm_pos K k) hK) (div_pos (safeNorm_pos K P) hP)
  have hmul (x y : ℝ) (hy : y ≠ 0) : y * (x / y) = x := by field_simp
  rw [hmul _ _ hK.ne', hmul _ _ hP.ne', hmul _ _ hC.ne', hmul _ _ hB.ne'] at h
  exact h

def modeRow (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (Y Klo t : ℝ) (k : Ideal (𝓞 K)) : ℂ :=
  ordinaryRow K S D f s θ q k * CommonMellinTail.rowFactor Y (safeNorm k / Klo) t

def modeMark (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (markWeight : Ideal (𝓞 K) → ℂ) (Y Plo t : ℝ) (P : Ideal (𝓞 K)) : ℂ :=
  markWeight P * ordinaryMark K S D f s θ q P *
    CommonMellinTail.markFactor Y (safeNorm P / Plo) t

def modeColumn (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (Y Clo Blo t : ℝ) (c b : Ideal (𝓞 K)) : ℂ :=
  ordinaryColumn K S D f s θ q c b *
    CommonMellinTail.columnFactor Y (safeNorm c / Clo) (safeNorm b / Blo) t

theorem continuous_vertical (Y : ℝ) : Continuous (CommonMellinTail.vertical Y) :=
  continuous_const.add (Complex.continuous_ofReal.mul_const _)

theorem continuous_rowFactor (Y x : ℝ) (hx : 0 < x) :
    Continuous (CommonMellinTail.rowFactor Y x) :=
  ((continuous_vertical Y).const_mul 2).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))

theorem continuous_markFactor (Y x : ℝ) (hx : 0 < x) :
    Continuous (CommonMellinTail.markFactor Y x) :=
  (continuous_vertical Y).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))

theorem continuous_columnFactor (Y n b : ℝ) (hn : 0 < n) (hb : 0 < b) :
    Continuous (CommonMellinTail.columnFactor Y n b) :=
  ((continuous_vertical Y).neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hn.ne'))).mul
    (((continuous_vertical Y).const_mul 3).neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne')))

theorem continuous_modeRow (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (Y Klo : ℝ) (hK : 0 < Klo) (k : Ideal (𝓞 K)) :
    Continuous (fun t => modeRow K S D f s θ q Y Klo t k) :=
  (continuous_rowFactor Y _ (div_pos (safeNorm_pos K k) hK)).const_mul _

theorem continuous_modeMark (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (markWeight : Ideal (𝓞 K) → ℂ) (Y Plo : ℝ) (hP : 0 < Plo) (P : Ideal (𝓞 K)) :
    Continuous (fun t => modeMark K S D f s θ q markWeight Y Plo t P) :=
  (continuous_markFactor Y _ (div_pos (safeNorm_pos K P) hP)).const_mul _

theorem continuous_modeColumn (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S))
    (Y Clo Blo : ℝ) (hC : 0 < Clo) (hB : 0 < Blo) (c b : Ideal (𝓞 K)) :
    Continuous (fun t => modeColumn K S D f s θ q Y Clo Blo t c b) :=
  (continuous_columnFactor Y _ _ (div_pos (safeNorm_pos K c) hC)
    (div_pos (safeNorm_pos K b) hB)).const_mul _

theorem modeRow_norm_le (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (q : FourClasses (SixthLocalClasses K S)) (Y Klo t : ℝ) (k : Ideal (𝓞 K))
    (hk0 : 1 ≤ safeNorm k / Klo) (hk1 : safeNorm k / Klo ≤ 2) :
    ‖modeRow K S D f s θ q Y Klo t k‖ ≤ 16 := by
  rw [modeRow, norm_mul]
  have h := mul_le_mul (ordinaryRow_norm_le_one K S D f s θ hθ q k)
    (CommonMellinTail.norm_rowFactor_le (Y := Y) hk0 hk1 t) (norm_nonneg _) zero_le_one
  simpa only [one_mul] using h

theorem modeMark_norm_le (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (q : FourClasses (SixthLocalClasses K S))
    (markWeight : Ideal (𝓞 K) → ℂ) (A Y Plo t : ℝ) (P : Ideal (𝓞 K))
    (hA : 0 ≤ A) (hw : ‖markWeight P‖ ≤ A)
    (hP0 : 1 ≤ safeNorm P / Plo) (hP1 : safeNorm P / Plo ≤ 2) :
    ‖modeMark K S D f s θ q markWeight Y Plo t P‖ ≤ 4 * A := by
  rw [modeMark, norm_mul, norm_mul]
  have hw' : ‖markWeight P‖ * ‖ordinaryMark K S D f s θ q P‖ ≤ A := by
    simpa only [mul_one] using mul_le_mul hw
      (ordinaryMark_norm_le_one K S D f s θ hθ q P) (norm_nonneg _) hA
  have h := mul_le_mul hw' (CommonMellinTail.norm_markFactor_le (Y := Y) hP0 hP1 t)
    (norm_nonneg _) hA
  simpa only [mul_comm A] using h

theorem modeColumn_norm_le (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (q : FourClasses (SixthLocalClasses K S)) (Y Clo Blo t : ℝ) (c b : Ideal (𝓞 K))
    (hc : IsExterior K S c) (hb : IsExterior K S b)
    (hc0 : 1 ≤ safeNorm c / Clo) (hc1 : safeNorm c / Clo ≤ 2)
    (hb0 : 1 ≤ safeNorm b / Blo) (hb1 : safeNorm b / Blo ≤ 2) :
    ‖modeColumn K S D f s θ q Y Clo Blo t c b‖ ≤
      4 * stateMajorant K S s / (Real.sqrt (c.absNorm : ℝ) * (b.absNorm : ℝ)) := by
  rw [modeColumn, norm_mul]
  have hC := ordinaryColumn_norm_le K S D f s θ hθ q c b hc hb
  have hnon : 0 ≤ stateMajorant K S s / (Real.sqrt (c.absNorm : ℝ) * (b.absNorm : ℝ)) :=
    div_nonneg (stateMajorant_nonneg K S s) (by positivity)
  have h := mul_le_mul hC
    (CommonMellinTail.norm_columnFactor_le (Y := Y) hc0 hc1 hb0 hb1 t)
    (norm_nonneg _) hnon
  convert h using 1 <;> ring

def slicedPhysicalBlock (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (markWeight : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (Z : ℝ)
    (ps cs bs : Finset (Ideal (𝓞 K))) (k : Ideal (𝓞 K)) : ℂ :=
  inactiveWeight K S f * ordinaryRow K S D f s θ q k *
    ∑ P ∈ ps, ∑ c ∈ cs, ∑ b ∈ bs,
      (markWeight P * ordinaryMark K S D f s θ q P) * ordinaryColumn K S D f s θ q c b *
      FiniteHybridIntegral.hybridKernel (cubicKernel K S D) (quadraticKernel K S D) k P c b *
      mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
        (blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2) V 0
        (CommonMellin.physicalArgument (physicalBase K S f s Z)
          (safeNorm k) (safeNorm P) (safeNorm c) (safeNorm b))

theorem slicedPhysicalBlock_zero_of_markWeight (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (ps cs bs : Finset (Ideal (𝓞 K))) (k : Ideal (𝓞 K))
    (ha : ∀ P ∈ ps, a P = 0) :
    slicedPhysicalBlock K S D f s F θ q a V Z ps cs bs k = 0 := by
  unfold slicedPhysicalBlock
  have hz : (∑ P ∈ ps, ∑ c ∈ cs, ∑ b ∈ bs,
      (a P * ordinaryMark K S D f s θ q P) * ordinaryColumn K S D f s θ q c b *
      FiniteHybridIntegral.hybridKernel (cubicKernel K S D) (quadraticKernel K S D) k P c b *
      mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
        (blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2) V 0
        (CommonMellin.physicalArgument (physicalBase K S f s Z)
          (safeNorm k) (safeNorm P) (safeNorm c) (safeNorm b))) = 0 := by
    apply Finset.sum_eq_zero
    intro P hP
    simp [ha P hP]
  rw [hz, mul_zero]

theorem slicedPhysicalBlock_zero_of_ordinaryRow (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (ps cs bs : Finset (Ideal (𝓞 K))) (k : Ideal (𝓞 K))
    (hk : ordinaryRow K S D f s θ q k = 0) :
    slicedPhysicalBlock K S D f s F θ q a V Z ps cs bs k = 0 := by
  simp [slicedPhysicalBlock, hk]

/-- The finite block identity is before squaring and retains the common
profile, the inactive scalar, all active marks, both columns and both masks. -/
theorem slicedPhysicalBlock_eq_integral [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (q : FourClasses (SixthLocalClasses K S)) (markWeight : Ideal (𝓞 K) → ℂ)
    (V : SmoothAnnularTest)
    (Z Klo Plo Clo Blo : ℝ)
    (hZ : 0 < Z) (hK : 0 < Klo) (hP : 0 < Plo) (hC : 0 < Clo) (hB : 0 < Blo)
    (ps cs bs : Finset (Ideal (𝓞 K))) (k : Ideal (𝓞 K))
    (hk0 : 1 ≤ safeNorm k / Klo) (hk1 : safeNorm k / Klo ≤ 2)
    (hp : ∀ P ∈ ps, 1 ≤ safeNorm P / Plo ∧ safeNorm P / Plo ≤ 2)
    (hc : ∀ c ∈ cs, 1 ≤ safeNorm c / Clo ∧ safeNorm c / Clo ≤ 2)
    (hb : ∀ b ∈ bs, 1 ≤ safeNorm b / Blo ∧ safeNorm b / Blo ≤ 2) :
    slicedPhysicalBlock K S D f s F θ q markWeight V.toFun Z ps cs bs k =
      inactiveWeight K S f * (CommonMellinTail.scalar (normalizedScale K S f s Z Klo Plo Clo Blo) : ℂ) *
      ∫ t : ℝ,
        ActualCommonMellinTail.profile F θ (QuotientGroup.mk f.rowUnit)
          (blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2)
          V (normalizedScale K S f s Z Klo Plo Clo Blo) t *
        (modeRow K S D f s θ q (normalizedScale K S f s Z Klo Plo Clo Blo) Klo t k *
          HeckeSkeleton.LowEnergy.IdealCanonicalColumns.hybridRow
            (cubicKernel K S D) (quadraticKernel K S D) ps cs bs
            (modeMark K S D f s θ q markWeight (normalizedScale K S f s Z Klo Plo Clo Blo) Plo t)
            (modeColumn K S D f s θ q (normalizedScale K S f s Z Klo Plo Clo Blo) Clo Blo t) k) := by
  let Y := normalizedScale K S f s Z Klo Plo Clo Blo
  let κ := blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2
  let rho := ActualCommonMellinTail.profile F θ (QuotientGroup.mk f.rowUnit) κ V Y
  have hY : 0 < Y := normalizedScale_pos K S f s hZ hK hP hC hB
  have hphase : Continuous (CommonMellinTail.phase Y) :=
    ((continuous_vertical Y).neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))).div_const _
  have hrho : Continuous rho :=
    (ActualCommonMellinTail.continuous_amplitude hF θ (QuotientGroup.mk f.rowUnit) κ V Y).mul hphase
  obtain ⟨C, hC0, hbound⟩ := ActualCommonMellinTail.profile_uniform_weighted_L1_of_finite hF θ 0
  have hint : Integrable (fun t => ‖rho t‖) := by
    simpa only [pow_zero, one_mul] using (hbound V (QuotientGroup.mk f.rowUnit) κ Y hY).1
  have heq := FiniteHybridIntegral.separated_kernel_sum_eq_hybrid_integral
    (cubicKernel K S D) (quadraticKernel K S D) ps cs bs
    (fun P => markWeight P * ordinaryMark K S D f s θ q P) (ordinaryColumn K S D f s θ q)
    rho (CommonMellinTail.rowFactor Y (safeNorm k / Klo))
    (fun t P => CommonMellinTail.markFactor Y (safeNorm P / Plo) t)
    (fun t c b => CommonMellinTail.columnFactor Y (safeNorm c / Clo) (safeNorm b / Blo) t)
    (fun P c b => mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit) κ V.toFun 0
      (CommonMellin.physicalArgument (physicalBase K S f s Z)
        (safeNorm k) (safeNorm P) (safeNorm c) (safeNorm b)))
    (CommonMellinTail.scalar Y : ℂ) k hrho hint
    (continuous_rowFactor Y _ (div_pos (safeNorm_pos K k) hK))
    (fun P => continuous_markFactor Y _ (div_pos (safeNorm_pos K P) hP))
    (fun c b => continuous_columnFactor Y _ _ (div_pos (safeNorm_pos K c) hC)
      (div_pos (safeNorm_pos K b) hB))
    16 (fun _ => 4) (fun _ _ => 4)
    (CommonMellinTail.norm_rowFactor_le hk0 hk1)
    (fun P hPm => CommonMellinTail.norm_markFactor_le (hp P hPm).1 (hp P hPm).2)
    (fun c hcm b hbm => CommonMellinTail.norm_columnFactor_le
      (hc c hcm).1 (hc c hcm).2 (hb b hbm).1 (hb b hbm).2)
    (by
      intro P hPm c hcm b hbm
      rw [argument_normalized K S f s Z Klo Plo Clo Blo k P c b hK hP hC hB]
      have hsep := ActualCommonMellinTail.kernel_physical_separation_at_zero θ hKernel
        (QuotientGroup.mk f.rowUnit) κ V hY
        (div_pos (safeNorm_pos K k) hK) (div_pos (safeNorm_pos K P) hP)
        (div_pos (safeNorm_pos K c) hC) (div_pos (safeNorm_pos K b) hB)
      convert hsep using 1
      congr 1
      congr 1
      funext t
      ring)
  unfold slicedPhysicalBlock
  rw [heq]
  repeat rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp only [rho, κ, Y, modeRow, modeMark, modeColumn]
  ring

#print axioms source_reflectedTerm
#print axioms modeRow_norm_le
#print axioms modeMark_norm_le
#print axioms modeColumn_norm_le
#print axioms slicedPhysicalBlock_eq_integral

end HeckeSkeleton.LowEnergy.ActualSeparatedBlock
