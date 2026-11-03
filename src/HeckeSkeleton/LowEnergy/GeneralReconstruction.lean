import HeckeSkeleton.LowEnergy.GeneralReflectedBlock
import HeckeSkeleton.LowEnergy.ActualSourceReindex
import HeckeSkeleton.Moments.MOM_BASE.ThetaBridge

/-!
# Exact reconstruction at an arbitrary completed scale

All active marks remain inside the row.  The only enlargement is zero
extension: the original row--mark mask, the canonical full-cube column
condition and the mark--cube mask are retained.  Four local classes are
expanded before any norm is taken.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralReconstruction

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualSymbols
open HeckeSkeleton.LowEnergy.ActualSourceReindex
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualHybridEntry
open HeckeSkeleton.LowEnergy.ClassSlices HeckeSkeleton.LowEnergy.ActualClassSlices
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)
variable (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)

theorem exterior_isExterior (I : ExteriorIdeal K S) : IsExterior K S I.val.val :=
  ⟨nonZeroDivisors.coe_ne_zero I.val, I.property⟩

theorem exterior_val_injective :
    Function.Injective (fun I : ExteriorIdeal K S => I.val.val) := by
  intro I J h
  exact Subtype.ext (Subtype.ext h)

theorem ordinaryRow_exterior (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (k : ExteriorIdeal K S) :
    ordinaryRow K S D f s θ q k.val.val =
      ActualSeparatedBlock.slicedRow K S D f s θ q k := by
  rw [ordinaryRow, dif_pos (exterior_isExterior K S k)]
  rfl

theorem ordinaryMark_exterior (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (P : ExteriorIdeal K S) :
    ordinaryMark K S D f s θ q P.val.val = slicedMark K S D f s θ q P := by
  rw [ordinaryMark, dif_pos (exterior_isExterior K S P)]
  rfl

theorem ordinaryColumn_exterior (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (c b : ExteriorIdeal K S) :
    ordinaryColumn K S D f s θ q c.val.val b.val.val =
      slicedColumn K S D f s θ q c b := by
  rw [ordinaryColumn, dif_pos (exterior_isExterior K S c),
    dif_pos (exterior_isExterior K S b)]
  rfl

/-- The original source term, extended by zero to the common two-column
rectangle.  Neither the column condition nor its coefficient depends on a
row or an active mark. -/
def literalTerm (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (markWeight : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (k P c b : ExteriorIdeal K S)
    (hk : RowAdmissible K S f k) (hP : MarkAdmissible K S f P) : ℂ :=
  if hkP : IsCoprime k.val.val P.val.val then
    if hcb : ColumnCondition K S s c b then
      if hPb : IsCoprime P.val.val b.val.val then
        markWeight P.val.val *
          reflectedTerm K S D (sourceDatum K S f k P hk hP hkP)
            (sourceIndex K S f s k P hk hP hkP ⟨(c, b), hcb⟩ hPb) F θ V
            X
      else 0
    else 0
  else 0

def generalAtom (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (markWeight : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (k P c b : ExteriorIdeal K S) : ℂ :=
  inactiveWeight K S f * rowCoefficient K S D θ f s k *
    hybridAtom K S D (markWeight P.val.val * markCoefficient K S D θ f s P)
      (columnCoefficient K S D θ f s c b) k.val.val P.val.val c.val.val b.val.val *
    mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
      (blockFrequency (frozenClass K S D f s) (generatorLocalClass K S D k)
        (generatorLocalClass K S D P) (generatorLocalClass K S D c)
        (generatorLocalClass K S D b)) V 0
      (CommonMellin.argument (GeneralReflectedBlock.baseScale K S f s X)
        (exteriorNorm K S k) (exteriorNorm K S P)
        (exteriorNorm K S c) (exteriorNorm K S b))

theorem generalAtom_zero_of_markWeight (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (k P c b : ExteriorIdeal K S) (hP : a P.val.val = 0) :
    generalAtom K S D f s F θ a V X k P c b = 0 := by
  simp [generalAtom, hP, hybridAtom]

theorem generalAtom_zero_of_rowCoefficient (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (k P c b : ExteriorIdeal K S) (hk : rowCoefficient K S D θ f s k = 0) :
    generalAtom K S D f s F θ a V X k P c b = 0 := by
  simp [generalAtom, hk]

theorem literalTerm_eq_generalAtom (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (markWeight : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (k P c b : ExteriorIdeal K S)
    (hk : RowAdmissible K S f k) (hP : MarkAdmissible K S f P) :
    literalTerm K S D f s F θ markWeight V X k P c b hk hP =
      generalAtom K S D f s F θ markWeight V X k P c b := by
  unfold literalTerm
  by_cases hkP : IsCoprime k.val.val P.val.val
  · rw [dif_pos hkP]
    by_cases hcb : ColumnCondition K S s c b
    · rw [dif_pos hcb]
      by_cases hPb : IsCoprime P.val.val b.val.val
      · rw [dif_pos hPb, GeneralReflectedBlock.source_reflectedTerm K S D f s k P hk hP hkP
          ⟨(c, b), hcb⟩ hPb hD]
        simp only [generalAtom, columnCoefficient, extendColumn, dif_pos hcb,
          hybridAtom, div_eq_mul_inv]
        ring
      · simp [hPb, generalAtom, hybridAtom]
    · simp [hcb, generalAtom, columnCoefficient, extendColumn, hybridAtom]
  · simp [hkP, generalAtom, hybridAtom]

def slicedAtom (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (markWeight : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (k P c b : Ideal (𝓞 K)) : ℂ :=
  inactiveWeight K S f * ordinaryRow K S D f s θ q k *
    ((markWeight P * ordinaryMark K S D f s θ q P) *
      ordinaryColumn K S D f s θ q c b *
      FiniteHybridIntegral.hybridKernel (cubicKernel K S D) (quadraticKernel K S D) k P c b *
      mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
        (blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2) V 0
        (CommonMellin.argument (GeneralReflectedBlock.baseScale K S f s X)
          (safeNorm k) (safeNorm P) (safeNorm c) (safeNorm b)))

/-- The exact expansion of one general reflected summand.  All class
indicators have a single allowed variable, or the joint column pair. -/
theorem generalAtom_eq_class_sum [Fintype (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (markWeight : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (k P c b : ExteriorIdeal K S) :
    generalAtom K S D f s F θ markWeight V X k P c b =
      ∑ q : FourClasses (SixthLocalClasses K S),
        slicedAtom K S D f s F θ q markWeight V X
          k.val.val P.val.val c.val.val b.val.val := by
  let H : SixthLocalClasses K S → SixthLocalClasses K S →
      SixthLocalClasses K S → SixthLocalClasses K S → ℂ := fun r m a x =>
    mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
      (blockFrequency (frozenClass K S D f s) r m a x) V 0
      (CommonMellin.argument (GeneralReflectedBlock.baseScale K S f s X)
        (exteriorNorm K S k) (exteriorNorm K S P)
        (exteriorNorm K S c) (exteriorNorm K S b))
  have he := class_expansion H (generatorLocalClass K S D k)
    (generatorLocalClass K S D P) (generatorLocalClass K S D c)
    (generatorLocalClass K S D b)
  unfold generalAtom
  change _ * H _ _ _ _ = _
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [slicedAtom, ordinaryRow_exterior K S D f s,
    ordinaryMark_exterior K S D f s, ordinaryColumn_exterior K S D f s,
    safeNorm_exterior K S k, safeNorm_exterior K S P,
    safeNorm_exterior K S c, safeNorm_exterior K S b]
  dsimp [H, ActualSeparatedBlock.slicedRow, slicedMark, slicedColumn,
    hybridAtom, FiniteHybridIntegral.hybridKernel, KeepOriginalRow.mask]
  simp only [div_eq_mul_inv]
  ring

def generalBlock (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (markWeight : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (ps cs bs : Finset (ExteriorIdeal K S)) (k : ExteriorIdeal K S) : ℂ :=
  ∑ P ∈ ps, ∑ c ∈ cs, ∑ b ∈ bs,
    generalAtom K S D f s F θ markWeight V X k P c b

theorem slicedBlock_eq_exterior_sum
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (markWeight : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (ps cs bs : Finset (ExteriorIdeal K S))
    (k : ExteriorIdeal K S) :
    GeneralReflectedBlock.slicedBlock K S D f s F θ q markWeight V X
      (ps.image (fun I => I.val.val)) (cs.image (fun I => I.val.val))
      (bs.image (fun I => I.val.val)) k.val.val =
      ∑ P ∈ ps, ∑ c ∈ cs, ∑ b ∈ bs,
        slicedAtom K S D f s F θ q markWeight V X
          k.val.val P.val.val c.val.val b.val.val := by
  unfold GeneralReflectedBlock.slicedBlock
  rw [Finset.sum_image (fun I _ J _ h => exterior_val_injective K S h)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.sum_image (fun I _ J _ h => exterior_val_injective K S h)]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_image (fun I _ J _ h => exterior_val_injective K S h)]
  rfl

/-- Finite active-mark and dual-column regrouping, before taking row norms. -/
theorem generalBlock_eq_class_sum [Fintype (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (markWeight : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (ps cs bs : Finset (ExteriorIdeal K S)) (k : ExteriorIdeal K S) :
    generalBlock K S D f s F θ markWeight V X ps cs bs k =
      ∑ q : FourClasses (SixthLocalClasses K S),
        GeneralReflectedBlock.slicedBlock K S D f s F θ q markWeight V X
          (ps.image (fun I => I.val.val)) (cs.image (fun I => I.val.val))
          (bs.image (fun I => I.val.val)) k.val.val := by
  simp only [generalBlock, generalAtom_eq_class_sum K S D f s,
    slicedBlock_eq_exterior_sum K S D f s]
  calc
    _ = ∑ P ∈ ps, ∑ c ∈ cs, ∑ q : FourClasses (SixthLocalClasses K S),
          ∑ b ∈ bs, slicedAtom K S D f s F θ q markWeight V X
            k.val.val P.val.val c.val.val b.val.val := by
      apply Finset.sum_congr rfl
      intro P _
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm
    _ = ∑ P ∈ ps, ∑ q : FourClasses (SixthLocalClasses K S),
          ∑ c ∈ cs, ∑ b ∈ bs, slicedAtom K S D f s F θ q markWeight V X
            k.val.val P.val.val c.val.val b.val.val := by
      apply Finset.sum_congr rfl
      intro P _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Specialization to the physical completed scale.  This equality is
proved before the active-mark sum: the general scale X equals
Z times the inactive norm times the active norm. -/
theorem generalAtom_eq_physicalAtom
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (markWeight : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (k P c b : ExteriorIdeal K S) :
    generalAtom K S D f s F θ markWeight V
      (Z * exteriorNorm K S (primeSetIdeal K S f.inactive) * exteriorNorm K S P)
      k P c b =
    ActualBlockReindex.physicalAtom K S D f s F θ markWeight V Z k P c b := by
  have ha := (exteriorNorm_pos K S (primeSetIdeal K S s.active)).ne'
  have hk := (exteriorNorm_pos K S k).ne'
  have hp := (exteriorNorm_pos K S P).ne'
  have harg : CommonMellin.argument
      (GeneralReflectedBlock.baseScale K S f s
        (Z * exteriorNorm K S (primeSetIdeal K S f.inactive) * exteriorNorm K S P))
      (exteriorNorm K S k) (exteriorNorm K S P)
      (exteriorNorm K S c) (exteriorNorm K S b) =
      CommonMellin.physicalArgument (physicalBase K S f s Z)
        (exteriorNorm K S k) (exteriorNorm K S P)
        (exteriorNorm K S c) (exteriorNorm K S b) := by
    unfold CommonMellin.argument CommonMellin.physicalArgument
      GeneralReflectedBlock.baseScale physicalBase
    field_simp [ha, hk, hp]
    <;> ring
  unfold generalAtom ActualBlockReindex.physicalAtom
  rw [harg]

variable {f s}

/-- The exact original sigma-indexed reflection summand is the block atom
for its actual inactive marks and full cube. -/
theorem reflectionSummand_eq_generalAtom (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (d : MarkedDatum K S) (s : FrozenState K S d.frozen d.puncture)
    (A : MarkChoice K S d) (cb : MarkedColumn K S s A.val)
    (V : ℝ → ℂ) (X : ℝ) :
    reflectedTerm K S D d ((reflectionSigmaEquiv K S d).symm ⟨s, A, cb⟩)
      F θ V X =
      generalAtom K S D (splitFixed K S d A) s F θ (fun _ => 1) V X
        d.moving (primeSetIdeal K S A.val) cb.val.val.1 cb.val.val.2 := by
  let f := splitFixed K S d A
  let hk := splitRow_admissible K S d A
  let hp := splitMark_admissible K S d A
  let hkp := split_row_mark_coprime K S d A
  let i := sourceIndex K S f s d.moving (primeSetIdeal K S A.val) hk hp hkp cb.val cb.property
  have hterm : reflectedTerm K S D
      (sourceDatum K S f d.moving (primeSetIdeal K S A.val) hk hp hkp) i F θ V
        X =
      reflectedTerm K S D d ((reflectionSigmaEquiv K S d).symm ⟨s, A, cb⟩)
        F θ V X := by
    apply reflectedTerm_congr K S D (split_sourceDatum K S d A)
    · change exteriorSupport K S (primeSetIdeal K S A.val) = A.val
      exact exteriorSupport_primeSetIdeal K S A.val
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  rw [← hterm]
  have h := literalTerm_eq_generalAtom K S D f s hD F θ (fun _ => 1) V X
    d.moving (primeSetIdeal K S A.val) cb.val.val.1 cb.val.val.2 hk hp
  unfold literalTerm at h
  erw [dif_pos hkp, dif_pos cb.val.property, dif_pos cb.property, one_mul] at h
  exact h

/-- The rectangular column coefficients inherit summability from the
supplied reflection after both exact zero extensions. -/
theorem extended_reflectionSummand_eq_generalAtom (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (d : MarkedDatum K S) (s : FrozenState K S d.frozen d.puncture)
    (A : MarkChoice K S d) (V : ℝ → ℂ) (X : ℝ)
    (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
    extendColumn K S s (extendMarkedColumn K S s A.val
      (fun z => reflectedTerm K S D d
        ((reflectionSigmaEquiv K S d).symm ⟨s, A, z⟩) F θ V
          X)) cb.1 cb.2 =
      generalAtom K S D (splitFixed K S d A) s F θ (fun _ => 1) V X
        d.moving (primeSetIdeal K S A.val) cb.1 cb.2 := by
  by_cases hcb : ColumnCondition K S s cb.1 cb.2
  · rw [extendColumn, dif_pos hcb]
    by_cases hPb : IsCoprime (primeSetIdeal K S A.val).val.val cb.2.val.val
    · rw [extendMarkedColumn, dif_pos hPb]
      exact reflectionSummand_eq_generalAtom K S D hD F θ d s A
        ⟨⟨cb, hcb⟩, hPb⟩ V X
    · simp [extendMarkedColumn, hPb, generalAtom, ActualHybridEntry.hybridAtom]
  · simp [extendColumn, hcb, generalAtom, columnCoefficient,
      ActualReflectionReindex.extendColumn, ActualHybridEntry.hybridAtom]
    intro _ hc
    exact (hcb hc).elim

/-- The supplied reflection is exactly the sum of the fixed-data atoms over
every frozen state, every active subset and the full common column pair.
The inactive set is the actual complement of that active subset. -/
theorem completedThetaSum_eq_general_atoms (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (d : MarkedDatum K S) (V : SmoothAnnularTest) (X : ℝ) (hZ : 0 < X) :
    completedThetaSum K S D θ (rowElement K S D d) d.puncture d.marks V.toFun
        X =
      ∑' s : FrozenState K S d.frozen d.puncture,
        ∑' A : MarkChoice K S d,
          ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
            generalAtom K S D (splitFixed K S d A) s F θ (fun _ => 1) V.toFun X
              d.moving (primeSetIdeal K S A.val) cb.1 cb.2 := by
  rw [completedThetaSum_reindexed K S D F θ hreflection d V X hZ]
  apply tsum_congr
  intro s
  apply tsum_congr
  intro A
  rw [tsum_extendColumn K S s]
  apply tsum_congr
  intro cb
  exact extended_reflectionSummand_eq_generalAtom K S D hD F θ d s A V.toFun X cb

 /-- Summability of the exact rectangular column expansion follows from the
 supplied reflected absolute convergence. -/
theorem generalAtom_columns_summable (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (d : MarkedDatum K S) (s : FrozenState K S d.frozen d.puncture)
    (A : MarkChoice K S d) (V : SmoothAnnularTest) (X : ℝ) (hZ : 0 < X) :
    Summable (fun cb : ExteriorIdeal K S × ExteriorIdeal K S =>
      generalAtom K S D (splitFixed K S d A) s F θ (fun _ => 1) V.toFun X
        d.moving (primeSetIdeal K S A.val) cb.1 cb.2) := by
  let g : MarkedColumn K S s A.val → ℂ := fun cb =>
    reflectedTerm K S D d ((reflectionSigmaEquiv K S d).symm ⟨s, A, cb⟩)
      F θ V.toFun X
  have hg : Summable g := original_column_summable K S D F θ hreflection d s A V X hZ
  have he := summable_extendColumn K S s (extendMarkedColumn K S s A.val g)
    (summable_extendMarkedColumn K S s A.val g hg)
  exact he.congr (fun cb =>
    extended_reflectionSummand_eq_generalAtom K S D hD F θ d s A V.toFun X cb)


open HeckeSkeleton.Moments.MOM_BASE in
/-- The canonical completed coefficient, including its whole-index mark,
is the exact reflected series at the same arbitrary completed scale. -/
theorem canonicalCompletedSum_eq_general_atoms
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (d : MarkedDatum K S) (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    canonicalCompletedSum (exteriorGamma K S D)
      (canonicalTau K S D θ (rowElement K S D d) d.puncture.val.val)
      (wholeMarkWeight K S d.marks) V.toFun X =
      ∑' s : FrozenState K S d.frozen d.puncture,
        ∑' A : MarkChoice K S d,
          ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
            generalAtom K S D (splitFixed K S d A) s F θ (fun _ => 1) V.toFun X
              d.moving (primeSetIdeal K S A.val) cb.1 cb.2 := by
  have h := canonicalCompletedSum_eq_weightedTheta K S D θ
    (rowElement K S D d) d.puncture d.marks (fun _ => 1) V.toFun X V.upper hX
    (fun y hy => (V.support hy).2)
  simp only [mul_one, weightedCompletedTheta_one] at h
  exact h.trans (completedThetaSum_eq_general_atoms K S D hD F θ hreflection d V X hX)

#print axioms literalTerm_eq_generalAtom
#print axioms generalAtom_eq_class_sum
#print axioms generalBlock_eq_class_sum
#print axioms generalAtom_eq_physicalAtom
#print axioms completedThetaSum_eq_general_atoms
#print axioms generalAtom_columns_summable
#print axioms canonicalCompletedSum_eq_general_atoms

end HeckeSkeleton.LowEnergy.GeneralReconstruction
