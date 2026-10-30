import HeckeSkeleton.LowEnergy.ActualSeparatedBlock

/-!
# Exact passage from literal reflected summands to finite ideal blocks

All active marks remain inside the row.  The only enlargement is zero
extension: the original row--mark mask, the canonical full-cube column
condition and the mark--cube mask are retained.  Four local classes are
expanded before any norm is taken.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualBlockReindex

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualSymbols
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
    (markWeight : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (k P c b : ExteriorIdeal K S)
    (hk : RowAdmissible K S f k) (hP : MarkAdmissible K S f P) : ℂ :=
  if hkP : IsCoprime k.val.val P.val.val then
    if hcb : ColumnCondition K S s c b then
      if hPb : IsCoprime P.val.val b.val.val then
        markWeight P.val.val *
          reflectedTerm K S D (sourceDatum K S f k P hk hP hkP)
            (sourceIndex K S f s k P hk hP hkP ⟨(c, b), hcb⟩ hPb) F θ V
            (Z * exteriorNorm K S
              (primeSetIdeal K S (sourceDatum K S f k P hk hP hkP).marks))
      else 0
    else 0
  else 0

def physicalAtom (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (markWeight : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (k P c b : ExteriorIdeal K S) : ℂ :=
  inactiveWeight K S f * rowCoefficient K S D θ f s k *
    hybridAtom K S D (markWeight P.val.val * markCoefficient K S D θ f s P)
      (columnCoefficient K S D θ f s c b) k.val.val P.val.val c.val.val b.val.val *
    mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
      (blockFrequency (frozenClass K S D f s) (generatorLocalClass K S D k)
        (generatorLocalClass K S D P) (generatorLocalClass K S D c)
        (generatorLocalClass K S D b)) V 0
      (CommonMellin.physicalArgument (physicalBase K S f s Z)
        (exteriorNorm K S k) (exteriorNorm K S P)
        (exteriorNorm K S c) (exteriorNorm K S b))

theorem physicalAtom_zero_of_markWeight (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (k P c b : ExteriorIdeal K S) (hP : a P.val.val = 0) :
    physicalAtom K S D f s F θ a V Z k P c b = 0 := by
  simp [physicalAtom, hP, hybridAtom]

theorem physicalAtom_zero_of_rowCoefficient (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (k P c b : ExteriorIdeal K S) (hk : rowCoefficient K S D θ f s k = 0) :
    physicalAtom K S D f s F θ a V Z k P c b = 0 := by
  simp [physicalAtom, hk]

theorem literalTerm_eq_physicalAtom (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (markWeight : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (k P c b : ExteriorIdeal K S)
    (hk : RowAdmissible K S f k) (hP : MarkAdmissible K S f P) :
    literalTerm K S D f s F θ markWeight V Z k P c b hk hP =
      physicalAtom K S D f s F θ markWeight V Z k P c b := by
  unfold literalTerm
  by_cases hkP : IsCoprime k.val.val P.val.val
  · rw [dif_pos hkP]
    by_cases hcb : ColumnCondition K S s c b
    · rw [dif_pos hcb]
      by_cases hPb : IsCoprime P.val.val b.val.val
      · rw [dif_pos hPb, source_reflectedTerm K S D f s k P hk hP hkP
          ⟨(c, b), hcb⟩ hPb hD]
        simp only [physicalAtom, columnCoefficient, extendColumn, dif_pos hcb,
          hybridAtom, div_eq_mul_inv]
        ring
      · simp [hPb, physicalAtom, hybridAtom]
    · simp [hcb, physicalAtom, columnCoefficient, extendColumn, hybridAtom]
  · simp [hkP, physicalAtom, hybridAtom]

def slicedAtom (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (markWeight : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (Z : ℝ) (k P c b : Ideal (𝓞 K)) : ℂ :=
  inactiveWeight K S f * ordinaryRow K S D f s θ q k *
    ((markWeight P * ordinaryMark K S D f s θ q P) *
      ordinaryColumn K S D f s θ q c b *
      FiniteHybridIntegral.hybridKernel (cubicKernel K S D) (quadraticKernel K S D) k P c b *
      mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
        (blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2) V 0
        (CommonMellin.physicalArgument (physicalBase K S f s Z)
          (safeNorm k) (safeNorm P) (safeNorm c) (safeNorm b)))

/-- The exact expansion of one physical reflected summand.  All class
indicators have a single allowed variable, or the joint column pair. -/
theorem physicalAtom_eq_class_sum [Fintype (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (markWeight : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (k P c b : ExteriorIdeal K S) :
    physicalAtom K S D f s F θ markWeight V Z k P c b =
      ∑ q : FourClasses (SixthLocalClasses K S),
        slicedAtom K S D f s F θ q markWeight V Z
          k.val.val P.val.val c.val.val b.val.val := by
  let H : SixthLocalClasses K S → SixthLocalClasses K S →
      SixthLocalClasses K S → SixthLocalClasses K S → ℂ := fun r m a x =>
    mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
      (blockFrequency (frozenClass K S D f s) r m a x) V 0
      (CommonMellin.physicalArgument (physicalBase K S f s Z)
        (exteriorNorm K S k) (exteriorNorm K S P)
        (exteriorNorm K S c) (exteriorNorm K S b))
  have he := class_expansion H (generatorLocalClass K S D k)
    (generatorLocalClass K S D P) (generatorLocalClass K S D c)
    (generatorLocalClass K S D b)
  unfold physicalAtom
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

def physicalBlock (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (markWeight : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (ps cs bs : Finset (ExteriorIdeal K S)) (k : ExteriorIdeal K S) : ℂ :=
  ∑ P ∈ ps, ∑ c ∈ cs, ∑ b ∈ bs,
    physicalAtom K S D f s F θ markWeight V Z k P c b

theorem slicedPhysicalBlock_eq_exterior_sum
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (markWeight : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (Z : ℝ) (ps cs bs : Finset (ExteriorIdeal K S))
    (k : ExteriorIdeal K S) :
    slicedPhysicalBlock K S D f s F θ q markWeight V Z
      (ps.image (fun I => I.val.val)) (cs.image (fun I => I.val.val))
      (bs.image (fun I => I.val.val)) k.val.val =
      ∑ P ∈ ps, ∑ c ∈ cs, ∑ b ∈ bs,
        slicedAtom K S D f s F θ q markWeight V Z
          k.val.val P.val.val c.val.val b.val.val := by
  unfold slicedPhysicalBlock
  rw [Finset.sum_image (fun I _ J _ h => exterior_val_injective K S h)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.sum_image (fun I _ J _ h => exterior_val_injective K S h)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_image (fun I _ J _ h => exterior_val_injective K S h)]
  simp only [Finset.mul_sum]
  rfl

/-- Finite active-mark and dual-column regrouping, before taking row norms. -/
theorem physicalBlock_eq_class_sum [Fintype (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (markWeight : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (ps cs bs : Finset (ExteriorIdeal K S)) (k : ExteriorIdeal K S) :
    physicalBlock K S D f s F θ markWeight V Z ps cs bs k =
      ∑ q : FourClasses (SixthLocalClasses K S),
        slicedPhysicalBlock K S D f s F θ q markWeight V Z
          (ps.image (fun I => I.val.val)) (cs.image (fun I => I.val.val))
          (bs.image (fun I => I.val.val)) k.val.val := by
  simp only [physicalBlock, physicalAtom_eq_class_sum K S D f s,
    slicedPhysicalBlock_eq_exterior_sum K S D f s]
  calc
    _ = ∑ P ∈ ps, ∑ c ∈ cs, ∑ q : FourClasses (SixthLocalClasses K S),
          ∑ b ∈ bs, slicedAtom K S D f s F θ q markWeight V Z
            k.val.val P.val.val c.val.val b.val.val := by
      apply Finset.sum_congr rfl
      intro P _
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm
    _ = ∑ P ∈ ps, ∑ q : FourClasses (SixthLocalClasses K S),
          ∑ c ∈ cs, ∑ b ∈ bs, slicedAtom K S D f s F θ q markWeight V Z
            k.val.val P.val.val c.val.val b.val.val := by
      apply Finset.sum_congr rfl
      intro P _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

#print axioms literalTerm_eq_physicalAtom
#print axioms physicalAtom_eq_class_sum
#print axioms physicalBlock_eq_class_sum

end HeckeSkeleton.LowEnergy.ActualBlockReindex
