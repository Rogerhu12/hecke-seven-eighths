import HeckeSkeleton.LowEnergy.GeneralReconstruction
import HeckeSkeleton.LowEnergy.GeneralInactiveEnergy

/-!
# Canonical blocks are blocks of the original reflected series

`sourceTerm` uses the original `reflectedTerm` and its actual source
index.  Its guards express only exterior support and the original
row, label, puncture and inactive exclusions.  The row--active-mark and
active-mark--cube masks remain inside `literalTerm`.

The equality with the finite hybrid block is proved before taking any
norm.  In particular an energy estimate on a `FrozenBlock` can be applied
to the original canonical block without a reconstruction hypothesis.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralCanonicalBlock

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualSieveDictionary
open HeckeSkeleton.LowEnergy.GeneralReconstruction
open HeckeSkeleton.LowEnergy.GeneralMarkedEnergy
open HeckeSkeleton.LowEnergy.GeneralAggregation
open HeckeSkeleton.LowEnergy.GeneralInactiveEnergy
open HeckeSkeleton.LowEnergy.ClassSlices
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- Only arithmetic conditions on the literal finite supports.  The
coefficient bounds and length ranges are supplied by `Admissible`.
No reflection identity or norm estimate is a field of this record. -/
structure SourceSupported (b : FrozenBlock K S) : Prop where
  rows_exterior : ∀ k ∈ b.rows, IsExterior K S k
  marks_exterior : ∀ P ∈ b.marks, IsExterior K S P
  squarefree_exterior : ∀ c ∈ b.squarefreeColumns, IsExterior K S c
  cube_exterior : ∀ n ∈ b.cubeColumns, IsExterior K S n
  rows_admissible : ∀ k (hk : k ∈ b.rows),
    RowAdmissible K S b.fixed (toExterior K S k (rows_exterior k hk))
  marks_admissible : ∀ P (hP : P ∈ b.marks),
    MarkAdmissible K S b.fixed (toExterior K S P (marks_exterior P hP))

/-- The source coefficient at the original reflection index, extended by
zero to the common ideal rectangle.  All four guards are one-variable
arithmetic support tests. -/
def sourceTerm (b : FrozenBlock K S)
    (s : FrozenState K S b.fixed.frozen b.fixed.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ)
    (k P c n : Ideal (𝓞 K)) : ℂ :=
  if hk : IsExterior K S k then
    if hP : IsExterior K S P then
      if hc : IsExterior K S c then
        if hn : IsExterior K S n then
          if hrow : RowAdmissible K S b.fixed (toExterior K S k hk) then
            if hmark : MarkAdmissible K S b.fixed (toExterior K S P hP) then
              literalTerm K S D b.fixed s F θ b.markWeight V b.X
                (toExterior K S k hk) (toExterior K S P hP)
                (toExterior K S c hc) (toExterior K S n hn) hrow hmark
            else 0
          else 0
        else 0
      else 0
    else 0
  else 0

def sourceRow (b : FrozenBlock K S) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) : ℂ :=
  if k ∈ b.rows then
    ∑ s ∈ b.states, ∑ P ∈ b.marks, ∑ c ∈ b.squarefreeColumns, ∑ n ∈ b.cubeColumns,
      sourceTerm K S D b s F θ V.toFun k P c n
  else 0

def sourceEnergy (b : FrozenBlock K S) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : SmoothAnnularTest) : ℝ :=
  ∑ k ∈ b.rows, ‖sourceRow K S D b F θ V k‖ ^ 2

theorem sourceTerm_eq_class_sum [Fintype (SixthLocalClasses K S)]
    (hD : AllowedGeneratorInput K S D) (b : FrozenBlock K S)
    (h : SourceSupported K S b)
    (s : FrozenState K S b.fixed.frozen b.fixed.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ)
    (k P c n : Ideal (𝓞 K)) (hk : k ∈ b.rows) (hP : P ∈ b.marks)
    (hc : c ∈ b.squarefreeColumns) (hn : n ∈ b.cubeColumns) :
    sourceTerm K S D b s F θ V k P c n =
      ∑ q : FourClasses (SixthLocalClasses K S),
        slicedAtom K S D b.fixed s F θ q b.markWeight V b.X k P c n := by
  rw [sourceTerm, dif_pos (h.rows_exterior k hk), dif_pos (h.marks_exterior P hP),
    dif_pos (h.squarefree_exterior c hc), dif_pos (h.cube_exterior n hn),
    dif_pos (h.rows_admissible k hk), dif_pos (h.marks_admissible P hP),
    literalTerm_eq_generalAtom K S D b.fixed s hD]
  exact generalAtom_eq_class_sum K S D b.fixed s F θ b.markWeight V b.X
    (toExterior K S k (h.rows_exterior k hk))
    (toExterior K S P (h.marks_exterior P hP))
    (toExterior K S c (h.squarefree_exterior c hc))
    (toExterior K S n (h.cube_exterior n hn))

theorem slicedBlock_eq_sumAtoms (b : FrozenBlock K S)
    (s : FrozenState K S b.fixed.frozen b.fixed.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (V : ℝ → ℂ) (k : Ideal (𝓞 K)) :
    GeneralReflectedBlock.slicedBlock K S D b.fixed s F θ q b.markWeight V b.X
        b.marks b.squarefreeColumns b.cubeColumns k =
      ∑ P ∈ b.marks, ∑ c ∈ b.squarefreeColumns, ∑ n ∈ b.cubeColumns,
        slicedAtom K S D b.fixed s F θ q b.markWeight V b.X k P c n := by
  simp only [GeneralReflectedBlock.slicedBlock, slicedAtom, Finset.mul_sum]

/-- Exact source reconstruction for every finite dual block, including
the zero extension on its actual row restrictions. -/
theorem sourceRow_eq_restrictedRow [Finite (SixthLocalClasses K S)]
    (hD : AllowedGeneratorInput K S D) (b : FrozenBlock K S)
    (h : SourceSupported K S b)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) :
    sourceRow K S D b F θ V k = b.restrictedRow D F θ V k := by
  letI : Fintype (SixthLocalClasses K S) := Fintype.ofFinite _
  by_cases hk : k ∈ b.rows
  · rw [sourceRow, if_pos hk, FrozenBlock.restrictedRow, if_pos hk, FrozenBlock.row]
    apply Finset.sum_congr rfl
    intro s hs
    have he : (∑ P ∈ b.marks, ∑ c ∈ b.squarefreeColumns, ∑ n ∈ b.cubeColumns,
        sourceTerm K S D b s F θ V.toFun k P c n) =
        ∑ P ∈ b.marks, ∑ c ∈ b.squarefreeColumns, ∑ n ∈ b.cubeColumns,
          ∑ q : FourClasses (SixthLocalClasses K S),
            slicedAtom K S D b.fixed s F θ q b.markWeight V.toFun b.X k P c n := by
      apply Finset.sum_congr rfl
      intro P hP
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro n hn
      exact sourceTerm_eq_class_sum K S D hD b h s F θ V.toFun k P c n hk hP hc hn
    rw [he]
    simp only [tsum_fintype, slicedBlock_eq_sumAtoms K S D b s]
    calc
      _ = ∑ P ∈ b.marks, ∑ c ∈ b.squarefreeColumns,
          ∑ q : FourClasses (SixthLocalClasses K S), ∑ n ∈ b.cubeColumns,
            slicedAtom K S D b.fixed s F θ q b.markWeight V.toFun b.X k P c n := by
        apply Finset.sum_congr rfl
        intro P _
        apply Finset.sum_congr rfl
        intro c _
        exact Finset.sum_comm
      _ = ∑ P ∈ b.marks, ∑ q : FourClasses (SixthLocalClasses K S),
          ∑ c ∈ b.squarefreeColumns, ∑ n ∈ b.cubeColumns,
            slicedAtom K S D b.fixed s F θ q b.markWeight V.toFun b.X k P c n := by
        apply Finset.sum_congr rfl
        intro P _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  · simp only [sourceRow, FrozenBlock.restrictedRow, if_neg hk]

theorem sourceEnergy_eq [Finite (SixthLocalClasses K S)]
    (hD : AllowedGeneratorInput K S D) (b : FrozenBlock K S)
    (h : SourceSupported K S b)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : SmoothAnnularTest) :
    sourceEnergy K S D b F θ V = b.energy D F θ V := by
  simp only [sourceEnergy, sourceRow_eq_restrictedRow K S D hD b h]
  exact FrozenBlock.restrictedRow_energy D b F θ V b.rows (Finset.Subset.refl _)

/-- The original source block has the general marked-energy exponent.
Every analytic estimate is obtained from the two original sieves and the
kernel; its hypotheses concern only the original arithmetic supports. -/
theorem canonical_frozen_block_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Fmax eps : ℝ) (hW : 0 ≤ W) (hFmax : 0 ≤ Fmax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z A E : ℝ), 1 < Z → 0 < A →
      ∀ (V : SmoothAnnularTest) (b : FrozenBlock K S),
      b.Admissible Z W A E Fmax → SourceSupported K S b →
      sourceEnergy K S D b F θ V ≤
        C * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          ‖inactiveWeight K S b.fixed‖ ^ 2 * Z ^ (E + eps) := by
  obtain ⟨C, hC, hb⟩ := general_frozen_block_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic W Fmax eps hW hFmax heps
  refine ⟨C, hC, ?_⟩
  intro Z A E hZ hA V b hadm hsource
  rw [sourceEnergy_eq K S D hD b hsource]
  exact hb Z A E hZ hA V b hadm

/-- The original tuple coefficient multiplies the original reflected
source block.  Its inactive prefactor is already inside `sourceTerm`. -/
def sourceInactiveRow (b : InactiveFamily K S) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) : ℂ :=
  ∑ p ∈ b.tuples, b.coefficient p * sourceRow K S D (b.blocks p) F θ V k

def sourceMarkedRow {rmax : ℕ} (b : MarkedFamily K S rmax)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) : ℂ :=
  ∑ a ∈ b.patterns, if k ∈ (b.components a).rows then
    sourceInactiveRow K S D (b.components a) F θ V k else 0

def sourceMarkedEnergy {rmax : ℕ} (b : MarkedFamily K S rmax)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : SmoothAnnularTest) : ℝ :=
  ∑ k ∈ b.rows, ‖sourceMarkedRow K S D b F θ V k‖ ^ 2

/-- Source support remains purely arithmetic at every activity pattern
and every inactive tuple. -/
def FamilySourceSupported {rmax : ℕ} (b : MarkedFamily K S rmax) : Prop :=
  ∀ a ∈ b.patterns, ∀ p ∈ (b.components a).tuples,
    SourceSupported K S ((b.components a).blocks p)

theorem sourceInactiveRow_eq [Finite (SixthLocalClasses K S)]
    (hD : AllowedGeneratorInput K S D) (b : InactiveFamily K S)
    (hsource : ∀ p ∈ b.tuples, SourceSupported K S (b.blocks p))
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) :
    sourceInactiveRow K S D b F θ V k = b.row D F θ V k := by
  unfold sourceInactiveRow InactiveFamily.row
  apply Finset.sum_congr rfl
  intro p hp
  rw [sourceRow_eq_restrictedRow K S D hD (b.blocks p) (hsource p hp)]

theorem sourceMarkedRow_eq [Finite (SixthLocalClasses K S)]
    (hD : AllowedGeneratorInput K S D) {rmax : ℕ} (b : MarkedFamily K S rmax)
    (hsource : FamilySourceSupported K S b)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) :
    sourceMarkedRow K S D b F θ V k = b.row D F θ V k := by
  unfold sourceMarkedRow MarkedFamily.row
  apply Finset.sum_congr rfl
  intro a ha
  rw [sourceInactiveRow_eq K S D hD (b.components a) (hsource a ha)]
  rfl

theorem sourceMarkedEnergy_eq [Finite (SixthLocalClasses K S)]
    (hD : AllowedGeneratorInput K S D) {rmax : ℕ} (b : MarkedFamily K S rmax)
    (hsource : FamilySourceSupported K S b)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : SmoothAnnularTest) :
    sourceMarkedEnergy K S D b F θ V = b.energy D F θ V := by
  simp only [sourceMarkedEnergy, sourceMarkedRow_eq K S D hD b hsource,
    MarkedFamily.energy]

/-- Lemma 4.8 for the actual source blocks: all activity patterns, inactive
tuples, frozen choices and local classes are summed inside each original
row norm.  The actual powerful parts, supported simple parts and row-unit
classes are summed outside the squared norm.  E is a common bound for the
explicit (can-Eref) exponent before its O/2 term; it is not an energy input.
-/
theorem canonical_complete_family_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Fmax Omax Lmax : ℝ) (rmax : ℕ) (eps : ℝ)
    (hW : 0 ≤ W) (hFmax : 0 ≤ Fmax) (hOmax : 0 ≤ Omax)
    (hLmax : 0 ≤ Lmax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z O A B E : ℝ),
      1 < Z → 0 ≤ O → O ≤ Omax → 0 < A → 1 ≤ B →
      ∀ (V : SmoothAnnularTest) (label puncture : ExteriorIdeal K S)
        (R : Finset (IdealRankin.PowerfulIdeal K))
        (families : IdealRankin.PowerfulIdeal K → Finset (ExteriorPrime K S) →
          SixthUnitClasses K S → MarkedFamily K S rmax),
      ((label.val * puncture.val).val.absNorm : ℝ) ≤ Z ^ Lmax →
      (∀ I ∈ R, IdealRankin.powerfulNorm K I ≤ Z ^ O) →
      (∀ I ∈ R, ∀ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∀ u, (families I T u).Admissible Z W A B E Fmax) →
      (∀ I ∈ R, ∀ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∀ u, FamilySourceSupported K S (families I T u)) →
      (∑ I ∈ R, ∑ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∑' u : SixthUnitClasses K S, sourceMarkedEnergy K S D (families I T u) F θ V) ≤
        C * A ^ 2 * (B ^ rmax) ^ 2 *
          testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          Z ^ (O / 2 + E + eps) := by
  obtain ⟨C, hC, hb⟩ := general_complete_family_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic W Fmax Omax Lmax rmax eps hW hFmax hOmax hLmax heps
  refine ⟨C, hC, ?_⟩
  intro Z O A B E hZ hO hO' hA hB V label puncture R families hnorm hR hadm hsource
  have he :
      (∑ I ∈ R, ∑ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∑' u : SixthUnitClasses K S, sourceMarkedEnergy K S D (families I T u) F θ V) =
      ∑ I ∈ R, ∑ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∑' u : SixthUnitClasses K S, (families I T u).energy D F θ V := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro T hT
    apply tsum_congr
    intro u
    exact sourceMarkedEnergy_eq K S D hD (families I T u) (hsource I hI T hT u) F θ V
  rw [he]
  exact hb Z O A B E hZ hO hO' hA hB V label puncture R families hnorm hR hadm

#print axioms sourceRow_eq_restrictedRow
#print axioms sourceEnergy_eq
#print axioms canonical_frozen_block_energy
#print axioms sourceMarkedRow_eq
#print axioms canonical_complete_family_energy

end HeckeSkeleton.LowEnergy.GeneralCanonicalBlock
