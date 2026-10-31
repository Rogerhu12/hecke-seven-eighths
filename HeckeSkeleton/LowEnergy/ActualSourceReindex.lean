import HeckeSkeleton.LowEnergy.ActualBlockReindex

/-!
# Every original reflection coordinate is a literal fixed-data block entry

The inactive mark set is the actual difference of the original marks and
the active choice.  Reconstructing the source datum gives the original
`MarkedDatum`, including its unit sector and puncture.  This identifies the
sigma-reindexed reflection summands with the exact block atoms.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualSourceReindex

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualSymbolProducts
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualBlockReindex
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem exteriorSupport_primeSetIdeal (A : Finset (ExteriorPrime K S)) :
    exteriorSupport K S (primeSetIdeal K S A) = A := by
  ext p
  rw [mem_exteriorSupport_iff, prime_dvd_primeSetIdeal_iff]

theorem primeSetIdeal_squarefree (A : Finset (ExteriorPrime K S)) :
    Squarefree (primeSetIdeal K S A).val.val :=
  HeckeGeneral.Arithmetic.IdealMobiusMask.squarefree_primeProduct _

def splitFixed (d : MarkedDatum K S) (A : MarkChoice K S d) : FixedData K S where
  frozen := d.frozen
  puncture := d.puncture
  puncture_squarefree := d.puncture_squarefree
  rowUnit := d.rowUnit
  inactive := d.marks \ A.val
  inactive_away := by
    intro p hp
    exact ⟨(d.marks_coprime p (Finset.mem_sdiff.mp hp).1).2.1,
      (d.marks_coprime p (Finset.mem_sdiff.mp hp).1).2.2⟩

theorem splitRow_admissible (d : MarkedDatum K S) (A : MarkChoice K S d) :
    RowAdmissible K S (splitFixed K S d A) d.moving where
  squarefree := d.moving_squarefree
  frozen_coprime := d.moving_frozen_coprime
  puncture_coprime := d.moving_puncture_coprime
  inactive_away := by
    intro p hp
    exact (d.marks_coprime p (Finset.mem_sdiff.mp hp).1).1

theorem splitMark_admissible (d : MarkedDatum K S) (A : MarkChoice K S d) :
    MarkAdmissible K S (splitFixed K S d A) (primeSetIdeal K S A.val) where
  squarefree := primeSetIdeal_squarefree K S A.val
  prime_away := by
    intro p hp
    rw [exteriorSupport_primeSetIdeal] at hp
    exact ⟨(d.marks_coprime p (A.property hp)).2.1,
      (d.marks_coprime p (A.property hp)).2.2⟩
  inactive_disjoint := by
    rw [exteriorSupport_primeSetIdeal]
    exact disjoint_sdiff_self_left

theorem split_row_mark_coprime (d : MarkedDatum K S) (A : MarkChoice K S d) :
    IsCoprime d.moving.val.val (primeSetIdeal K S A.val).val.val := by
  apply Ideal.coprime_of_no_prime_ge
  intro P hm hP hprime
  have hP0 : P ≠ ⊥ := by
    intro hz
    exact nonZeroDivisors.coe_ne_zero d.moving.val (le_bot_iff.mp (hz ▸ hm))
  let p : HeightOneSpectrum (𝓞 K) := ⟨P, hprime, hP0⟩
  let ep : ExteriorPrime K S := ⟨p, d.moving.property p (Ideal.dvd_iff_le.mpr hm)⟩
  have hep : ep ∈ A.val := (prime_dvd_primeSetIdeal_iff K S A.val ep).mp
    (Ideal.dvd_iff_le.mpr hP)
  exact (d.marks_coprime ep (A.property hep)).1 (Ideal.dvd_iff_le.mpr hm)

theorem markedDatum_ext {d e : MarkedDatum K S}
    (hm : d.moving = e.moving) (hf : d.frozen = e.frozen)
    (hp : d.puncture = e.puncture) (hu : d.rowUnit = e.rowUnit)
    (hQ : d.marks = e.marks) : d = e := by
  cases d
  cases e
  cases hm
  cases hf
  cases hp
  cases hu
  cases hQ
  rfl

theorem fixedData_ext {f g : FixedData K S}
    (hf : f.frozen = g.frozen) (hp : f.puncture = g.puncture)
    (hu : f.rowUnit = g.rowUnit) (hQ : f.inactive = g.inactive) : f = g := by
  cases f
  cases g
  cases hf
  cases hp
  cases hu
  cases hQ
  rfl

theorem split_sourceDatum (d : MarkedDatum K S) (A : MarkChoice K S d) :
    sourceDatum K S (splitFixed K S d A) d.moving (primeSetIdeal K S A.val)
      (splitRow_admissible K S d A) (splitMark_admissible K S d A)
      (split_row_mark_coprime K S d A) = d := by
  apply markedDatum_ext K S
    (d := sourceDatum K S (splitFixed K S d A) d.moving (primeSetIdeal K S A.val)
      (splitRow_admissible K S d A) (splitMark_admissible K S d A)
      (split_row_mark_coprime K S d A)) (e := d) rfl rfl rfl rfl
  change (d.marks \ A.val) ∪ exteriorSupport K S (primeSetIdeal K S A.val) = d.marks
  rw [exteriorSupport_primeSetIdeal]
  exact Finset.sdiff_union_of_subset A.property

theorem reflectedTerm_congr (D : ThetaArithmeticData K S)
    {d e : MarkedDatum K S} (hde : d = e)
    (i : ReflectionIndex K S d) (j : ReflectionIndex K S e)
    (hP : i.activeMarks = j.activeMarks) (hF : i.activeFrozen = j.activeFrozen)
    (ha : i.numeratorFrozen = j.numeratorFrozen) (hn : i.n = j.n)
    (hc : i.c = j.c) (hu : i.unitSector = j.unitSector)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ) (X : ℝ) :
    reflectedTerm K S D d i F θ V X = reflectedTerm K S D e j F θ V X := by
  cases hde
  have hi : i = j := reflectionIndex_ext K S hP hF ha hn hc hu
  rw [hi]

theorem summable_extendColumn {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) (g : FrozenColumn K S s → ℂ)
    (hg : Summable g) :
    Summable (fun cb : ExteriorIdeal K S × ExteriorIdeal K S =>
      extendColumn K S s g cb.1 cb.2) := by
  let G : ExteriorIdeal K S × ExteriorIdeal K S → ℂ :=
    fun cb => extendColumn K S s g cb.1 cb.2
  have hzero : ∀ cb ∉ Set.range (Subtype.val : FrozenColumn K S s → _), G cb = 0 := by
    intro cb hcb
    have hc : ¬ColumnCondition K S s cb.1 cb.2 := by
      intro hc
      exact hcb ⟨⟨cb, hc⟩, rfl⟩
    simp [G, extendColumn, hc]
  have hsub : Summable (G ∘ (Subtype.val : FrozenColumn K S s → _)) :=
    hg.congr (fun cb => by simp [G, extendColumn, cb.property])
  exact (Subtype.val_injective.summable_iff hzero).mp hsub

theorem summable_extendMarkedColumn {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) (A : Finset (ExteriorPrime K S))
    (g : MarkedColumn K S s A → ℂ) (hg : Summable g) :
    Summable (extendMarkedColumn K S s A g) := by
  let G := extendMarkedColumn K S s A g
  have hzero : ∀ cb ∉ Set.range (Subtype.val : MarkedColumn K S s A → _), G cb = 0 := by
    intro cb hcb
    have hc : ¬IsCoprime (primeSetIdeal K S A).val.val cb.val.2.val.val := by
      intro hc
      exact hcb ⟨⟨cb, hc⟩, rfl⟩
    simp [G, extendMarkedColumn, hc]
  have hsub : Summable (G ∘ (Subtype.val : MarkedColumn K S s A → _)) :=
    hg.congr (fun cb => by simp [G, extendMarkedColumn, cb.property])
  exact (Subtype.val_injective.summable_iff hzero).mp hsub

/-- The dual section is genuinely summable because it is a section of the
original absolutely convergent reflection, not by a new block hypothesis. -/
theorem original_column_summable (D : ThetaArithmeticData K S)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (d : MarkedDatum K S) (s : FrozenState K S d.frozen d.puncture)
    (A : MarkChoice K S d) (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    Summable (fun cb : MarkedColumn K S s A.val =>
      reflectedTerm K S D d ((reflectionSigmaEquiv K S d).symm ⟨s, A, cb⟩)
        F θ V.toFun X) := by
  let e := reflectionSigmaEquiv K S d
  have h := e.symm.summable_iff.mpr (hreflection.reflected_absolute d V X hX)
  exact (h.sigma_factor s).sigma_factor A

/-- The exact original sigma-indexed reflection summand is the block atom
for its actual inactive marks and full cube. -/
theorem reflectionSummand_eq_physicalAtom (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (d : MarkedDatum K S) (s : FrozenState K S d.frozen d.puncture)
    (A : MarkChoice K S d) (cb : MarkedColumn K S s A.val)
    (V : ℝ → ℂ) (Z : ℝ) :
    reflectedTerm K S D d ((reflectionSigmaEquiv K S d).symm ⟨s, A, cb⟩)
      F θ V (Z * exteriorNorm K S (primeSetIdeal K S d.marks)) =
      physicalAtom K S D (splitFixed K S d A) s F θ (fun _ => 1) V Z
        d.moving (primeSetIdeal K S A.val) cb.val.val.1 cb.val.val.2 := by
  let f := splitFixed K S d A
  let hk := splitRow_admissible K S d A
  let hp := splitMark_admissible K S d A
  let hkp := split_row_mark_coprime K S d A
  let i := sourceIndex K S f s d.moving (primeSetIdeal K S A.val) hk hp hkp cb.val cb.property
  have hterm : reflectedTerm K S D
      (sourceDatum K S f d.moving (primeSetIdeal K S A.val) hk hp hkp) i F θ V
        (Z * exteriorNorm K S (primeSetIdeal K S d.marks)) =
      reflectedTerm K S D d ((reflectionSigmaEquiv K S d).symm ⟨s, A, cb⟩)
        F θ V (Z * exteriorNorm K S (primeSetIdeal K S d.marks)) := by
    apply reflectedTerm_congr K S D (split_sourceDatum K S d A)
    · change exteriorSupport K S (primeSetIdeal K S A.val) = A.val
      exact exteriorSupport_primeSetIdeal K S A.val
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  rw [← hterm]
  have h := literalTerm_eq_physicalAtom K S D f s hD F θ (fun _ => 1) V Z
    d.moving (primeSetIdeal K S A.val) cb.val.val.1 cb.val.val.2 hk hp
  unfold literalTerm at h
  erw [dif_pos hkp, dif_pos cb.val.property, dif_pos cb.property, one_mul] at h
  have hm := congrArg (fun e : MarkedDatum K S => e.marks) (split_sourceDatum K S d A)
  erw [hm] at h
  exact h

/-- The rectangular column coefficients inherit summability from the
supplied reflection after both exact zero extensions. -/
theorem extended_reflectionSummand_eq_physicalAtom (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (d : MarkedDatum K S) (s : FrozenState K S d.frozen d.puncture)
    (A : MarkChoice K S d) (V : ℝ → ℂ) (Z : ℝ)
    (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
    extendColumn K S s (extendMarkedColumn K S s A.val
      (fun z => reflectedTerm K S D d
        ((reflectionSigmaEquiv K S d).symm ⟨s, A, z⟩) F θ V
          (Z * exteriorNorm K S (primeSetIdeal K S d.marks)))) cb.1 cb.2 =
      physicalAtom K S D (splitFixed K S d A) s F θ (fun _ => 1) V Z
        d.moving (primeSetIdeal K S A.val) cb.1 cb.2 := by
  by_cases hcb : ColumnCondition K S s cb.1 cb.2
  · rw [extendColumn, dif_pos hcb]
    by_cases hPb : IsCoprime (primeSetIdeal K S A.val).val.val cb.2.val.val
    · rw [extendMarkedColumn, dif_pos hPb]
      exact reflectionSummand_eq_physicalAtom K S D hD F θ d s A
        ⟨⟨cb, hcb⟩, hPb⟩ V Z
    · simp [extendMarkedColumn, hPb, physicalAtom, ActualHybridEntry.hybridAtom]
  · simp [extendColumn, hcb, physicalAtom, columnCoefficient,
      ActualReflectionReindex.extendColumn, ActualHybridEntry.hybridAtom]
    intro _ hc
    exact (hcb hc).elim

/-- The supplied reflection is exactly the sum of the fixed-data atoms over
every frozen state, every active subset and the full common column pair.
The inactive set is the actual complement of that active subset. -/
theorem completedThetaSum_eq_physical_atoms (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (d : MarkedDatum K S) (V : SmoothAnnularTest) (Z : ℝ) (hZ : 0 < Z) :
    completedThetaSum K S D θ (rowElement K S D d) d.puncture d.marks V.toFun
        (Z * exteriorNorm K S (primeSetIdeal K S d.marks)) =
      ∑' s : FrozenState K S d.frozen d.puncture,
        ∑' A : MarkChoice K S d,
          ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
            physicalAtom K S D (splitFixed K S d A) s F θ (fun _ => 1) V.toFun Z
              d.moving (primeSetIdeal K S A.val) cb.1 cb.2 := by
  rw [completedThetaSum_reindexed K S D F θ hreflection d V _
    (mul_pos hZ (exteriorNorm_pos K S _))]
  apply tsum_congr
  intro s
  apply tsum_congr
  intro A
  rw [tsum_extendColumn K S s]
  apply tsum_congr
  intro cb
  exact extended_reflectionSummand_eq_physicalAtom K S D hD F θ d s A V.toFun Z cb

 /-- Summability of the exact rectangular column expansion follows from the
 supplied reflected absolute convergence. -/
theorem physicalAtom_columns_summable (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (d : MarkedDatum K S) (s : FrozenState K S d.frozen d.puncture)
    (A : MarkChoice K S d) (V : SmoothAnnularTest) (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun cb : ExteriorIdeal K S × ExteriorIdeal K S =>
      physicalAtom K S D (splitFixed K S d A) s F θ (fun _ => 1) V.toFun Z
        d.moving (primeSetIdeal K S A.val) cb.1 cb.2) := by
  let g : MarkedColumn K S s A.val → ℂ := fun cb =>
    reflectedTerm K S D d ((reflectionSigmaEquiv K S d).symm ⟨s, A, cb⟩)
      F θ V.toFun (Z * exteriorNorm K S (primeSetIdeal K S d.marks))
  have hg : Summable g := original_column_summable K S D F θ hreflection d s A V _
    (mul_pos hZ (exteriorNorm_pos K S _))
  have he := summable_extendColumn K S s (extendMarkedColumn K S s A.val g)
    (summable_extendMarkedColumn K S s A.val g hg)
  exact he.congr (fun cb =>
    extended_reflectionSummand_eq_physicalAtom K S D hD F θ d s A V.toFun Z cb)

theorem physicalAtom_columns_summable_fixed (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (k P : ExteriorIdeal K S) (hk : RowAdmissible K S f k)
    (hP : MarkAdmissible K S f P) (V : SmoothAnnularTest) (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun cb : ExteriorIdeal K S × ExteriorIdeal K S =>
      physicalAtom K S D f s F θ (fun _ => 1) V.toFun Z k P cb.1 cb.2) := by
  by_cases hcop : IsCoprime k.val.val P.val.val
  · let d := sourceDatum K S f k P hk hP hcop
    let A : MarkChoice K S d := ⟨exteriorSupport K S P, Finset.subset_union_right⟩
    have hf : splitFixed K S d A = f := by
      apply fixedData_ext K S (f := splitFixed K S d A) (g := f) rfl rfl rfl
      change (f.inactive ∪ exteriorSupport K S P) \ exteriorSupport K S P = f.inactive
      rw [Finset.union_sdiff_distrib, Finset.sdiff_self, Finset.union_empty]
      exact hP.inactive_disjoint.sdiff_eq_left
    have h :=
      fun t : FrozenState K S (splitFixed K S d A).frozen
          (splitFixed K S d A).puncture =>
        physicalAtom_columns_summable K S D hD F θ hreflection d t A V Z hZ
    rw [hf] at h
    have hA : primeSetIdeal K S A.val = P := by
      exact primeSetIdeal_support K S P hP.squarefree
    have hmoving : d.moving = k := rfl
    simpa only [hA, hmoving] using h s
  · have hz : (fun cb : ExteriorIdeal K S × ExteriorIdeal K S =>
        physicalAtom K S D f s F θ (fun _ => 1) V.toFun Z k P cb.1 cb.2) = 0 := by
      funext cb
      simp [physicalAtom, ActualHybridEntry.hybridAtom, hcop]
    rw [hz]
    exact summable_zero

#print axioms split_sourceDatum
#print axioms reflectionSummand_eq_physicalAtom
#print axioms original_column_summable
#print axioms completedThetaSum_eq_physical_atoms
#print axioms physicalAtom_columns_summable
#print axioms physicalAtom_columns_summable_fixed

end HeckeSkeleton.LowEnergy.ActualSourceReindex
