import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderReflection

/-!
# The original reflected source uses the permitted block atoms

For each original active-mark choice, the inactive marks and the frozen
row data form exactly `ActualSeparatedBlock.FixedData`. The source datum
and its reflection index are proved equal to the original objects. This
identifies the completed source with the very atoms occurring in the
general reflected-energy input, including both coprimality masks and the
whole dual cube.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalAtoms

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualReflectionReindex
  HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local notation "Ext" => ExteriorIdeal K S

theorem exteriorSupport_primeSetIdeal (A : Finset (ExteriorPrime K S)) :
    exteriorSupport K S (primeSetIdeal K S A) = A := by
  ext p
  rw [mem_exteriorSupport_iff, prime_dvd_primeSetIdeal_iff]

def fixedForChoice (d : MarkedDatum K S) (A : MarkChoice K S d) : FixedData K S where
  frozen := d.frozen
  puncture := d.puncture
  puncture_squarefree := d.puncture_squarefree
  rowUnit := d.rowUnit
  inactive := d.marks \ A.val
  inactive_away := by
    intro p hp
    have hm := d.marks_coprime p (Finset.mem_sdiff.mp hp).1
    exact ⟨hm.2.1, hm.2.2⟩

theorem moving_admissible (d : MarkedDatum K S) (A : MarkChoice K S d) :
    RowAdmissible K S (fixedForChoice K S d A) d.moving where
  squarefree := d.moving_squarefree
  frozen_coprime := d.moving_frozen_coprime
  puncture_coprime := d.moving_puncture_coprime
  inactive_away := fun p hp => (d.marks_coprime p (Finset.mem_sdiff.mp hp).1).1

theorem active_admissible (d : MarkedDatum K S) (A : MarkChoice K S d) :
    MarkAdmissible K S (fixedForChoice K S d A) (primeSetIdeal K S A.val) where
  squarefree := HeckeGeneral.Arithmetic.IdealMobiusMask.squarefree_primeProduct _
  prime_away := by
    intro p hp
    rw [exteriorSupport_primeSetIdeal] at hp
    exact (d.marks_coprime p (A.property hp)).2
  inactive_disjoint := by
    change Disjoint (d.marks \ A.val) (exteriorSupport K S (primeSetIdeal K S A.val))
    rw [exteriorSupport_primeSetIdeal]
    exact Finset.disjoint_left.mpr (fun p hp hpa => (Finset.mem_sdiff.mp hp).2 hpa)

theorem moving_active_coprime (d : MarkedDatum K S) (A : MarkChoice K S d) :
    IsCoprime d.moving.val.val (primeSetIdeal K S A.val).val.val := by
  apply Ideal.coprime_of_no_prime_ge
  intro P hm hA hP
  have hP0 : P ≠ ⊥ := by
    intro hz
    exact nonZeroDivisors.coe_ne_zero d.moving.val (le_bot_iff.mp (hz ▸ hm))
  let p : HeightOneSpectrum (𝓞 K) := ⟨P, hP, hP0⟩
  let ep : ExteriorPrime K S := ⟨p, d.moving.property p (Ideal.dvd_iff_le.mpr hm)⟩
  have hpA : ep ∈ A.val := (prime_dvd_primeSetIdeal_iff K S A.val ep).mp
    (Ideal.dvd_iff_le.mpr hA)
  exact (d.marks_coprime ep (A.property hpA)).1 (Ideal.dvd_iff_le.mpr hm)

private theorem markedDatum_ext {d e : MarkedDatum K S}
    (hm : d.moving = e.moving) (hf : d.frozen = e.frozen)
    (hr : d.puncture = e.puncture) (hu : d.rowUnit = e.rowUnit)
    (hQ : d.marks = e.marks) : d = e := by
  cases d
  cases e
  cases hm
  cases hf
  cases hr
  cases hu
  cases hQ
  rfl

/-- The fixed block does not introduce a replacement source datum. -/
theorem sourceDatum_eq_original (d : MarkedDatum K S) (A : MarkChoice K S d) :
    sourceDatum K S (fixedForChoice K S d A) d.moving (primeSetIdeal K S A.val)
      (moving_admissible K S d A) (active_admissible K S d A)
      (moving_active_coprime K S d A) = d := by
  refine markedDatum_ext K S ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · rfl
  · change d.marks \ A.val ∪ exteriorSupport K S (primeSetIdeal K S A.val) = d.marks
    rw [exteriorSupport_primeSetIdeal]
    exact Finset.sdiff_union_of_subset A.property

private theorem reflectionIndex_heq {d e : MarkedDatum K S} (hde : d = e)
    (i : ReflectionIndex K S d) (j : ReflectionIndex K S e)
    (hP : i.activeMarks = j.activeMarks) (hF : i.activeFrozen = j.activeFrozen)
    (ha : i.numeratorFrozen = j.numeratorFrozen) (hn : i.n = j.n)
    (hc : i.c = j.c) (hu : i.unitSector = j.unitSector) : HEq i j := by
  cases hde
  exact heq_of_eq (reflectionIndex_ext K S hP hF ha hn hc hu)

private theorem reflectedTerm_congr {d e : MarkedDatum K S} (hde : d = e)
    (i : ReflectionIndex K S d) (j : ReflectionIndex K S e) (hij : HEq i j)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ) (X : ℝ) :
    reflectedTerm K S D d i F θ V X = reflectedTerm K S D e j F θ V X := by
  cases hde
  cases hij
  rfl

/-- The active mark and the complete cube in the permitted block atom
are exactly those of the original reflected index. -/
theorem extended_original_eq_atom (d : MarkedDatum K S) (A : MarkChoice K S d)
    (s : FrozenState K S d.frozen d.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ) (X : ℝ)
    (cb : FrozenColumn K S s) :
    extendMarkedColumn K S s A.val
        (fun z => reflectedTerm K S D d
          ((reflectionSigmaEquiv K S d).symm ⟨s, A, z⟩) F θ V X) cb =
      GeneralReflectedEnergy.atom K S D (fixedForChoice K S d A) s F θ V X
        d.moving (primeSetIdeal K S A.val) cb.val.1 cb.val.2 := by
  let f : FixedData K S := fixedForChoice K S d A
  have hk : RowAdmissible K S f d.moving := moving_admissible K S d A
  have hP : MarkAdmissible K S f (primeSetIdeal K S A.val) := active_admissible K S d A
  have hkm : IsCoprime d.moving.val.val (primeSetIdeal K S A.val).val.val :=
    moving_active_coprime K S d A
  by_cases hPb : IsCoprime (primeSetIdeal K S A.val).val.val cb.val.2.val.val
  · let source : MarkedDatum K S :=
      sourceDatum K S f d.moving (primeSetIdeal K S A.val) hk hP hkm
    let sourceIdx : ReflectionIndex K S source :=
      sourceIndex K S f s d.moving (primeSetIdeal K S A.val) hk hP hkm cb hPb
    let originalIdx : ReflectionIndex K S d :=
      (reflectionSigmaEquiv K S d).symm ⟨s, A, ⟨cb, hPb⟩⟩
    have hdatum : source = d := sourceDatum_eq_original K S d A
    have hindex : HEq sourceIdx originalIdx := by
      refine reflectionIndex_heq K S hdatum sourceIdx originalIdx ?_ ?_ ?_ ?_ ?_ ?_
      · exact exteriorSupport_primeSetIdeal K S A.val
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    have hterm : reflectedTerm K S D source sourceIdx F θ V X =
        reflectedTerm K S D d originalIdx F θ V X :=
      reflectedTerm_congr K S D hdatum sourceIdx originalIdx hindex F θ V X
    have hatom : GeneralReflectedEnergy.atom K S D f s F θ V X
        d.moving (primeSetIdeal K S A.val) cb.val.1 cb.val.2 =
        reflectedTerm K S D source sourceIdx F θ V X :=
      GeneralReflectedEnergy.atom_on_source K S D f s F θ V X
        d.moving (primeSetIdeal K S A.val) cb.val.1 cb.val.2 hk hP hkm cb.property hPb
    rw [extendMarkedColumn, dif_pos hPb]
    exact hterm.symm.trans hatom.symm
  · simp only [extendMarkedColumn, dif_neg hPb, GeneralReflectedEnergy.atom,
      dif_pos hk, dif_pos hP, dif_pos hkm, dif_pos cb.property, dif_neg hPb,
      dite_eq_ite, ite_self]

theorem atom_tsum_over_complete_columns (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ) (X : ℝ)
    (k P : Ext) :
    (∑' cb : FrozenColumn K S s,
      GeneralReflectedEnergy.atom K S D f s F θ V X k P cb.val.1 cb.val.2) =
      ∑' cb : Ext × Ext, GeneralReflectedEnergy.atom K S D f s F θ V X k P cb.1 cb.2 := by
  rw [tsum_extendColumn K S s]
  apply tsum_congr
  intro cb
  by_cases hc : ColumnCondition K S s cb.1 cb.2
  · simp only [extendColumn, dif_pos hc]
  · simp only [extendColumn, dif_neg hc]
    symm
    unfold GeneralReflectedEnergy.atom
    split_ifs <;> simp_all

/-- The full completed theta source is an exact sum of the permitted
general reflected-energy atoms, before truncation, dyadic separation,
or any norm inequality. -/
theorem completedThetaSum_eq_atoms (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (d : MarkedDatum K S) (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    completedThetaSum K S D θ (rowElement K S D d) d.puncture d.marks V.toFun X =
      ∑' s : FrozenState K S d.frozen d.puncture, ∑' A : MarkChoice K S d,
        ∑' cb : Ext × Ext,
          GeneralReflectedEnergy.atom K S D (fixedForChoice K S d A) s F θ V.toFun X
            d.moving (primeSetIdeal K S A.val) cb.1 cb.2 := by
  rw [GeneralReflectedEnergy.completed_source_expansion K S D F θ hreflection d V X hX]
  apply tsum_congr
  intro s
  apply tsum_congr
  intro A
  simp_rw [extended_original_eq_atom K S D d A s F θ V.toFun X]
  exact atom_tsum_over_complete_columns K S D (fixedForChoice K S d A) s F θ V.toFun X
    d.moving (primeSetIdeal K S A.val)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalAtoms

end
