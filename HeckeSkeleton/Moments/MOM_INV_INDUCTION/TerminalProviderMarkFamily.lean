import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderTupleSplit
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderFrozenBlock

/-!
# Row-independent active coefficients from the original marked source

Every original tuple and every active subset is retained. An inactive
tuple meeting the frozen row or puncture gives a proved zero; every
remaining collision is one of the literal atom masks. Thus the tuple
reindexing may be done before the moving row is chosen.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalMarkFamily

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeSkeleton.LowEnergy.ActualRows HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualReflectionReindex HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open TerminalAtoms TerminalMarks TerminalAggregation TerminalTupleSplit
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)
local notation "Ext" => ExteriorIdeal K S

instance frozenStatesFintype (g r : Ext) : Fintype (FrozenState K S g r) := Fintype.ofFinite _

def InactiveAway (g r : Ext) (B : Finset (ExteriorPrime K S)) : Prop :=
  ∀ p ∈ B, ¬p.val.asIdeal ∣ g.val.val ∧ ¬p.val.asIdeal ∣ r.val.val

def fixedMarkData (g r : Ext) (hr : Squarefree r.val.val) (u : S.unit K)
    (B : Finset (ExteriorPrime K S)) (hB : InactiveAway K S g r B) : FixedData K S where
  frozen := g
  puncture := r
  puncture_squarefree := hr
  rowUnit := u
  inactive := B
  inactive_away := hB

def choiceValue (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (g r : Ext) (hr : Squarefree r.val.val) (u : S.unit K)
    (s : FrozenState K S g r) (B : Finset (ExteriorPrime K S))
    (P : Ext) (V : ℝ → ℂ) (X : ℝ) (k : Ext) : ℂ :=
  if hB : InactiveAway K S g r B then
    ∑' cb : Ext × Ext, GeneralReflectedEnergy.atom K S D
      (fixedMarkData K S g r hr u B hB) s F θ V X k P cb.1 cb.2
  else 0

theorem choiceValue_eq_zero_of_collision
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (g r k : Ext) (hr : Squarefree r.val.val) (u : S.unit K)
    (s : FrozenState K S g r) (Q A : Finset (ExteriorPrime K S))
    (p : ExteriorPrime K S) (hp : p ∈ Q)
    (hbad : p.val.asIdeal ∣ k.val.val ∨ p.val.asIdeal ∣ g.val.val ∨ p.val.asIdeal ∣ r.val.val)
    (V : ℝ → ℂ) (X : ℝ) :
    choiceValue K S D F θ g r hr u s (Q \ A) (primeSetIdeal K S A) V X k = 0 := by
  unfold choiceValue
  split_ifs with hB
  · apply tsum_eq_zero
    intro cb
    unfold GeneralReflectedEnergy.atom
    split_ifs with hk hA hkA hcol hAb
    · exfalso
      by_cases hpA : p ∈ A
      · have hd : p.val.asIdeal ∣ (primeSetIdeal K S A).val.val :=
          (prime_dvd_primeSetIdeal_iff K S A p).mpr hpA
        have hpS : p ∈ exteriorSupport K S (primeSetIdeal K S A) := by
          rw [TerminalAtoms.exteriorSupport_primeSetIdeal]
          exact hpA
        rcases hbad with hpk | hpg | hpr
        · exact p.val.prime.not_unit (hkA.isUnit_of_dvd' hpk hd)
        · exact (hA.prime_away p hpS).1 hpg
        · exact (hA.prime_away p hpS).2 hpr
      · have hpB : p ∈ Q \ A := Finset.mem_sdiff.mpr ⟨hp, hpA⟩
        rcases hbad with hpk | hpg | hpr
        · exact hk.inactive_away p hpB hpk
        · exact (hB p hpB).1 hpg
        · exact (hB p hpB).2 hpr
    all_goals rfl
  · rfl

/-- The all-tuples reflection formula includes every moving-row
collision as a zero of the same actual reflected atoms. -/
theorem completedThetaSum_eq_choices
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (g r k : Ext) (hr : Squarefree r.val.val) (u : S.unit K)
    (hk : Squarefree k.val.val) (hkg : IsCoprime k.val.val g.val.val)
    (hkr : IsCoprime k.val.val r.val.val)
    (Q : Finset (ExteriorPrime K S)) (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    completedThetaSum K S D θ
        ((S.unitEquivUnitsInteger K u).val * D.generator (exteriorMul K S k g)) r Q V.toFun X =
      ∑ s : FrozenState K S g r, ∑ A : {A : Finset (ExteriorPrime K S) // A ⊆ Q},
        choiceValue K S D F θ g r hr u s (Q \ A.val) (primeSetIdeal K S A.val) V.toFun X k := by
  by_cases hgood : ∀ p ∈ Q, ¬p.val.asIdeal ∣ k.val.val ∧
      ¬p.val.asIdeal ∣ g.val.val ∧ ¬p.val.asIdeal ∣ r.val.val
  · let d : MarkedDatum K S := {
      moving := k, frozen := g, puncture := r, moving_squarefree := hk,
      puncture_squarefree := hr, moving_frozen_coprime := hkg,
      moving_puncture_coprime := hkr, rowUnit := u, marks := Q,
      marks_coprime := hgood }
    have hd := TerminalAtoms.completedThetaSum_eq_atoms K S D F θ hreflection d V X hX
    change completedThetaSum K S D θ (rowElement K S D d) d.puncture d.marks V.toFun X = _
    rw [hd]
    simp only [tsum_fintype]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro A hA
    have hB : InactiveAway K S g r (Q \ A.val) :=
      fun p hp => (hgood p (Finset.mem_sdiff.mp hp).1).2
    rw [choiceValue, dif_pos hB]
    rfl
  · have hbad : ∃ p ∈ Q, p.val.asIdeal ∣ k.val.val ∨
        p.val.asIdeal ∣ g.val.val ∨ p.val.asIdeal ∣ r.val.val := by
      simpa only [not_forall, not_and_or, not_not, exists_prop] using hgood
    obtain ⟨p, hp, hbad⟩ := hbad
    have hz : completedThetaSum K S D θ
        ((S.unitEquivUnitsInteger K u).val * D.generator (exteriorMul K S k g)) r Q V.toFun X = 0 := by
      rcases hbad with hpk | hpg | hpr
      · apply completedThetaSum_eq_zero_of_mark_overlap K S D θ _ r Q V.toFun X p hp
        unfold sIntegerModulusContraction
        rw [Ideal.span_singleton_mul_left_unit (S.unitEquivUnitsInteger K u).isUnit,
          contraction_thetaGenerator]
        exact dvd_mul_of_dvd_left hpk _
      · apply completedThetaSum_eq_zero_of_mark_overlap K S D θ _ r Q V.toFun X p hp
        unfold sIntegerModulusContraction
        rw [Ideal.span_singleton_mul_left_unit (S.unitEquivUnitsInteger K u).isUnit,
          contraction_thetaGenerator]
        exact dvd_mul_of_dvd_right hpg _
      · exact TerminalReflection.completedThetaSum_eq_zero_of_puncture_overlap
          K S D θ _ r Q V.toFun X p hp hpr
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro s hs
    apply Finset.sum_eq_zero
    intro A hA
    exact choiceValue_eq_zero_of_collision K S D F θ g r k hr u s Q A.val p hp hbad V.toFun X

variable {σ : Type*} [DecidableEq σ]
variable (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
variable (a : σ → Ideal (𝓞 K) → ℂ)
variable (hprime : ∀ i ∈ I, ∀ p ∈ L i, Prime p)
variable (hexterior : ∀ i ∈ I, ∀ p ∈ L i, MOM_INV_STEP.CanonicalChildren.IsExterior K S p)
variable (hdisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (L i) (L j))

def inactiveBlock (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (g r : Ext) (hr : Squarefree r.val.val) (u : S.unit K)
    (s : FrozenState K S g r) (J : {J : Finset σ // J ⊆ I})
    (qi : tuplePool K (I \ J.val) L) (V : ℝ → ℂ) (X : ℝ) (k : Ext) : ℂ :=
  let B := tuplePrimes K S (I \ J.val) L
    (fun i hi => hprime i (Finset.mem_sdiff.mp hi).1)
    (fun i hi => hexterior i (Finset.mem_sdiff.mp hi).1) qi
  ∑ P ∈ idealPool K S J.val L (fun i hi => hprime i (J.property hi))
      (fun i hi => hexterior i (J.property hi)),
    coefficient K S J.val L (fun i hi => hprime i (J.property hi))
        (fun i hi => hexterior i (J.property hi)) a P *
      choiceValue K S D F θ g r hr u s B P V X k

theorem inactiveBlock_eq_fullSource (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (g r : Ext) (hr : Squarefree r.val.val) (u : S.unit K)
    (s : FrozenState K S g r) (J : {J : Finset σ // J ⊆ I})
    (qi : tuplePool K (I \ J.val) L) (V : ℝ → ℂ) (X : ℝ) (k : Ext)
    (hB : InactiveAway K S g r (tuplePrimes K S (I \ J.val) L
      (fun i hi => hprime i (Finset.mem_sdiff.mp hi).1)
      (fun i hi => hexterior i (Finset.mem_sdiff.mp hi).1) qi)) :
    inactiveBlock K S D I L a hprime hexterior F θ g r hr u s J qi V X k =
      TerminalFrozenBlock.fullSource K S D
        (fixedMarkData K S g r hr u _ hB) s F θ
        (coefficient K S J.val L (fun i hi => hprime i (J.property hi))
          (fun i hi => hexterior i (J.property hi)) a) V X
        (idealPool K S J.val L (fun i hi => hprime i (J.property hi))
          (fun i hi => hexterior i (J.property hi))) k := by
  unfold inactiveBlock TerminalFrozenBlock.fullSource
  apply Finset.sum_congr rfl
  intro P hP
  rw [choiceValue, dif_pos hB]

theorem tuple_sum_eq_inactive_blocks (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (g r : Ext) (hr : Squarefree r.val.val) (u : S.unit K)
    (s : FrozenState K S g r) (J : {J : Finset σ // J ⊆ I})
    (V : ℝ → ℂ) (X : ℝ) (k : Ext) :
    (∑ q : tuplePool K I L, tupleWeight K I a q.val *
      choiceValue K S D F θ g r hr u s
        (tuplePrimes K S I L hprime hexterior q \
          activePrimes K I L S hprime hexterior J.val J.property q)
        (primeSetIdeal K S (activePrimes K I L S hprime hexterior J.val J.property q)) V X k) =
      ∑ qi : tuplePool K (I \ J.val) L, tupleWeight K (I \ J.val) a qi.val *
        inactiveBlock K S D I L a hprime hexterior F θ g r hr u s J qi V X k := by
  rw [TerminalTupleSplit.sum_split K I L J.val J.property]
  apply Finset.sum_congr rfl
  intro qi hqi
  let hpA := fun i hi => hprime i (J.property hi)
  let heA := fun i hi => hexterior i (J.property hi)
  let hpI := fun i hi => hprime i (Finset.mem_sdiff.mp hi).1
  let heI := fun i hi => hexterior i (Finset.mem_sdiff.mp hi).1
  let B := tuplePrimes K S (I \ J.val) L hpI heI qi
  have hterm (qa : tuplePool K J.val L) :
      tupleWeight K I a (join K I L J.val J.property qa qi).val *
        choiceValue K S D F θ g r hr u s
          (tuplePrimes K S I L hprime hexterior (join K I L J.val J.property qa qi) \
            activePrimes K I L S hprime hexterior J.val J.property
              (join K I L J.val J.property qa qi))
          (primeSetIdeal K S (activePrimes K I L S hprime hexterior J.val J.property
            (join K I L J.val J.property qa qi))) V X k =
        tupleWeight K (I \ J.val) a qi.val *
          (tupleWeight K J.val a qa.val *
            choiceValue K S D F θ g r hr u s B (tupleIdeal K S J.val L hpA heA qa) V X k) := by
    have ha : restrict K I L J.val J.property (join K I L J.val J.property qa qi) = qa :=
      congrArg Prod.fst ((equiv K I L J.val J.property).apply_symm_apply (qa, qi))
    have hi : restrict K I L (I \ J.val) Finset.sdiff_subset
        (join K I L J.val J.property qa qi) = qi :=
      congrArg Prod.snd ((equiv K I L J.val J.property).apply_symm_apply (qa, qi))
    rw [inactivePrimes_eq K I L S hprime hexterior hdisjoint J.val J.property,
      weight_join K I L a J.val J.property]
    simp only [activePrimes, ha, hi, tupleIdeal, hpA, heA, hpI, heI, B]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  congr 1
  exact sum_eq_aggregated K S J.val L hpA heA
    (fun i hi j hj hij => hdisjoint i (J.property hi) j (J.property hj) hij) a
      (fun P => choiceValue K S D F θ g r hr u s B P V X k)

/-- Exact original product-mark source, regrouped with active ideal
coefficients bounded by one and inactive tuple weights still explicit. -/
theorem canonicalCompletedSum_eq_inactive_blocks
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (g r k : Ext) (hr : Squarefree r.val.val) (u : S.unit K)
    (hk : Squarefree k.val.val) (hkg : IsCoprime k.val.val g.val.val)
    (hkr : IsCoprime k.val.val r.val.val)
    (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    MOM_BASE.canonicalCompletedSum (MOM_BASE.exteriorGamma K S D)
      (MOM_BASE.canonicalTau K S D θ
        ((S.unitEquivUnitsInteger K u).val * D.generator (exteriorMul K S k g)) r.val.val)
      (MOMInvStep.divisorMark I L a) V.toFun X =
      ∑ s : FrozenState K S g r, ∑ J : {J : Finset σ // J ⊆ I},
        ∑ qi : tuplePool K (I \ J.val) L, tupleWeight K (I \ J.val) a qi.val *
          inactiveBlock K S D I L a hprime hexterior F θ g r hr u s J qi V.toFun X k := by
  rw [canonicalCompletedSum_eq_marked_tuples K S D θ _ r I L a hprime hexterior
    V.toFun X V.upper hX (fun y hy => (V.support hy).2)]
  have hchoice (q : tuplePool K I L) (s : FrozenState K S g r) :
      (∑ A : {A : Finset (ExteriorPrime K S) // A ⊆ tuplePrimes K S I L hprime hexterior q},
        choiceValue K S D F θ g r hr u s
          (tuplePrimes K S I L hprime hexterior q \ A.val)
          (primeSetIdeal K S A.val) V.toFun X k) =
      ∑ J : {J : Finset σ // J ⊆ I},
        choiceValue K S D F θ g r hr u s
          (tuplePrimes K S I L hprime hexterior q \
            activePrimes K I L S hprime hexterior J.val J.property q)
          (primeSetIdeal K S (activePrimes K I L S hprime hexterior J.val J.property q))
          V.toFun X k :=
    ((choicesEquiv K I L S hprime hexterior hdisjoint q).sum_comp _).symm
  simp_rw [completedThetaSum_eq_choices K S D F θ hreflection g r k hr u hk hkg hkr
    _ V X hX, hchoice, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J hJ
  exact tuple_sum_eq_inactive_blocks K S D I L a hprime hexterior hdisjoint
    F θ g r hr u s J V.toFun X k

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalMarkFamily

end
