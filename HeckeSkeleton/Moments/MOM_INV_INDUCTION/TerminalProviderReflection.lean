import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderMarks
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderTerminalConductor
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.GeneralReflectedEnergy

/-!
# Genuine reflection of the punctured canonical marked source

The original row and its fourth-power averaged label determine the
powerful, supported and moving ideals.  The original unit is retained.
The allowed generator section is used through its exact sextic symbol
identity, so no multiplicativity of chosen generators is asserted.

Every marked tuple is covered. A tuple meeting the row or the puncture
is a literal zero before reflection. Every other tuple gives an actual
`MarkedDatum`, and the supplied coefficient reflection gives the full
frozen-state expansion with its complete cube coordinate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalReflection

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeSkeleton.LowEnergy.ActualRows HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualSymbols HeckeSkeleton.LowEnergy.ActualFrozenCube
  HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.Moments.MOM_BASE HeckeSkeleton.Moments.MOM_INV_STEP
open ProviderTerminalConductor TerminalMarks
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local notation "Ext" => ExteriorIdeal K S

def totalRow (k f : Ext) : Ext := exteriorMul K S k (exteriorPower K S f 4)

def frozenRow (k f r : Ext) : Ext :=
  frozenIdeal K S (exteriorPowerfulPart K S k) (rowSupported K S k f r) f

theorem moving_frozen_eq_total (k f r : Ext) :
    exteriorMul K S (rowResidual K S k f r) (frozenRow K S k f r) =
      totalRow K S k f := by
  have h := congrArg (fun I : Ext => I.val.val) (row_decomposition K S k f r)
  apply Subtype.ext
  apply Subtype.ext
  change (rowResidual K S k f r).val.val *
    (((exteriorPowerfulPart K S k).val.val * (rowSupported K S k f r).val.val) *
      f.val.val ^ 4) = k.val.val * f.val.val ^ 4
  change ((exteriorPowerfulPart K S k).val.val * (rowSupported K S k f r).val.val) *
    (rowResidual K S k f r).val.val = k.val.val at h
  rw [← h]
  ring

/-- Exactly the primes which do not already kill the literal completed
source through its row symbol or its puncture mask. -/
def MarksAway (k f r : Ext) (Q : Finset (ExteriorPrime K S)) : Prop :=
  ∀ p ∈ Q, ¬p.val.asIdeal ∣ (totalRow K S k f).val.val ∧
    ¬p.val.asIdeal ∣ r.val.val

def markedDatum (k f r : Ext) (u : S.unit K)
    (hr : Squarefree r.val.val) (Q : Finset (ExteriorPrime K S))
    (hQ : MarksAway K S k f r Q) : MarkedDatum K S where
  moving := rowResidual K S k f r
  frozen := frozenRow K S k f r
  puncture := r
  moving_squarefree := rowResidual_squarefree K S k f r
  puncture_squarefree := hr
  moving_frozen_coprime := rowResidual_coprime_frozen K S k f r
  moving_puncture_coprime := rowResidual_coprime_puncture K S k f r
  rowUnit := u
  marks := Q
  marks_coprime := by
    intro p hp
    have he := congrArg (fun I : Ext => I.val.val) (moving_frozen_eq_total K S k f r)
    refine ⟨?_, ?_, (hQ p hp).2⟩
    · intro hpm
      apply (hQ p hp).1
      rw [← he]
      exact dvd_mul_of_dvd_left hpm _
    · intro hpf
      apply (hQ p hp).1
      rw [← he]
      exact dvd_mul_of_dvd_right hpf _

theorem markedDatum_rowElement (k f r : Ext) (u : S.unit K)
    (hr : Squarefree r.val.val) (Q : Finset (ExteriorPrime K S))
    (hQ : MarksAway K S k f r Q) :
    rowElement K S D (markedDatum K S k f r u hr Q hQ) =
      (S.unitEquivUnitsInteger K u).val * D.generator (totalRow K S k f) := by
  change (S.unitEquivUnitsInteger K u).val *
    D.generator (exteriorMul K S (rowResidual K S k f r) (frozenRow K S k f r)) = _
  rw [moving_frozen_eq_total]

theorem fourth_generator_symbol (hD : AllowedGeneratorInput K S D) (A f : Ext) :
    idealSymbol K S D A (D.generator (exteriorPower K S f 4)) =
      idealSymbol K S D A (D.generator f) ^ 4 := by
  have he : exteriorPower K S f 4 =
      exteriorMul K S (exteriorMul K S f f) (exteriorMul K S f f) := by
    apply Subtype.ext
    apply Subtype.ext
    change f.val.val ^ 4 = (f.val.val * f.val.val) * (f.val.val * f.val.val)
    ring
  simp only [he, actualSymbol_mul_right K S D hD]
  ring

/-- Equality holds at every ideal symbol, including its coprimality
zeros, although the two chosen row generators need not be equal. -/
theorem canonical_row_symbol (hD : AllowedGeneratorInput K S D)
    (A k f : Ext) (u : S.unit K) :
    idealSymbol K S D A
        (((S.unitEquivUnitsInteger K u).val * D.generator k) * D.generator f ^ 4) =
      idealSymbol K S D A
        ((S.unitEquivUnitsInteger K u).val * D.generator (totalRow K S k f)) := by
  change (elementSymbolHom K S D A)
      (((S.unitEquivUnitsInteger K u).val * D.generator k) * D.generator f ^ 4) =
    (elementSymbolHom K S D A)
      ((S.unitEquivUnitsInteger K u).val * D.generator (totalRow K S k f))
  simp only [map_mul, map_pow]
  change (_ * idealSymbol K S D A (D.generator k)) *
    idealSymbol K S D A (D.generator f) ^ 4 =
    _ * idealSymbol K S D A (D.generator (totalRow K S k f))
  rw [totalRow, actualSymbol_mul_right K S D hD, fourth_generator_symbol K S D hD]
  ring

theorem completedThetaSum_row_symbol_congr
    (θ : HeckeCharacter K) (m m' : S.integer K) (r : Ext)
    (Q : Finset (ExteriorPrime K S)) (V : ℝ → ℂ) (X : ℝ)
    (he : ∀ A : Ext, idealSymbol K S D A m = idealSymbol K S D A m') :
    completedThetaSum K S D θ m r Q V X =
      completedThetaSum K S D θ m' r Q V X := by
  apply tsum_congr
  intro cn
  simp only [completedTerm, he]

theorem completedThetaSum_canonical_row
    (hD : AllowedGeneratorInput K S D) (θ : HeckeCharacter K)
    (k f r : Ext) (u : S.unit K) (Q : Finset (ExteriorPrime K S))
    (V : ℝ → ℂ) (X : ℝ) :
    completedThetaSum K S D θ
        (((S.unitEquivUnitsInteger K u).val * D.generator k) * D.generator f ^ 4) r Q V X =
      completedThetaSum K S D θ
        ((S.unitEquivUnitsInteger K u).val * D.generator (totalRow K S k f)) r Q V X :=
  completedThetaSum_row_symbol_congr K S D θ _ _ r Q V X
    (fun A => canonical_row_symbol K S D hD A k f u)

theorem completedThetaSum_eq_zero_of_puncture_overlap
    (θ : HeckeCharacter K) (m : S.integer K) (r : Ext)
    (Q : Finset (ExteriorPrime K S)) (V : ℝ → ℂ) (X : ℝ)
    (p : ExteriorPrime K S) (hpQ : p ∈ Q) (hpr : p.val.asIdeal ∣ r.val.val) :
    completedThetaSum K S D θ m r Q V X = 0 := by
  apply tsum_eq_zero
  intro cn
  unfold completedTerm
  split_ifs with h
  · exact False.elim (p.val.prime.not_unit
      (h.2.1.isUnit_of_dvd' (h.2.2 p hpQ) hpr))
  · rfl

theorem completedThetaSum_eq_zero_of_not_marksAway
    (hD : AllowedGeneratorInput K S D) (θ : HeckeCharacter K)
    (k f r : Ext) (u : S.unit K) (Q : Finset (ExteriorPrime K S))
    (V : ℝ → ℂ) (X : ℝ) (hQ : ¬MarksAway K S k f r Q) :
    completedThetaSum K S D θ
      (((S.unitEquivUnitsInteger K u).val * D.generator k) * D.generator f ^ 4) r Q V X = 0 := by
  rw [completedThetaSum_canonical_row K S D hD]
  have hbad : ∃ p ∈ Q, p.val.asIdeal ∣ (totalRow K S k f).val.val ∨
      p.val.asIdeal ∣ r.val.val := by
    simpa only [MarksAway, not_forall, not_and_or, not_not, exists_prop] using hQ
  obtain ⟨p, hpQ, hpm | hpr⟩ := hbad
  · apply completedThetaSum_eq_zero_of_mark_overlap K S D θ _ r Q V X p hpQ
    have hc : sIntegerModulusContraction K S
        ((S.unitEquivUnitsInteger K u).val * D.generator (totalRow K S k f)) =
        (totalRow K S k f).val.val := by
      unfold sIntegerModulusContraction
      rw [Ideal.span_singleton_mul_left_unit (S.unitEquivUnitsInteger K u).isUnit]
      exact contraction_thetaGenerator K S D (totalRow K S k f)
    rwa [hc]
  · exact completedThetaSum_eq_zero_of_puncture_overlap K S D θ _ r Q V X p hpQ hpr

/-- The actual reflected source, with only the proved collision zeros
removed. It retains the original unit, puncture, mark set and all dual
indices, including the complete reflected cube. -/
def reflectedRow (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (k f r : Ext) (u : S.unit K) (hr : Squarefree r.val.val)
    (Q : Finset (ExteriorPrime K S)) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  if hQ : MarksAway K S k f r Q then
    ∑' i : ReflectionIndex K S (markedDatum K S k f r u hr Q hQ),
      reflectedTerm K S D (markedDatum K S k f r u hr Q hQ) i F θ V X
  else 0

theorem completedThetaSum_eq_reflectedRow
    (hD : AllowedGeneratorInput K S D) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (k f r : Ext) (u : S.unit K) (hr : Squarefree r.val.val)
    (Q : Finset (ExteriorPrime K S)) (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    completedThetaSum K S D θ
        (((S.unitEquivUnitsInteger K u).val * D.generator k) * D.generator f ^ 4) r Q V.toFun X =
      reflectedRow K S D F θ k f r u hr Q V.toFun X := by
  by_cases hQ : MarksAway K S k f r Q
  · rw [reflectedRow, dif_pos hQ, completedThetaSum_canonical_row K S D hD,
      ← markedDatum_rowElement K S D k f r u hr Q hQ]
    exact hreflection.reflection (markedDatum K S k f r u hr Q hQ) V X hX
  · rw [reflectedRow, dif_neg hQ]
    exact completedThetaSum_eq_zero_of_not_marksAway K S D hD θ k f r u Q V.toFun X hQ

/-- The noncolliding canonical source has the exact frozen-state and
full-cube expansion required by the general reflected-energy lemma. -/
theorem completedThetaSum_canonical_reindexed
    (hD : AllowedGeneratorInput K S D) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (k f r : Ext) (u : S.unit K) (hr : Squarefree r.val.val)
    (Q : Finset (ExteriorPrime K S)) (hQ : MarksAway K S k f r Q)
    (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    let d := markedDatum K S k f r u hr Q hQ
    completedThetaSum K S D θ
        (((S.unitEquivUnitsInteger K u).val * D.generator k) * D.generator f ^ 4) r Q V.toFun X =
      ∑' s : FrozenState K S d.frozen d.puncture, ∑' A : MarkChoice K S d,
        ∑' cb : FrozenColumn K S s, extendMarkedColumn K S s A.val
          (fun z => reflectedTerm K S D d
            ((reflectionSigmaEquiv K S d).symm ⟨s, A, z⟩) F θ V.toFun X) cb := by
  dsimp only
  rw [completedThetaSum_canonical_row K S D hD,
    ← markedDatum_rowElement K S D k f r u hr Q hQ]
  exact GeneralReflectedEnergy.completed_source_expansion K S D F θ hreflection
    (markedDatum K S k f r u hr Q hQ) V X hX

/-- The actual product-mark completed source is the sum of reflected
rows for its original prime tuples. The tuple coefficient is unchanged,
and collision deletion is proved inside `reflectedRow`. -/
theorem canonicalCompletedSum_eq_reflected_tuples {σ : Type*} [DecidableEq σ]
    (hD : AllowedGeneratorInput K S D) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (k f r : Ext) (u : S.unit K) (hr : Squarefree r.val.val)
    (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ)
    (hprime : ∀ i ∈ I, ∀ p ∈ L i, Prime p)
    (hexterior : ∀ i ∈ I, ∀ p ∈ L i, CanonicalChildren.IsExterior K S p)
    (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    canonicalCompletedSum (exteriorGamma K S D)
        (canonicalTau K S D θ
          (((S.unitEquivUnitsInteger K u).val * D.generator k) * D.generator f ^ 4) r.val.val)
        (HeckeSkeleton.Moments.MOMInvStep.divisorMark I L a) V.toFun X =
      ∑ q : tuplePool K I L, tupleWeight K I a q.val *
        reflectedRow K S D F θ k f r u hr
          (tuplePrimes K S I L hprime hexterior q) V.toFun X := by
  rw [canonicalCompletedSum_eq_marked_tuples K S D θ _ r I L a hprime hexterior
    V.toFun X V.upper hX (fun y hy => (V.support hy).2)]
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  exact completedThetaSum_eq_reflectedRow K S D hD F θ hreflection
    k f r u hr (tuplePrimes K S I L hprime hexterior q) V X hX

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalReflection

end
