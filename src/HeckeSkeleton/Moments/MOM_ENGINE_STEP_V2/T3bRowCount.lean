module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bSavings
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bMaskBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonMass

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Counting the actual exceptional rows over their original sixth bases

The partition is only by the actual sixth-power-free part supplied by
T3a.  All original unit sectors and the original extracted-ideal fibres
are counted.  The fourth-power lower bound uses the same multiplicity-one
nonunit radical on the whole selected original row class.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

namespace T3b

def rowCountConstant (c : TargetContext K) : ℝ :=
  ((Expansion.Project.canonicalDetectorTheta K (targetCharacter K c)).card *
      Nat.card (SixthUnitClasses K (places K c)) *
      (Arithmetic.unitSubgroup c).index : ℕ) * idealCountConstant K

theorem rowCountConstant_nonneg (c : TargetContext K) :
    0 ≤ rowCountConstant c :=
  mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (one_le_idealCountConstant K))

private theorem exceptional_base_count_of_data
    {A : SArithmeticData K} {σ : K →+* ℂ}
    {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
    {H ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ActualSecondCorrelationRows A σ H ι)
    (C : A.GeneralArithmeticContext σ η hS) (rows : Finset R.live)
    (base : R.live → HeckeGeneral.Analysis.NonzeroIdeal K)
    (factor : R.live → Ideal (𝓞 K)) (B : HeckeGeneral.Analysis.NonzeroIdeal K)
    (Z width v : ℝ) (sectors : ℕ)
    (hclass : ∀ h ∈ rows, ∀ i ∈ multiplicityOneNonunitPrimes C R.primes
      R.leftMultiplicity R.rightMultiplicity (R.frequency h.val),
      6 ∣ (UniqueFactorizationMonoid.normalizedFactors (R.originalIdeal h.val).val).count
        (R.primes i).val.asIdeal)
    (hfactor : ∀ h ∈ rows, (R.extractedRow C h).ideal.val =
      (base h).val * factor h ^ 6)
    (hZ : 1 ≤ Z) (hv : 0 ≤ v)
    (hwindow : ∀ h ∈ rows, Z ^ v ≤
      (Ideal.absNorm (multiplicityOneNonunitRadical C R.primes
        R.leftMultiplicity R.rightMultiplicity (R.frequency h.val)).val : ℝ))
    (hcutoff : ∀ h ∈ rows, (Ideal.absNorm (R.originalIdeal h.val).val : ℝ) ≤
      (Ideal.absNorm (gcd (primePowerProduct R.primes R.leftMultiplicity).val
        (primePowerProduct R.primes R.rightMultiplicity).val) : ℝ) *
      (Ideal.absNorm (nonunitFrequencyRadical C R.primes
        R.leftMultiplicity R.rightMultiplicity (R.frequency h.val)).val : ℝ) * Z ^ width)
    (hfibers : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      (rows.filter (fun h => (R.extractedRow C h).momentIdeal = I)).card ≤ sectors) :
    ((rows.filter (fun h => base h = B)).card : ℝ) ≤
      (sectors : ℝ) * idealCountConstant K * Z ^ ((width - 2 * v) / 6) := by
  let selected := rows.filter (fun h => base h = B)
  refine actual_exceptional_sector_count C R.primes R.primes_injective
    R.leftMultiplicity R.rightMultiplicity selected
    (fun h => R.originalIdeal h.val) (fun h => R.frequency h.val)
    (R.exceptionalRow C) B.val
    (fun h hh => hclass h (Finset.mem_filter.mp hh).1) ?_
    Z width v (sectors : ℝ) hZ hv (Nat.cast_nonneg _)
    (fun h hh => hwindow h (Finset.mem_filter.mp hh).1)
    (fun h hh => hcutoff h (Finset.mem_filter.mp hh).1) ?_
  · intro h hh
    refine ⟨factor h, ?_⟩
    exact (hfactor h (Finset.mem_filter.mp hh).1).trans
      (congrArg (fun I : HeckeGeneral.Analysis.NonzeroIdeal K => I.val * factor h ^ 6)
        (Finset.mem_filter.mp hh).2)
  · intro I hI
    obtain ⟨h, hh, hI⟩ := Finset.mem_image.mp hI
    have hsub : selected.filter (fun x => (R.exceptionalRow C x).ideal.val = I) ⊆
        rows.filter (fun x => (R.extractedRow C x).momentIdeal =
          (R.extractedRow C h).momentIdeal) := by
      intro x hx
      refine Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1, ?_⟩
      apply Subtype.ext
      exact (Finset.mem_filter.mp hx).2.trans hI.symm
    exact_mod_cast (Finset.card_le_card hsub).trans
      (hfibers (R.extractedRow C h).momentIdeal)

end T3b

namespace RawLeafPacket

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable (packet : RawLeafPacket call p)

/-- Count one actual sixth-base fibre, with the original ideal fibre
bound from T3a and the paid S5 window. -/
theorem t3b_exceptional_base_count (hpacket : packet.Realizes)
    (recovery : packet.ExceptionalRecovery) (side : Bool) (h₀ : packet.R.live)
    (B : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((packet.exceptionalRows.filter (fun h => packet.sixthBase h = B)).card : ℝ) ≤
      ((Arithmetic.unitSubgroup c).index : ℝ) * idealCountConstant K *
        call.base ^ (((packet.nominal side).skeleton.nominalRow + 12 * p.loss -
          2 * packet.t3bMultiplicityOneLength h₀) / 6) := by
  refine T3b.exceptional_base_count_of_data packet.R (Arithmetic.context c)
    packet.exceptionalRows packet.sixthBase
    (fun h => (HeckeGeneral.Analysis.ConditionalMoments.sixthPowerAmplifierPart
      (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal).val)
    B call.base ((packet.nominal side).skeleton.nominalRow + 12 * p.loss)
    (packet.t3bMultiplicityOneLength h₀) (Arithmetic.unitSubgroup c).index
    recovery.valuations recovery.factorization call.domain.scale.le
    (packet.t3bMultiplicityOneLength_nonneg h₀) ?_
    (fun h _ => packet.t3b_originalRow_norm_le h hpacket side) recovery.extracted_fibres
  intro h hh
  have hnorm := congrArg
    (fun I : (Arithmetic.data c).Exterior => (Ideal.absNorm I.val : ℝ))
    (packet.t3b_multiplicityOneRadical_eq hpacket h₀ h)
  have hpower : call.base ^ packet.t3bMultiplicityOneLength h₀ =
      (Ideal.absNorm (packet.multiplicityOneRadical h₀).val : ℝ) :=
    rpow_idealLogLength call.base call.domain.scale _
      (packet.multiplicityOneRadical h₀).property.1
  exact (hpower.trans hnorm).le

/-- Summing the actual base fibres introduces exactly the fixed theta
and sixth-unit-sector count.  No separate analytic catalogue is counted. -/
theorem t3b_exceptional_rows_count (hpacket : packet.Realizes)
    (recovery : packet.ExceptionalRecovery) (side : Bool) (h₀ : packet.R.live) :
    (packet.exceptionalRows.card : ℝ) ≤ T3b.rowCountConstant c *
      call.base ^ (((packet.nominal side).skeleton.nominalRow + 12 * p.loss -
        2 * packet.t3bMultiplicityOneLength h₀) / 6) := by
  let U := ((Arithmetic.unitSubgroup c).index : ℝ) * idealCountConstant K *
    call.base ^ (((packet.nominal side).skeleton.nominalRow + 12 * p.loss -
      2 * packet.t3bMultiplicityOneLength h₀) / 6)
  have hU : 0 ≤ U := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (one_le_idealCountConstant K)))
    (Real.rpow_nonneg call.base_pos.le _)
  have hmap : ∀ h ∈ packet.exceptionalRows,
      packet.sixthBase h ∈ packet.exceptionalBases :=
    fun h hh => Finset.mem_image_of_mem _ hh
  have hpartition := Finset.card_eq_sum_card_fiberwise hmap
  have hbases : (packet.exceptionalBases.card : ℝ) ≤
      (call.node.data.theta.card * Nat.card (SixthUnitClasses K (places K c)) : ℕ) := by
    exact_mod_cast recovery.bases_card
  calc
    _ = ∑ B ∈ packet.exceptionalBases,
        ((packet.exceptionalRows.filter (fun h => packet.sixthBase h = B)).card : ℝ) := by
      exact_mod_cast hpartition
    _ ≤ ∑ _B ∈ packet.exceptionalBases, U :=
      Finset.sum_le_sum (fun B _ =>
        packet.t3b_exceptional_base_count hpacket recovery side h₀ B)
    _ = (packet.exceptionalBases.card : ℝ) * U := by simp
    _ ≤ (call.node.data.theta.card * Nat.card (SixthUnitClasses K (places K c)) : ℕ) * U :=
      mul_le_mul_of_nonneg_right hbases hU
    _ = _ := by
      rw [call.source.source.theta_eq]
      simp only [T3b.rowCountConstant, Nat.cast_mul, U]
      ring

end RawLeafPacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_exceptional_rows_count
