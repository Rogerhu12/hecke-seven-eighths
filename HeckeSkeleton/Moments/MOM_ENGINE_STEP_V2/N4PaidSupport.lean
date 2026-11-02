import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalPhaseData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FullSecondDeletionSupport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: the original first and pool factors fit the paid support

The first fixed element has the original complementary divisor and
the original active primes. Its higher powers do not add primes.
The pool tag identifies the same actual valuation and prime, so its
reduced support is charged with the recorded moving multiplicity.
The empty-mask unit contributes no support. Every conclusion is proved
from the original source trace rather than supplied by calibration.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum CommonSupportMass
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

private theorem powerProduct_radical_mul_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (primes : ι → ExteriorPrime A) (powers : ι → ℕ) (D : A.Exterior) :
    commonRadical (D.val * (primePowerProduct primes powers).val)
        (D.val * (primePowerProduct primes powers).val) ∣
      D.val * (primePowerProduct primes (fun _ => 1)).val := by
  have htarget : D.val * (primePowerProduct primes (fun _ => 1)).val ≠ 0 :=
    mul_ne_zero D.property.1 (primePowerProduct primes (fun _ => 1)).property.1
  unfold commonRadical
  rw [Finset.inter_self]
  apply support_product_dvd htarget
  intro Q hQ
  have hprime := support_prime hQ
  have hd := (prime_mem_support_iff_dvd Q _ hprime
    (mul_ne_zero D.property.1 (primePowerProduct primes powers).property.1)).mp hQ
  apply (prime_mem_support_iff_dvd Q _ hprime htarget).mpr
  rcases hprime.dvd_or_dvd hd with hD | hprod
  · exact dvd_mul_of_dvd_left hD _
  · change Q ∣ ∏ i, (primes i).val.asIdeal ^ powers i at hprod
    obtain ⟨i, _, hi⟩ := (hprime.dvd_finsetProd_iff
      (fun i => (primes i).val.asIdeal ^ powers i)).mp hprod
    have hi' : Q ∣ (primes i).val.asIdeal := hprime.dvd_of_dvd_pow hi
    have hfactor : (primes i).val.asIdeal ∣
        (primePowerProduct primes (fun _ => 1)).val := by
      change (primes i).val.asIdeal ∣ ∏ j, (primes j).val.asIdeal ^ 1
      simpa only [pow_one] using
        Finset.dvd_prod_of_mem (fun j => (primes j).val.asIdeal) (Finset.mem_univ i)
    exact dvd_mul_of_dvd_right (hi'.trans hfactor) _

private theorem singleton_one_support :
    (OriginalMovingFactors.singleton (P := P) (R := R) ⟨1, one_ne_zero⟩ 1).support.val = 1 := by
  rw [OriginalMovingFactors.singleton_support
    (unitExterior A) 1 (unitExterior_generates A) 1]
  change commonRadical (1 : Ideal (𝓞 K)) 1 = 1
  simp only [commonRadical, primeSupport, normalizedFactors_one,
    Multiset.toFinset_zero, Finset.inter_self, Finset.prod_empty]

private theorem append_effectiveSupport_dvd
    (D E : OriginalMovingFactors A P R)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((D.append E).effectiveFullSupport remaining).val ∣
      (D.effectiveFullSupport remaining).val * E.support.val :=
  D.append_fullMaskSupport_dvd_product E (remainingMaskIdeal A remaining)

section FirstPhase

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable (C : A.GeneralArithmeticContext σ η hS)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem leftMoving_support_dvd
    (primes : ι → ExteriorPrime A) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) :
    (CanonicalLiteralFirstPhase.leftMoving C P R primes m n D δ hδ).support.val ∣
      D.val * (firstActiveIdeal primes m n).val := by
  rw [CanonicalLiteralFirstPhase.leftMoving_support]
  exact powerProduct_radical_mul_dvd (firstActivePrimes primes m n)
    (CanonicalLiteralFirstPhase.leftExponent m n) D

private theorem rightMoving_support_dvd
    (primes : ι → ExteriorPrime A) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) :
    (CanonicalLiteralFirstPhase.rightMoving C P R primes m n D δ hδ).support.val ∣
      D.val * (firstActiveIdeal primes m n).val := by
  rw [CanonicalLiteralFirstPhase.rightMoving_support]
  exact powerProduct_radical_mul_dvd (firstActivePrimes primes m n)
    (CanonicalLiteralFirstPhase.rightExponent m n) D

end FirstPhase

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

private theorem firstKey_support_dvd (key : FirstCauchyKey F) :
    key.moving.support.val ∣
      (firstPhysicalDivisorIdeal (A := Arithmetic.data c) key.divisor.val).val *
        (firstActiveIdeal key.block.primes key.block.leftMultiplicity
          key.block.rightMultiplicity).val := by
  dsimp only [FirstCauchyKey.moving]
  split
  · exact rightMoving_support_dvd _ _ _ _ _ _ _
  · exact leftMoving_support_dvd _ _ _ _ _ _ _

private theorem firstMoving_eq (key : FirstCauchyKey F)
    (a : (Arithmetic.data c).R) (ha : a ≠ 0) (he : a = key.firstElement) :
    key.moving = OriginalMovingFactors.singleton
      (P := probeData K c) (R := momentRowCharacters K c) ⟨a, ha⟩ 1 := by
  subst a
  cases hs : key.side <;>
    simp [FirstCauchyKey.moving, FirstCauchyKey.firstElement, hs,
      CanonicalLiteralFirstPhase.leftMoving, CanonicalLiteralFirstPhase.rightMoving]

private theorem firstSource_support_dvd (hfamily : family.Realizes)
    (i : Fin family.count) (ha : (family.source i).first.firstElement ≠ 0) :
    call.oldSupport.val *
      (OriginalMovingFactors.singleton (P := probeData K c) (R := momentRowCharacters K c)
        ⟨(family.source i).first.firstElement, ha⟩ 1).support.val ∣
      (family.source i).first.paidSupport.val := by
  rw [← firstMoving_eq (family.index i) _ ha (hfamily.firstElement i),
    hfamily.paid i, hfamily.complementary i]
  have hd := mul_dvd_mul (dvd_refl call.oldSupport.val) (firstKey_support_dvd (family.index i))
  convert hd using 1 <;> ac_rfl

private def paidPoolMoving
    (poolChoice : Option (AmplifierValuation × ExteriorPrime (Arithmetic.data c))) :
    OriginalMovingFactors (Arithmetic.data c) (probeData K c) (momentRowCharacters K c) :=
  match poolChoice with
  | none => OriginalMovingFactors.singleton ⟨1, one_ne_zero⟩ 1
  | some (e, q) => CanonicalLiteralPassivePhases.activeMoving
      (probeData K c) (momentRowCharacters K c) (Arithmetic.context c) q e

private theorem expansion_paid_support (expansion : PoolExpansion family)
    (hfamily : family.Realizes) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) (ha : (expansion.source i).first.firstElement ≠ 0)
    (poolChoice : Option (AmplifierValuation × ExteriorPrime (Arithmetic.data c)))
    (htag : match poolChoice with
      | none => (expansion.source i).first.tag = .direct ∨
          (expansion.source i).first.tag = .main
      | some (e, q) => (expansion.source i).first.tag = .error e q.val) :
    (call.oldSupport.val *
      (OriginalMovingFactors.singleton (P := probeData K c) (R := momentRowCharacters K c)
        ⟨(expansion.source i).first.firstElement, ha⟩ 1).support.val) *
      (paidPoolMoving poolChoice).support.val ∣ (expansion.source i).first.paidSupport.val := by
  cases expansion with
  | direct =>
    have hp : poolChoice = none := by
      cases hc : poolChoice with
      | none => rfl
      | some eq =>
        rcases eq with ⟨e, q⟩
        have ht : (family.source i).first.tag = .error e q.val := by
          simpa only [hc] using htag
        rw [hfamily.tag i] at ht
        cases ht
    simpa only [hp, paidPoolMoving, singleton_one_support, mul_one] using
      firstSource_support_dvd hfamily i ha
  | pooled pool count index source =>
    obtain ⟨_, _, horigin⟩ := hexpansion
    cases hindex : (index i).2 with
    | inl u =>
      have hm : pool.MainOrigin (index i).1 (source i) := by
        simpa only [PoolPresentation.Origin, hindex] using horigin i
      rcases hm with ⟨_, _, _, _, _, _, _, hfirst⟩
      have hp : poolChoice = none := by
        cases hc : poolChoice with
        | none => rfl
        | some eq =>
          rcases eq with ⟨e, q⟩
          have ht : (source i).first.tag = .error e q.val := by
            simpa only [hc] using htag
          rw [hfirst] at ht
          cases ht
      have ha' : (family.source (index i).1).first.firstElement ≠ 0 := by
        simpa only [hfirst] using ha
      simpa only [hp, paidPoolMoving, singleton_one_support, mul_one, hfirst] using
        firstSource_support_dvd hfamily (index i).1 ha'
    | inr qe =>
      rcases qe with ⟨q, e⟩
      have he : pool.ErrorOrigin (index i).1 q e (source i) := by
        simpa only [PoolPresentation.Origin, hindex] using horigin i
      rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, helement, _, _, _, ht, _, hpaid⟩
      have hp : poolChoice = some (e, q.val) := by
        cases hc : poolChoice with
        | none =>
          have hh : (source i).first.tag = .direct ∨ (source i).first.tag = .main := by
            simpa only [hc] using htag
          rw [ht] at hh
          rcases hh with hh | hh <;> cases hh
        | some eq =>
          rcases eq with ⟨e', q'⟩
          have hh : (source i).first.tag = .error e' q'.val := by
            simpa only [hc] using htag
          have hsame := ht.symm.trans hh
          injection hsame with heq hq
          have hq' : q.val = q' := Subtype.ext hq
          simp only [hc, ← heq, ← hq']
      have ha' : (family.source (index i).1).first.firstElement ≠ 0 := by
        rw [← helement]
        exact ha
      have hd := mul_dvd_mul (firstSource_support_dvd hfamily (index i).1 ha')
        (dvd_refl (q.val.val.asIdeal ^ e.movingMultiplicity))
      simpa only [hp, paidPoolMoving, CanonicalLiteralPassivePhases.activeMoving_support,
        helement, hpaid] using hd

variable {packet : RawLeafPacket call p}

/-- The original trace pays the complete old moving support, the actual
first factor, and the same reduced pool factor. No remaining passive
deletion is reintroduced after its original finite allocation. -/
theorem paidMoving_effectiveSupport_dvd
    (phases : OriginalPhaseData packet) (hpacket : packet.Realizes) :
    ((phases.moving true).effectiveFullSupport
      call.localizedSource.source.recipe.remaining).val ∣
        packet.second.physical.first.paidSupport.val := by
  have hfixed :
      (call.oldSupport.val * phases.firstMoving.support.val) *
        (phases.poolMoving true).support.val ∣ packet.second.physical.first.paidSupport.val := by
    rcases hpacket with ⟨trace, geometry, raw, j, htrace, _, _, rfl⟩
    let i : Fin trace.expansion.count := (raw.index j).val.1.1
    have hphysical := htrace.second.physical i
    have ha : (trace.expansion.source i).first.firstElement ≠ 0 := by
      rw [← hphysical]
      exact phases.first_nonzero
    have ht : match phases.pool with
        | none => (trace.expansion.source i).first.tag = .direct ∨
            (trace.expansion.source i).first.tag = .main
        | some (e, q) => (trace.expansion.source i).first.tag = .error e q.val := by
      rw [← hphysical]
      exact phases.pool_tag
    have hd := expansion_paid_support trace.expansion htrace.cauchy htrace.expansion
      i ha phases.pool ht
    have hp : paidPoolMoving phases.pool = phases.poolMoving true := by
      cases hpool : phases.pool <;> rfl
    rw [hp] at hd
    simpa only [← hphysical, OriginalPhaseData.firstMoving] using hd
  let old := call.localizedSource.source.recipe.moving
  let remaining := call.localizedSource.source.recipe.remaining
  let empty := CanonicalLiteralFixedPhases.emptyDivisorMoving (probeData K c) (momentRowCharacters K c)
  have hfirst := append_effectiveSupport_dvd old phases.firstMoving remaining
  have hpool := append_effectiveSupport_dvd (old.append phases.firstMoving)
    (phases.poolMoving true) remaining
  have hempty := append_effectiveSupport_dvd
    ((old.append phases.firstMoving).append (phases.poolMoving true)) empty remaining
  have hfull := hempty.trans (mul_dvd_mul
    (hpool.trans (mul_dvd_mul hfirst (dvd_refl _))) (dvd_refl _))
  have hunit : empty.support.val = 1 :=
    CanonicalLiteralFixedPhases.emptyDivisorMoving_support (probeData K c) (momentRowCharacters K c)
  change ((phases.moving true).effectiveFullSupport remaining).val ∣ _
  exact hfull.trans (by simpa only [hunit, mul_one] using hfixed)

private def appendAtoms
    (D E : OriginalMovingFactors A P R) (old unit nonunit : A.Exterior)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (left : D.SupportAtoms old unit nonunit remaining)
    (right : E.SupportAtoms old unit nonunit remaining) :
    (D.append E).SupportAtoms old unit nonunit remaining where
  ideal := Fin.append left.ideal right.ideal
  generates := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.append_left, OriginalMovingFactors.append_element_left] using left.generates j
    · intro j
      simpa only [Fin.append_right, OriginalMovingFactors.append_element_right] using right.generates j
  oldPower := Fin.append left.oldPower right.oldPower
  unitPower := Fin.append left.unitPower right.unitPower
  nonunitPower := Fin.append left.nonunitPower right.nonunitPower
  factor_divides := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.append_left] using left.factor_divides j
    · intro j
      simpa only [Fin.append_right] using right.factor_divides j
  remaining_divides := left.remaining_divides

private def paidOldAtoms
    (D : OriginalMovingFactors A P R)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (paid unit nonunit root : A.Exterior)
    (hpaid : (D.effectiveFullSupport remaining).val ∣ paid.val) :
    D.SupportAtoms (ExteriorIdealEuler.mul paid root) unit nonunit
      (remainingMaskIdeal A remaining * exteriorMomentIdeal root) where
  ideal := D.factorIdeal
  generates := D.factorIdeal_generates
  oldPower i := (normalizedFactors (D.factorIdeal i).val).card
  unitPower _ := 0
  nonunitPower _ := 0
  factor_divides i := by
    have hd : (D.effectiveFullSupport remaining).val ∣ paid.val * root.val :=
      dvd_mul_of_dvd_left hpaid _
    have hp := (D.factorIdeal_dvd_effectiveFullSupport_pow remaining i).trans
      (pow_dvd_pow_of_dvd hd (normalizedFactors (D.factorIdeal i).val).card)
    simpa only [pow_zero, mul_one] using hp
  remaining_divides := by
    have hr := (D.remainingMaskIdeal_dvd_effectiveFullSupport remaining).trans hpaid
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (mul_dvd_mul hr (dvd_refl root.val)) _) _

/-- Each atom is the actual original first/pool list or the same
second active factor. The complete sixth root is retained in the
remaining ideal and in the charged old support, with no extra premise
about either complete support or a completed budget. -/
def paidSecondSupportAtoms
    (phases : OriginalPhaseData packet) (hpacket : packet.Realizes)
    (hm : ∀ i, 0 < packet.R.leftMultiplicity i)
    (hn : ∀ i, 0 < packet.R.rightMultiplicity i)
    (pattern : Fin packet.block.primeCount → Bool)
    (h : packet.R.NonunitClass (Arithmetic.context c) pattern) :
    ((phases.moving true).append
      (secondOriginalMovingFactors (probeData K c) (momentRowCharacters K c)
        (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity
        packet.R.rightMultiplicity pattern)).SupportAtoms
      (ExteriorIdealEuler.mul packet.second.physical.first.paidSupport
        (secondSixthRootIdeal packet.R.primes packet.R.leftMultiplicity packet.R.rightMultiplicity))
      (unitFrequencyRadical (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity
        packet.R.rightMultiplicity (packet.R.frequency h.val.val))
      (nonunitFrequencyRadical (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity
        packet.R.rightMultiplicity (packet.R.frequency h.val.val))
      (remainingMaskIdeal (Arithmetic.data c) call.localizedSource.source.recipe.remaining *
        exteriorMomentIdeal (secondSixthRootIdeal packet.R.primes
          packet.R.leftMultiplicity packet.R.rightMultiplicity)) := by
  let old := phases.moving true
  let remaining := call.localizedSource.source.recipe.remaining
  let paid := packet.second.physical.first.paidSupport
  let root := secondSixthRootIdeal packet.R.primes packet.R.leftMultiplicity packet.R.rightMultiplicity
  let unit := unitFrequencyRadical (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity
    packet.R.rightMultiplicity (packet.R.frequency h.val.val)
  let nonunit := nonunitFrequencyRadical (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity
    packet.R.rightMultiplicity (packet.R.frequency h.val.val)
  have hp : (old.effectiveFullSupport remaining).val ∣ paid.val :=
    paidMoving_effectiveSupport_dvd phases hpacket
  have hr : (remainingMaskIdeal (Arithmetic.data c) remaining).val ∣ paid.val :=
    (old.remainingMaskIdeal_dvd_effectiveFullSupport remaining).trans hp
  exact appendAtoms old _ (ExteriorIdealEuler.mul paid root) unit nonunit _
    (paidOldAtoms old remaining paid unit nonunit root hp)
    (packet.R.nonunitClassFullDeletionSupportAtoms (probeData K c) (momentRowCharacters K c)
      (Arithmetic.context c) hm hn paid (remainingMaskIdeal (Arithmetic.data c) remaining) hr pattern h)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.paidMoving_effectiveSupport_dvd
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.paidSecondSupportAtoms
