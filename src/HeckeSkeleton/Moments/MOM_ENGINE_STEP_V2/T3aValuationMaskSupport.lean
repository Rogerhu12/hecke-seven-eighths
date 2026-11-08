module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aValuationAtomCharacters

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The exceptional coefficient mask retains both original support extractions

At every second common prime, either the sixth-root ideal has positive
exponent or the active ideal does. Thus the complete coefficient mask
deletes every second common prime, with no restriction to multiplicity
one. Its old factor also retains the entire first deletion.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

namespace T3b

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positivity of both common multiplicities puts each original
common prime in the active or sixth-power deletion. -/
theorem completePhaseMask_coprime_common_prime
    (C : A.GeneralArithmeticContext σ η hS) (primes : ι → ExteriorPrime A)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (frequency : A.R) (u oldMask J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hcop : IsCoprime J.val (completePhaseMask u
      (secondOriginalMovingFactors P R C primes m n
        (actualNonunitPattern C primes m n frequency)).support.val
      (secondSixthRootIdeal primes m n) oldMask)) (i : ι) :
    IsCoprime J.val (primes i).val.asIdeal := by
  let pattern := actualNonunitPattern C primes m n frequency
  let D := secondOriginalMovingFactors P R C primes m n pattern
  have hparts := (coprime_completePhaseMask_iff u D.support.val
    (secondSixthRootIdeal primes m n) oldMask J).mp hcop
  have hfull : D.fullIdeal = secondActiveFrequencyIdeal primes m n pattern :=
    OriginalMovingFactors.singleton_fullIdeal _ _
      (secondActiveFrequencyGenerator_generates C primes m n pattern) 1
  have hactive : IsCoprime J.val (secondActiveFrequencyIdeal primes m n pattern).val := by
    rw [← hfull]
    exact (D.coprime_support_iff_fullIdeal J.val).mp hparts.1.2.2.1
  have hmin : 0 < min (m i) (n i) := lt_min (hm i) (hn i)
  by_cases hsix : 0 < min (m i) (n i) / 6
  · apply hparts.1.2.2.2.of_isCoprime_of_dvd_right
    change (primes i).val.asIdeal ∣
      ∏ j, (primes j).val.asIdeal ^ (min (m j) (n j) / 6)
    exact (dvd_pow_self _ hsix.ne').trans
      (Finset.dvd_prod_of_mem
        (fun j => (primes j).val.asIdeal ^ (min (m j) (n j) / 6))
        (Finset.mem_univ i))
  · have hrem : 0 < min (m i) (n i) % 6 := by omega
    have hexp : 0 < secondActiveExponent m n pattern i := by
      unfold secondActiveExponent
      exact hrem.trans_le (Nat.le_add_right _ _)
    apply hactive.of_isCoprime_of_dvd_right
    change (primes i).val.asIdeal ∣
      ∏ j, (primes j).val.asIdeal ^ secondActiveExponent m n pattern j
    exact (dvd_pow_self _ hexp.ne').trans
      (Finset.dvd_prod_of_mem
        (fun j => (primes j).val.asIdeal ^ secondActiveExponent m n pattern j)
        (Finset.mem_univ i))

end T3b

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (phases : OriginalPhaseData packet)
variable (h : packet.R.live) (J : HeckeGeneral.Analysis.NonzeroIdeal K)

theorem t3bCompleteMask_coprime_badPlaces
    (hcop : IsCoprime J.val (packet.t3bCompleteMask phases h)) :
    IsCoprime J.val (Arithmetic.data c).cS := by
  have hparts := (T3b.coprime_completePhaseMask_iff _ _ _ _ J).mp hcop
  exact (CanonicalOriginalPhaseCalibration.outside_iff_coprime J).mp hparts.1.1

theorem t3bCompleteMask_coprime_old
    (hcop : IsCoprime J.val (packet.t3bCompleteMask phases h)) :
    IsCoprime J.val (phases.mask false).val :=
  ((T3b.coprime_completePhaseMask_iff _ _ _ _ J).mp hcop).2

theorem t3bCompleteMask_coprime_firstDeletion
    (hcop : IsCoprime J.val (packet.t3bCompleteMask phases h))
    (Q : Ideal (𝓞 K)) (hQ : Q ∈ packet.second.physical.first.fullDeletion) :
    IsCoprime J.val Q := by
  have hold := packet.t3bCompleteMask_coprime_old phases h J hcop
  change IsCoprime J.val
    (((phases.moving false).effectiveFullSupport
      call.localizedSource.source.recipe.remaining).val * phases.deletionIdeal.val) at hold
  have hdel := (IsCoprime.mul_right_iff.mp hold).2
  exact hdel.of_isCoprime_of_dvd_right (Finset.dvd_prod_of_mem (fun Q => Q) hQ)

theorem t3bCompleteMask_coprime_commonPrime
    (hcop : IsCoprime J.val (packet.t3bCompleteMask phases h))
    (i : Fin packet.block.primeCount) :
    IsCoprime J.val (packet.R.primes i).val.asIdeal :=
  T3b.completePhaseMask_coprime_common_prime (probeData K c) (momentRowCharacters K c)
    (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity packet.R.rightMultiplicity
    packet.block.left_positive packet.block.right_positive (packet.R.frequency h.val)
    (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal (phases.mask false) J hcop i

theorem t3bCompleteMask_coprime_secondDeletion
    (hcop : IsCoprime J.val (packet.t3bCompleteMask phases h))
    (Q : Ideal (𝓞 K)) (hQ : Q ∈ primeSupport packet.key.1.val.1) :
    IsCoprime J.val Q := by
  have hcommon :
      (primePowerProduct packet.R.primes packet.R.leftMultiplicity).val =
        packet.key.1.val.1 :=
    packet.block.common_left
  have hQ' : Q ∈ primeSupport
      (primePowerProduct packet.R.primes packet.R.leftMultiplicity).val :=
    (congrArg (fun I : Ideal (𝓞 K) => Q ∈ primeSupport I) hcommon).mpr hQ
  have hsupport := primePowerProduct_support packet.R.primes packet.R.primes_injective
    packet.R.leftMultiplicity packet.block.left_positive
  have himage := (congrArg (fun S : Finset (Ideal (𝓞 K)) => Q ∈ S) hsupport).mp hQ'
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp himage
  exact packet.t3bCompleteMask_coprime_commonPrime phases h J hcop i

end RawLeafPacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bCompleteMask_coprime_secondDeletion
