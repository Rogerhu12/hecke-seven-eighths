import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aValuationSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryRawAtomFormula
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinarySourceTransport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# A live original column retains every moving coprimality zero

The two exact rectangular formulas are used before the original
centered subtraction. A nonzero whole column therefore supplies a
nonzero first residual rectangle. Its literal atom mask includes the
entire actual moving support, so every second common prime is outside
that support. No unramified-background assumption is made.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace T3a

/-- A nonzero original Cartesian atom has a nonzero complete mask
on its full ideal, including the empty-slot case. -/
theorem bare_mask_nonzero {k : ℕ} (T : FixedChildCharacters K k)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x : AllocationColumn K k) (hx : allocationColumnIdeal x ≠ 0)
    (hc : rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w x ≠ 0) :
    T.mask (allocationColumnIdeal x) ≠ 0 := by
  have hleft : x.1.1 ≠ 0 := by
    intro hz
    exact hx (by simp only [allocationColumnIdeal, hz, zero_mul])
  have hright : x.1.2 ≠ 0 := by
    intro hz
    exact hx (by simp only [allocationColumnIdeal, hz, mul_zero, zero_mul])
  simp only [rawBareSourceCoefficient, FixedChildCharacters.bareCoefficient,
    childCartesianCoefficient, sourcePlainCoefficient, sourcePrimeCoefficient,
    mul_ne_zero_iff, Finset.prod_ne_zero_iff] at hc
  have hm₁ : T.mask x.1.1 ≠ 0 := by
    simpa only [sourceMomentIdeal_val_of_ne_zero _ hleft] using hc.1.1.2.1.2
  have hm₂ : T.mask x.1.2 ≠ 0 := by
    simpa only [sourceMomentIdeal_val_of_ne_zero _ hright] using hc.1.2.2.1.2
  have hms (j : Fin k) : T.mask (x.2 j).asIdeal ≠ 0 :=
    (hc.2 j (Finset.mem_univ j)).2.1.2
  rw [allocationColumnIdeal, map_mul, map_mul, map_prod]
  exact mul_ne_zero (mul_ne_zero hm₁ hm₂)
    (Finset.prod_ne_zero_iff.mpr (fun j _ => hms j))

theorem table_mask_nonzero {k : ℕ} (d : OrdinaryAtomTable (K := K) k)
    (rectangle : Bool) (x : AllocationColumn K k)
    (hx : allocationColumnIdeal x ≠ 0) (hc : d.term rectangle x ≠ 0) :
    d.characters.mask (allocationColumnIdeal x) ≠ 0 := by
  exact bare_mask_nonzero d.characters (d.scale₁ rectangle) (d.scale₂ rectangle)
    d.base d.length (d.comparisonWeight rectangle) (d.rightWeight rectangle)
    d.slotWeight x hx ((mul_ne_zero_iff.mp hc).2)

end T3a

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

/-- A live raw packet already contains an original nonzero comparison
rectangle. Its selected occurrence remains in the whole Cartesian
support before the independent divisor allocation. -/
theorem exceptional_nonzero_left_rectangle (hpacket : packet.Realizes) :
    ∃ x ∈ packet.leftReindex.cartesian, ∃ rectangle : Bool,
      packet.originalLeftRectangle rectangle x ≠ 0 := by
  obtain ⟨h, hh, x, hx, hc⟩ := packet.live.2.1
  have hwhole : packet.leftWhole x ≠ 0 := by
    intro hz
    apply hc
    change packet.leftWhole x * _ * _ = 0
    rw [hz, zero_mul, zero_mul]
  have hx' : x ∈ packet.leftReindex.cartesian :=
    packet.ordinaryAllocation.val.leftColumns_subset hx
  rw [packet.leftWhole_eq_rectangle_sub hpacket x
    (packet.realizes_coefficient hpacket (packet.leftReindex.index x))] at hwhole
  refine ⟨x, hx', ?_⟩
  by_cases hfalse : packet.originalLeftRectangle false x = 0
  · refine ⟨true, ?_⟩
    intro htrue
    exact hwhole (by rw [hfalse, htrue, sub_self])
  · exact ⟨false, hfalse⟩

/-- The nonzero rectangle is inspected before the second common
support is extracted. Thus its complete original mask controls the
second common primes themselves, as required for exceptional recovery. -/
theorem exceptional_moving_support_coprime (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (i : Fin packet.block.primeCount) :
    IsCoprime (packet.R.primes i).val.asIdeal (phases.moving false).support.val := by
  obtain ⟨x, hx, rectangle, hrectangle⟩ :=
    packet.exceptional_nonzero_left_rectangle hpacket
  have hx' : x ∈ (packet.secondBranch false).residualColumns :=
    packet.leftReindex_cartesian ▸ hx
  let y := (packet.secondBranch false).reconstruct x
  have hterm : (packet.firstAtomTable hpacket phases false).term rectangle y ≠ 0 := by
    intro hz
    apply hrectangle
    rw [← packet.beforeAtomTable_left hpacket phases rectangle x hx,
      ← packet.beforeAtomTable_term hpacket phases false rectangle x hx']
    change packet.firstExternalScalar false *
      (packet.firstAtomTable hpacket phases false).term rectangle y = 0
    rw [hz, mul_zero]
  have hideal :
      (packet.second.physical.source.ideal (packet.leftReindex.index x)).val =
        allocationColumnIdeal y :=
    packet.secondColumn_ideal false x hx'
  have hy : allocationColumnIdeal y ≠ 0 := by
    rw [← hideal]
    exact (packet.second.physical.source.ideal (packet.leftReindex.index x)).property.1
  have hmask := T3a.table_mask_nonzero
    (packet.firstAtomTable hpacket phases false) rectangle y hy hterm
  have hcop : IsCoprime (allocationColumnIdeal y) (phases.mask false).val := by
    by_contra hn
    apply hmask
    change (if IsCoprime (allocationColumnIdeal y) (phases.mask false).val
      then (1 : ℂ) else 0) = 0
    exact if_neg hn
  have hmoving : IsCoprime (allocationColumnIdeal y)
      (phases.moving false).support.val := by
    change IsCoprime (allocationColumnIdeal y)
      (((phases.moving false).effectiveFullSupport
        call.localizedSource.source.recipe.remaining).val * phases.deletionIdeal.val) at hcop
    have hfull := (IsCoprime.mul_right_iff.mp hcop).1
    exact ((phases.moving false).fullMaskSupport_coprime_iff
      (remainingMaskIdeal (Arithmetic.data c) call.localizedSource.source.recipe.remaining)
      (allocationColumnIdeal y)).mp hfull |>.1
  have hcommon : (packet.R.primes i).val.asIdeal ∣ packet.block.commonLeftIdeal.val := by
    change (packet.block.primes i).val.asIdeal ∣
      ∏ j, (packet.block.primes j).val.asIdeal ^ packet.block.leftMultiplicity j
    exact (dvd_pow_self _ (packet.block.left_positive i).ne').trans
      (Finset.dvd_prod_of_mem
        (fun j => (packet.block.primes j).val.asIdeal ^ packet.block.leftMultiplicity j)
        (Finset.mem_univ i))
  have hdiv : (packet.R.primes i).val.asIdeal ∣ allocationColumnIdeal y := by
    rw [← hideal, packet.block.left_reconstruct _ _ (packet.leftReindex_mem_common x hx)]
    exact hcommon.trans (dvd_mul_right _ _)
  exact hmoving.of_isCoprime_of_dvd_left hdiv

end RawLeafPacket

namespace RawFamily

variable (trace : SourceTrace call p) (htrace : trace.Realizes)
variable {geometry : GeometryFamily trace.second} (raw : RawFamily geometry)

theorem packet_moving_unramified (j : Fin raw.count)
    (hpacket : (raw.packet j).Realizes) (i : Fin (raw.packet j).block.primeCount) :
    UnramifiedAt K (trace.expansion.moving (raw.index j).val.1.1).character
      ((raw.packet j).R.primes i).val := by
  rw [← OrdinaryPhaseFacts.ofRaw_moving_false trace htrace raw j]
  exact T3a.moving_unramified_of_coprime_support _ _
    ((HeckeAxiom.exteriorEquiv (Arithmetic.data c)
      (LocalFiniteSums.primeIdeal ((raw.packet j).R.primes i))).property
        ((raw.packet j).R.primes i).val dvd_rfl)
    ((raw.packet j).exceptional_moving_support_coprime hpacket
      (OrdinaryPhaseFacts.ofRaw trace htrace raw j) i)

end RawFamily

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3a.bare_mask_nonzero
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.exceptional_moving_support_coprime
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.packet_moving_unramified
