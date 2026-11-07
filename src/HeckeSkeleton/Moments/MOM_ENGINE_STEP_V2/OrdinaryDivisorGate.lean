module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryLeafLocations

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original first divisor survives the one pool on every live source

An eligible pool prime does not divide the frozen first divisor. Thus
removing its entire prime power preserves divisibility by that divisor.
Nonzero coefficients on the active second common class then open the
original gate throughout both complete Cartesian column supports.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

namespace OrdinaryDivisorGate

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

theorem errorRows_not_dvd_frozen (d : FirstGaussPoolData C P ι)
    (q : ExteriorPrime A) (hrows : (d.errorRows q).Nonempty) :
    ¬q.val.asIdeal ∣ d.frozen := by
  obtain ⟨h, hh⟩ := hrows
  have he := (Finset.mem_filter.mp hh).2
  change ¬q.val.asIdeal ∣ (d.rowIdeal h).val ∧ ¬q.val.asIdeal ∣ d.frozen at he
  exact he.2

theorem residual_divisor (d : FirstGaussPoolData C P ι)
    (q : ExteriorPrime A) (n : ℕ) (D : Ideal (𝓞 K))
    (hnot : ¬q.val.asIdeal ∣ D) (i : d.valuationColumns q n)
    (hdiv : D ∣ (d.ideal i.val).val) :
    D ∣ (d.residualPresentation q n i).residual.val := by
  have hcop : IsCoprime q.val.asIdeal D := by
    rw [Ideal.isCoprime_iff_sup_eq]
    have hmax : q.val.asIdeal.IsMaximal := q.val.isPrime.isMaximal q.val.ne_bot
    exact hmax.out.2 _ (lt_of_le_of_ne le_sup_left (fun he =>
      hnot (Ideal.dvd_iff_le.mpr (sup_eq_left.mp he.symm))))
  have hpow : IsCoprime D (q.val.asIdeal ^ n) := by
    simpa only [pow_one] using (hcop.symm.pow : IsCoprime (D ^ 1) (q.val.asIdeal ^ n))
  apply hpow.dvd_of_dvd_mul_left
  rwa [← (d.residualPresentation q n i).reconstructed]

theorem residualCoefficient_nonzero (d : FirstGaussPoolData C P ι)
    (q : ExteriorPrime A) (n : ℕ) (f : ι → ℂ) (i : d.valuationColumns q n)
    (hi : d.residualCoefficient q n f i ≠ 0) : f i.val ≠ 0 := by
  intro hz
  exact hi (by simp only [FirstGaussPoolData.residualCoefficient,
    FirstGaussPoolData.adjustedCoefficient, hz, zero_mul, zero_div])

end OrdinaryDivisorGate

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace PhysicalSource

variable (source : PhysicalSource call p)

def DivisorRealizes : Prop := ∀ i ∈ source.source.columns,
  source.source.coefficient i ≠ 0 →
    source.first.residualDivisor.val ∣ (source.source.ideal i).val

theorem rows_eq_of_transport {ι : Type}
    (G : ActualGaussSource (Arithmetic.context c) ι)
    (column : source.Column = ι) (hsource : HEq source.source G) :
    source.source.rows = G.rows := by
  subst ι
  exact congrArg ActualGaussSource.rows (eq_of_heq hsource)

theorem divisorRealizes_of_transport {ι : Type}
    (G : ActualGaussSource (Arithmetic.context c) ι) (D : Ideal (𝓞 K))
    (column : source.Column = ι) (hsource : HEq source.source G)
    (hdivisor : source.first.residualDivisor.val = D)
    (hdiv : ∀ i ∈ G.columns, G.coefficient i ≠ 0 → D ∣ (G.ideal i).val) :
    source.DivisorRealizes := by
  subst ι
  have hs := eq_of_heq hsource
  intro i hi hc
  rw [hs] at hi hc ⊢
  rw [hdivisor]
  exact hdiv i hi hc

end PhysicalSource

namespace FirstCauchyFamily

variable {F : FirstPresentation call p} (family : FirstCauchyFamily F)

theorem divisorRealizes (hfamily : family.Realizes) (i : Fin family.count) :
    (family.source i).DivisorRealizes := by
  apply (family.source i).divisorRealizes_of_transport
    ((FirstCauchyKey.data (family.index i)).directSource
      (FirstCauchyKey.coefficient (family.index i)))
    (FirstCauchyKey.residual (family.index i)).val
    (hfamily.column i) (hfamily.source i) (hfamily.residual i)
  intro j _ hc
  exact FirstCauchyKey.coefficient_nonzero_divisor (family.index i) j hc

end FirstCauchyFamily

namespace PoolPresentation

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable (P : PoolPresentation family)

theorem main_divisorRealizes (hP : P.Realizes) (i : Fin family.count)
    (source : PhysicalSource call p) (horigin : P.MainOrigin i source)
    (hfirst : (family.source i).DivisorRealizes) : source.DivisorRealizes := by
  rcases horigin with ⟨hcolumn, hsource, hancestor, hmultiplier, hkernel,
    hpoint, houter, hcoordinates⟩
  apply source.divisorRealizes_of_transport
    ((P.data i).mainSource (family.source i).source.coefficient)
    (family.source i).first.residualDivisor.val hcolumn hsource
    (by simpa only using congrArg (fun f : FirstCoordinates call => f.residualDivisor.val) hcoordinates)
  intro j hj hc
  have hideal := congrArg (fun G : ActualGaussSource (Arithmetic.context c) (family.source i).Column => G.ideal j) (hP.original i)
  have hcolumns := congrArg ActualGaussSource.columns (hP.original i)
  change (P.data i).ideal j = _ at hideal
  change (P.data i).columns = _ at hcolumns
  change (family.source i).first.residualDivisor.val ∣ ((P.data i).ideal j).val
  rw [hideal]
  exact hfirst j (hcolumns ▸ hj) hc

theorem error_divisorRealizes (hP : P.Realizes) (i : Fin family.count)
    (q : P.pool.primes) (e : AmplifierValuation)
    (source : PhysicalSource call p) (horigin : P.ErrorOrigin i q e source)
    (hfirst : (family.source i).DivisorRealizes)
    (hrows : source.source.rows.Nonempty) : source.DivisorRealizes := by
  rcases horigin with ⟨hcolumn, hsource, hancestor, hmultiplier, hkernel,
    hpoint, houter, hselected, hopposite, hcomplementary, hresidual,
    helement, hright, hpool, hretained, htag, hdeletion, hpaid⟩
  have herror : ((P.data i).errorRows q.val).Nonempty := by
    rwa [source.rows_eq_of_transport _ hcolumn hsource] at hrows
  have hnot := OrdinaryDivisorGate.errorRows_not_dvd_frozen (P.data i) q.val herror
  rw [hP.frozen i] at hnot
  apply source.divisorRealizes_of_transport
    ((P.data i).residualSource q.val e.multiplicity (family.source i).source.coefficient)
    (family.source i).first.residualDivisor.val hcolumn hsource
    (congrArg Subtype.val hresidual)
  intro j _ hc
  apply OrdinaryDivisorGate.residual_divisor (P.data i) q.val e.multiplicity
    (family.source i).first.residualDivisor.val hnot j
  have hideal := congrArg (fun G : ActualGaussSource (Arithmetic.context c) (family.source i).Column => G.ideal j.val) (hP.original i)
  have hcolumns := congrArg ActualGaussSource.columns (hP.original i)
  change (P.data i).ideal j.val = _ at hideal
  change (P.data i).columns = _ at hcolumns
  rw [hideal]
  exact hfirst j.val (hcolumns ▸ (Finset.mem_filter.mp j.property).1)
    (OrdinaryDivisorGate.residualCoefficient_nonzero (P.data i) q.val e.multiplicity
      (family.source i).source.coefficient j hc)

end PoolPresentation

namespace PoolExpansion

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable (expansion : PoolExpansion family)

theorem divisorRealizes (hfirst : ∀ i, (family.source i).DivisorRealizes)
    (hexpansion : expansion.Realizes) (i : Fin expansion.count)
    (hrows : (expansion.source i).source.rows.Nonempty) :
    (expansion.source i).DivisorRealizes := by
  cases expansion with
  | direct => exact hfirst i
  | pooled P count index source =>
    have horigin := hexpansion.2.2 i
    cases hi : (index i).2 with
    | inl u =>
      apply P.main_divisorRealizes hexpansion.2.1 (index i).1 (source i) _
        (hfirst (index i).1)
      simpa only [PoolPresentation.Origin, hi] using horigin
    | inr qe =>
      apply P.error_divisorRealizes hexpansion.2.1 (index i).1 qe.1 qe.2 (source i) _
        (hfirst (index i).1) hrows
      simpa only [PoolPresentation.Origin, hi] using horigin

end PoolExpansion

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem realizes_divisor (hpacket : packet.Realizes) :
    packet.second.physical.DivisorRealizes := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  have hphysical := htrace.second.physical (raw.index j).val.1.1
  have hrows := (raw.packet j).physicalRows
  change (trace.second.source (raw.index j).val.1.1).physical.source.rows.Nonempty at hrows
  change (trace.second.source (raw.index j).val.1.1).physical.DivisorRealizes
  rw [hphysical] at hrows ⊢
  exact trace.expansion.divisorRealizes (trace.cauchy.divisorRealizes htrace.cauchy)
    htrace.expansion _ hrows

theorem residualDivisor_dvd_common (hpacket : packet.Realizes) :
    packet.second.physical.first.residualDivisor.val ∣ packet.key.1.val.1 ∧
      packet.second.physical.first.residualDivisor.val ∣ packet.key.1.val.2 :=
  packet.second.physical.residualDivisor_dvd_activeCommon
    (packet.realizes_divisor hpacket) packet.key.1.val (packet.realizes_activeCommon hpacket)

theorem residualDivisor_dvd_left (hpacket : packet.Realizes)
    (i : AllocationColumn K packet.leaf.leftSlots) (hi : i ∈ packet.leftReindex.cartesian) :
    packet.second.physical.first.residualDivisor.val ∣
      (packet.second.physical.source.ideal (packet.leftReindex.index i)).val := by
  rw [packet.block.left_reconstruct _ _ (packet.leftReindex_mem_common i hi),
    packet.block.common_left]
  exact (packet.residualDivisor_dvd_common hpacket).1.trans (dvd_mul_right _ _)

theorem residualDivisor_dvd_right (hpacket : packet.Realizes)
    (i : AllocationColumn K packet.leaf.rightSlots) (hi : i ∈ packet.rightReindex.cartesian) :
    packet.second.physical.first.residualDivisor.val ∣
      (packet.second.physical.source.ideal (packet.rightReindex.index i)).val := by
  rw [packet.block.right_reconstruct _ _ (packet.rightReindex_mem_common i hi),
    packet.block.common_right]
  exact (packet.residualDivisor_dvd_common hpacket).2.trans (dvd_mul_right _ _)

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.realizes_divisor
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.residualDivisor_dvd_left
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.residualDivisor_dvd_right
