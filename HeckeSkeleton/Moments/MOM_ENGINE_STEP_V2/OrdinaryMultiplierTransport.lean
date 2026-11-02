import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryDivisorGate
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryPhaseFacts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryNormPower

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The exact first and one-pool scalar on each original source column

The old inverse norm cancels against the pool's original Gauss norm.
The resulting denominator is the actual residual norm. Reciprocity
identifies the pool column phase with the fixed original prime-power
element, retaining all residue zeros. The original first divisor gate
is opened only on the active second common class.
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

namespace OrdinaryMultiplierTransport

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (C : A.GeneralArithmeticContext σ η hS)

def poolElement (pool : Option (AmplifierValuation × ExteriorPrime A)) : A.R :=
  match pool with
  | none => 1
  | some (e, q) => LocalFiniteSums.generator C q ^ (2 * e.multiplicity)

def formula (tilt : ℝ) (power : A.Exterior) (first : A.R) (I : A.Exterior)
    (pool : Option (AmplifierValuation × ExteriorPrime A)) : ℂ :=
  ((((A.exteriorNorm power ^ tilt : ℝ) : ℂ) *
      ((A.exteriorNorm I ^ tilt : ℝ) : ℂ)) / (A.exteriorNorm I : ℂ)) *
    actualIdealResidue (A := A) (σ := σ) power.val first *
    actualIdealResidue (A := A) (σ := σ) I.val first *
    actualIdealResidue (A := A) (σ := σ) I.val (poolElement C pool)

theorem formula_none (tilt : ℝ) (first : A.R) (I : A.Exterior) :
    formula C tilt (unitExterior A) first I none =
      (((A.exteriorNorm I ^ tilt : ℝ) : ℂ) / (A.exteriorNorm I : ℂ)) *
        actualIdealResidue (A := A) (σ := σ) I.val first := by
  have hunit : A.exteriorNorm (unitExterior A) = 1 := by
    change (Ideal.absNorm (⊤ : Ideal (𝓞 K)) : ℝ) = 1
    simp only [Ideal.absNorm_top, Nat.cast_one]
  have hval : (unitExterior A).val = 1 := Ideal.one_eq_top.symm
  simp only [formula, poolElement, hunit, hval, Real.one_rpow, Complex.ofReal_one,
    one_mul, actualIdealResidue_one, actualIdealResidue_frequency_one, mul_one]

/-- The two original tilts combine with the one original inverse norm.
The fixed pool norm and first residue stay as one explicit scalar. -/
theorem formula_mul_second (tilt : ℝ) (power : A.Exterior) (first unit : A.R)
    (I : A.Exterior) (pool : Option (AmplifierValuation × ExteriorPrime A)) :
    formula C tilt power first I pool *
        (((A.exteriorNorm I ^ tilt : ℝ) : ℂ) *
          actualIdealResidue (A := A) (σ := σ) I.val unit) =
      (((A.exteriorNorm power ^ tilt : ℝ) : ℂ) *
          actualIdealResidue (A := A) (σ := σ) power.val first) *
        ((A.exteriorNorm I ^ (-1 + 2 * tilt) : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) I.val first *
        actualIdealResidue (A := A) (σ := σ) I.val (poolElement C pool) *
        actualIdealResidue (A := A) (σ := σ) I.val unit := by
  rw [OrdinaryNormPower.two_tilts_complex _ _ (A.exteriorNorm_pos I)]
  unfold formula
  ring

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

/-- The pool cancellation uses the nonzero norm of this exact original
column, before the second transform or any triangle inequality. -/
theorem residualCoefficient_formula (d : FirstGaussPoolData C P ι)
    (q : ExteriorPrime A) (e : AmplifierValuation) (tilt : ℝ) (first : A.R)
    (m : ι → ℂ) (i : d.valuationColumns q e.multiplicity)
    (hm : m i.val =
      (((A.exteriorNorm (d.ideal i.val) ^ tilt : ℝ) : ℂ) /
        (A.exteriorNorm (d.ideal i.val) : ℂ)) *
        actualIdealResidue (A := A) (σ := σ) (d.ideal i.val).val first) :
    d.residualCoefficient q e.multiplicity m i =
      formula C tilt (powerIdeal q e.multiplicity) first
        (d.residualPresentation q e.multiplicity i).residual (some (e, q)) := by
  have hN : (A.exteriorNorm (d.ideal i.val) : ℂ) ≠ 0 := by
    exact_mod_cast (A.exteriorNorm_pos (d.ideal i.val)).ne'
  have hcancel :
      ((((A.exteriorNorm (d.ideal i.val) ^ tilt : ℝ) : ℂ) /
          (A.exteriorNorm (d.ideal i.val) : ℂ)) *
        actualIdealResidue (A := A) (σ := σ) (d.ideal i.val).val first) *
          (A.exteriorNorm (d.ideal i.val) : ℂ) =
      ((A.exteriorNorm (d.ideal i.val) ^ tilt : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (d.ideal i.val).val first := by
    field_simp [hN] <;> ring
  have hnorm : A.exteriorNorm (d.ideal i.val) =
      A.exteriorNorm (powerIdeal q e.multiplicity) *
        A.exteriorNorm (d.residualPresentation q e.multiplicity i).residual := by
    change (Ideal.absNorm (d.ideal i.val).val : ℝ) = _
    rw [(d.residualPresentation q e.multiplicity i).reconstructed, map_mul, Nat.cast_mul]
    rfl
  unfold FirstGaussPoolData.residualCoefficient FirstGaussPoolData.adjustedCoefficient
  rw [hm, hcancel, AmplifierResidualPresentation.columnPhase_eq_residue,
    hnorm, Real.mul_rpow (A.exteriorNorm_pos _).le (A.exteriorNorm_pos _).le,
    Complex.ofReal_mul, (d.residualPresentation q e.multiplicity i).reconstructed,
    actualIdealResidue_ideal_mul]
  unfold formula poolElement
  rw [show (powerIdeal q e.multiplicity).val =
    q.val.asIdeal ^ e.multiplicity from rfl]
  ring

def TagMatches (tag : OriginalNominalTag K)
    (pool : Option (AmplifierValuation × ExteriorPrime A)) : Prop :=
  match pool with
  | none => tag = .direct ∨ tag = .main
  | some (e, q) => tag = .error e q.val

/-- The recorded original tag fixes the actual optional prime; the
proof of exteriority adds no choice to that prime. -/
theorem pool_eq_of_tag {tag : OriginalNominalTag K}
    {a b : Option (AmplifierValuation × ExteriorPrime A)}
    (ha : TagMatches tag a) (hb : TagMatches tag b) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      rcases b with ⟨e, q⟩
      rcases ha with ha | ha
      · cases ha.symm.trans hb
      · cases ha.symm.trans hb
  | some a =>
    rcases a with ⟨ea, qa⟩
    cases b with
    | none =>
      rcases hb with hb | hb
      · cases hb.symm.trans ha
      · cases hb.symm.trans ha
    | some b =>
      rcases b with ⟨eb, qb⟩
      have he := ha.symm.trans hb
      injection he with he hq
      exact congrArg Option.some (Prod.ext he (Subtype.ext hq))

end OrdinaryMultiplierTransport

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace OrdinaryMultiplierTransport

private theorem tagMatches_of_phaseFacts {source : PhysicalSource call p}
    {first : (Arithmetic.data c).R}
    {pool : Option (AmplifierValuation × ExteriorPrime (Arithmetic.data c))}
    (facts : OrdinaryPhaseFacts.PhaseFacts source first pool) :
    TagMatches source.first.tag pool := by
  cases pool with
  | none => exact facts.tag
  | some ep =>
    rcases ep with ⟨e, q⟩
    exact facts.tag

private theorem tagMatches_of_phaseData {packet : RawLeafPacket call p}
    (phases : OriginalPhaseData packet) :
    TagMatches packet.second.physical.first.tag phases.pool := by
  have h := phases.pool_tag
  cases hp : phases.pool with
  | none => simpa only [TagMatches, hp] using h
  | some ep =>
    rcases ep with ⟨e, q⟩
    simpa only [TagMatches, hp] using h

end OrdinaryMultiplierTransport

namespace PhysicalSource

variable (source : PhysicalSource call p)

def MultiplierRealizes
    (pool : Option (AmplifierValuation × ExteriorPrime (Arithmetic.data c))) : Prop :=
  ∀ i, source.first.residualDivisor.val ∣ (source.source.ideal i).val →
    source.multiplier i = OrdinaryMultiplierTransport.formula (Arithmetic.context c) p.tilt
      source.first.poolPower source.first.firstElement (source.source.ideal i) pool

theorem multiplierRealizes_of_transport {ι : Type}
    (G : ActualGaussSource (Arithmetic.context c) ι) (m : ι → ℂ)
    (D : Ideal (𝓞 K)) (first : (Arithmetic.data c).R)
    (power : (Arithmetic.data c).Exterior)
    (pool : Option (AmplifierValuation × ExteriorPrime (Arithmetic.data c)))
    (column : source.Column = ι) (hsource : HEq source.source G)
    (hmultiplier : HEq source.multiplier m)
    (hdivisor : source.first.residualDivisor.val = D)
    (hfirst : source.first.firstElement = first) (hpower : source.first.poolPower = power)
    (hformula : ∀ i, D ∣ (G.ideal i).val →
      m i = OrdinaryMultiplierTransport.formula (Arithmetic.context c) p.tilt
        power first (G.ideal i) pool) : source.MultiplierRealizes pool := by
  subst ι
  have hs := eq_of_heq hsource
  have hm := eq_of_heq hmultiplier
  intro i hd
  rw [hs, hdivisor] at hd
  rw [hm, hs, hfirst, hpower]
  exact hformula i hd

end PhysicalSource

namespace FirstCauchyFamily

variable {F : FirstPresentation call p} (family : FirstCauchyFamily F)

theorem multiplierRealizes (hfamily : family.Realizes) (i : Fin family.count) :
    (family.source i).MultiplierRealizes none := by
  apply (family.source i).multiplierRealizes_of_transport
    ((FirstCauchyKey.data (family.index i)).directSource
      (FirstCauchyKey.coefficient (family.index i)))
    (FirstCauchyKey.multiplier (family.index i))
    (FirstCauchyKey.residual (family.index i)).val
    (FirstCauchyKey.firstElement (family.index i)) (unitExterior (Arithmetic.data c)) none
    (hfamily.column i) (hfamily.source i) (hfamily.multiplier i)
    (hfamily.residual i) (hfamily.firstElement i) (hfamily.poolPower i)
  intro j hj
  rw [OrdinaryMultiplierTransport.formula_none]
  exact FirstCauchyKey.multiplier_eq_residue (family.index i) j hj

end FirstCauchyFamily

namespace PoolPresentation

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable (P : PoolPresentation family)

theorem main_multiplierRealizes (hP : P.Realizes) (i : Fin family.count)
    (source : PhysicalSource call p) (horigin : P.MainOrigin i source)
    (hfirst : (family.source i).MultiplierRealizes none) :
    source.MultiplierRealizes none := by
  rcases horigin with ⟨hcolumn, hsource, hancestor, hmultiplier, hkernel,
    hpoint, houter, hcoordinates⟩
  apply source.multiplierRealizes_of_transport
    ((P.data i).mainSource (family.source i).source.coefficient)
    (family.source i).multiplier (family.source i).first.residualDivisor.val
    (family.source i).first.firstElement (family.source i).first.poolPower none
    hcolumn hsource hmultiplier
    (by simpa only using congrArg (fun f : FirstCoordinates call => f.residualDivisor.val) hcoordinates)
    (by simpa only using congrArg (fun f : FirstCoordinates call => f.firstElement) hcoordinates)
    (by simpa only using congrArg (fun f : FirstCoordinates call => f.poolPower) hcoordinates)
  intro j hj
  have hideal := congrArg (fun G : ActualGaussSource (Arithmetic.context c) (family.source i).Column => G.ideal j) (hP.original i)
  change (P.data i).ideal j = _ at hideal
  change (family.source i).first.residualDivisor.val ∣ ((P.data i).ideal j).val at hj
  change (family.source i).multiplier j = OrdinaryMultiplierTransport.formula _ _ _ _
    ((P.data i).ideal j) _
  rw [hideal] at hj ⊢
  exact hfirst j hj

theorem error_multiplierRealizes (hP : P.Realizes) (i : Fin family.count)
    (q : P.pool.primes) (e : AmplifierValuation)
    (source : PhysicalSource call p) (horigin : P.ErrorOrigin i q e source)
    (hpower : (family.source i).first.poolPower = unitExterior (Arithmetic.data c))
    (hfirst : (family.source i).MultiplierRealizes none) :
    source.MultiplierRealizes (some (e, q.val)) := by
  rcases horigin with ⟨hcolumn, hsource, hancestor, hmultiplier, hkernel,
    hpoint, houter, hselected, hopposite, hcomplementary, hresidual,
    helement, hright, hpool, hretained, htag, hdeletion, hpaid⟩
  apply source.multiplierRealizes_of_transport
    ((P.data i).residualSource q.val e.multiplicity (family.source i).source.coefficient)
    ((P.data i).residualCoefficient q.val e.multiplicity (family.source i).multiplier)
    (family.source i).first.residualDivisor.val (family.source i).first.firstElement
    (powerIdeal q.val e.multiplicity) (some (e, q.val))
    hcolumn hsource hmultiplier (congrArg Subtype.val hresidual) helement hpool
  intro j hj
  apply OrdinaryMultiplierTransport.residualCoefficient_formula (Arithmetic.context c)
    (P.data i) q.val e p.tilt (family.source i).first.firstElement
    (family.source i).multiplier j
  have hideal := congrArg (fun G : ActualGaussSource (Arithmetic.context c) (family.source i).Column => G.ideal j.val) (hP.original i)
  change (P.data i).ideal j.val = _ at hideal
  have hd : (family.source i).first.residualDivisor.val ∣
      ((family.source i).source.ideal j.val).val := by
    rw [← hideal, ((P.data i).residualPresentation q.val e.multiplicity j).reconstructed]
    exact hj.trans (dvd_mul_left _ _)
  have hm := hfirst j.val hd
  rw [hpower, OrdinaryMultiplierTransport.formula_none, ← hideal] at hm
  exact hm

end PoolPresentation

namespace PoolExpansion

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable (expansion : PoolExpansion family)

theorem multiplierRealizes
    (hfirst : ∀ i, (family.source i).MultiplierRealizes none)
    (hpower : ∀ i, (family.source i).first.poolPower = unitExterior (Arithmetic.data c))
    (hexpansion : expansion.Realizes) (i : Fin expansion.count) :
    (expansion.source i).MultiplierRealizes (OrdinaryPhaseFacts.poolOption expansion i) := by
  cases expansion with
  | direct => exact hfirst i
  | pooled P count index source =>
    have horigin := hexpansion.2.2 i
    cases hi : (index i).2 with
    | inl u =>
      change (source i).MultiplierRealizes _
      simp only [OrdinaryPhaseFacts.poolOption, hi]
      apply P.main_multiplierRealizes hexpansion.2.1 (index i).1 (source i) _
        (hfirst (index i).1)
      simpa only [PoolPresentation.Origin, hi] using horigin
    | inr qe =>
      change (source i).MultiplierRealizes _
      simp only [OrdinaryPhaseFacts.poolOption, hi]
      apply P.error_multiplierRealizes hexpansion.2.1 (index i).1 qe.1 qe.2 (source i) _
        (hpower (index i).1) (hfirst (index i).1)
      simpa only [PoolPresentation.Origin, hi] using horigin

end PoolExpansion

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem realizes_multiplier (hpacket : packet.Realizes) (phases : OriginalPhaseData packet) :
    packet.second.physical.MultiplierRealizes phases.pool := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  have hphysical := htrace.second.physical (raw.index j).val.1.1
  have htag : OrdinaryMultiplierTransport.TagMatches (raw.packet j).second.physical.first.tag
      (OrdinaryPhaseFacts.poolOption trace.expansion (raw.index j).val.1.1) := by
    change OrdinaryMultiplierTransport.TagMatches
      (trace.second.source (raw.index j).val.1.1).physical.first.tag _
    rw [hphysical]
    exact OrdinaryMultiplierTransport.tagMatches_of_phaseFacts
      (OrdinaryPhaseFacts.phase_facts htrace.cauchy trace.expansion
        htrace.expansion (raw.index j).val.1.1)
  have hpool := OrdinaryMultiplierTransport.pool_eq_of_tag
    (OrdinaryMultiplierTransport.tagMatches_of_phaseData phases) htag
  rw [hpool]
  change (trace.second.source (raw.index j).val.1.1).physical.MultiplierRealizes _
  rw [hphysical]
  exact trace.expansion.multiplierRealizes (trace.cauchy.multiplierRealizes htrace.cauchy)
    htrace.cauchy.poolPower htrace.expansion (raw.index j).val.1.1

theorem secondDivisor_eq_empty (hpacket : packet.Realizes) : packet.key.2.1.val = ∅ := by
  have hs := Finset.mem_powerset.mp packet.key.2.1.property
  have he := congrArg (fun mask : Finset (Ideal (𝓞 K)) => packet.key.2.1.val ⊆ mask)
    (packet.realizes_second hpacket).mask
  exact Finset.subset_empty.mp (he.mp hs)

theorem leftSecondMultiplier_eq_residue (hpacket : packet.Realizes)
    (i : AllocationColumn K packet.leaf.leftSlots) (hi : i ∈ packet.leftReindex.cartesian) :
    packet.leftSecondMultiplier (packet.leftReindex.index i) =
      (((Arithmetic.data c).exteriorNorm
        (packet.second.physical.source.ideal (packet.leftReindex.index i)) ^ p.tilt : ℝ) : ℂ) *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          (packet.second.physical.source.ideal (packet.leftReindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := Arithmetic.data c)) := by
  unfold leftSecondMultiplier
  rw [packet.secondDivisor_eq_empty hpacket,
    CanonicalLiteralFixedPhases.generated_empty_divisorPhase,
    packet.block.secondLeftIdeal_eq _ _ (packet.leftReindex_mem_common i hi)]

theorem rightSecondMultiplier_eq_residue (hpacket : packet.Realizes)
    (i : AllocationColumn K packet.leaf.rightSlots) (hi : i ∈ packet.rightReindex.cartesian) :
    packet.rightSecondMultiplier (packet.rightReindex.index i) =
      (((Arithmetic.data c).exteriorNorm
        (packet.second.physical.source.ideal (packet.rightReindex.index i)) ^ p.tilt : ℝ) : ℂ) *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          (packet.second.physical.source.ideal (packet.rightReindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := Arithmetic.data c)) := by
  unfold rightSecondMultiplier
  rw [packet.secondDivisor_eq_empty hpacket,
    CanonicalLiteralFixedPhases.generated_empty_divisorPhase,
    packet.block.secondRightIdeal_eq _ _ (packet.rightReindex_mem_common i hi)]

/-- The actual left coefficient has exactly its original two tilts,
one inverse norm, and three fixed residues before occurrence extraction. -/
theorem leftMultiplier_eq_residues (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet)
    (i : AllocationColumn K packet.leaf.leftSlots) (hi : i ∈ packet.leftReindex.cartesian) :
    packet.second.physical.multiplier (packet.leftReindex.index i) *
        packet.leftSecondMultiplier (packet.leftReindex.index i) =
      packet.poolScalar *
        (((Arithmetic.data c).exteriorNorm
          (packet.second.physical.source.ideal (packet.leftReindex.index i)) ^
            (-1 + 2 * p.tilt) : ℝ) : ℂ) *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          (packet.second.physical.source.ideal (packet.leftReindex.index i)).val
          packet.second.physical.first.firstElement *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          (packet.second.physical.source.ideal (packet.leftReindex.index i)).val
          (OrdinaryMultiplierTransport.poolElement (Arithmetic.context c) phases.pool) *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          (packet.second.physical.source.ideal (packet.leftReindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := Arithmetic.data c)) := by
  rw [(packet.realizes_multiplier hpacket phases) (packet.leftReindex.index i)
    (packet.residualDivisor_dvd_left hpacket i hi), packet.leftSecondMultiplier_eq_residue hpacket i hi]
  exact OrdinaryMultiplierTransport.formula_mul_second (Arithmetic.context c) p.tilt
    packet.second.physical.first.poolPower packet.second.physical.first.firstElement
    (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := Arithmetic.data c))
    (packet.second.physical.source.ideal (packet.leftReindex.index i)) phases.pool

/-- The same scalar operation applies to each right rectangle before
its later complex conjugation; none of the three residues is discarded. -/
theorem rightMultiplier_eq_residues (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet)
    (i : AllocationColumn K packet.leaf.rightSlots) (hi : i ∈ packet.rightReindex.cartesian) :
    packet.second.physical.multiplier (packet.rightReindex.index i) *
        packet.rightSecondMultiplier (packet.rightReindex.index i) =
      packet.poolScalar *
        (((Arithmetic.data c).exteriorNorm
          (packet.second.physical.source.ideal (packet.rightReindex.index i)) ^
            (-1 + 2 * p.tilt) : ℝ) : ℂ) *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          (packet.second.physical.source.ideal (packet.rightReindex.index i)).val
          packet.second.physical.first.firstElement *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          (packet.second.physical.source.ideal (packet.rightReindex.index i)).val
          (OrdinaryMultiplierTransport.poolElement (Arithmetic.context c) phases.pool) *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          (packet.second.physical.source.ideal (packet.rightReindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := Arithmetic.data c)) := by
  rw [(packet.realizes_multiplier hpacket phases) (packet.rightReindex.index i)
    (packet.residualDivisor_dvd_right hpacket i hi), packet.rightSecondMultiplier_eq_residue hpacket i hi]
  exact OrdinaryMultiplierTransport.formula_mul_second (Arithmetic.context c) p.tilt
    packet.second.physical.first.poolPower packet.second.physical.first.firstElement
    (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := Arithmetic.data c))
    (packet.second.physical.source.ideal (packet.rightReindex.index i)) phases.pool

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryMultiplierTransport.residualCoefficient_formula
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.realizes_multiplier
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.leftMultiplier_eq_residues
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.rightMultiplier_eq_residues
