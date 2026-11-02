import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedCanonical
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationOrigin
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalOrbitFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The canonical refinement retains the original orbit fibres

The actual nonunit pattern was fixed before the row Cauchy step.
Consequently an extracted ideal determines the original ideal, whose
orbit fibre has at most the fixed sixth-unit subgroup index.  The
passive allocation and both comparison rectangles leave that row map
unchanged.  No finite-fibre estimate is a task input.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

namespace N8Normalized

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι] [IsPrincipalIdealRing A.R]
variable (R : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS)

theorem nonunitRadical_eq_pattern (h : H) :
    nonunitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity
      (R.frequency h) =
    primePowerProduct R.primes (fun i =>
      if actualNonunitPattern C R.primes R.leftMultiplicity R.rightMultiplicity
        (R.frequency h) i then 1 else 0) := by
  simp only [nonunitFrequencyRadical, actualNonunitPattern, decide_eq_true_eq]

theorem extracted_fibres_of_nonunit (N : Ideal (𝓞 K))
    (hnonunit : ∀ h : R.live,
      (nonunitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity
        (R.frequency h.val)).val = N)
    (bound : ℕ)
    (hbound : ∀ I : Ideal (𝓞 K),
      (R.rows.filter (fun h => (R.originalIdeal h).val = I)).card ≤ bound)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((Finset.univ : Finset R.live).filter
      (fun h => (R.extractedRow C h).momentIdeal = I)).card ≤ bound := by
  let T : Finset R.live := Finset.univ.filter
    (fun h => (R.extractedRow C h).momentIdeal = I)
  let J : Ideal (𝓞 K) :=
    gcd (primePowerProduct R.primes R.leftMultiplicity).val
      (primePowerProduct R.primes R.rightMultiplicity).val * N * I.val
  have hm : T.image Subtype.val ⊆ R.rows.filter
      (fun h => (R.originalIdeal h).val = J) := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hh
    have hi : (R.extractedRow C x).ideal.val = I.val :=
      congrArg (fun J : HeckeGeneral.Analysis.NonzeroIdeal K => J.val) (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp x.property).1, ?_⟩
    rw [R.extractedRow_ideal_factor C x, hnonunit x, hi]
  calc
    _ = (T.image Subtype.val).card :=
      (Finset.card_image_of_injective T Subtype.val_injective).symm
    _ ≤ (R.rows.filter (fun h => (R.originalIdeal h).val = J)).card := Finset.card_le_card hm
    _ ≤ bound := hbound J

/-- Extracting the fixed nonunit ideal does not increase the number of
original rows of a given ideal.  Only the actual finite pattern and the
original ideal map enter this finite combinatorial argument. -/
theorem extracted_fibres_of_pattern (pattern : ι → Bool)
    (hpattern : ∀ h : R.live,
      actualNonunitPattern C R.primes R.leftMultiplicity R.rightMultiplicity
        (R.frequency h.val) = pattern)
    (bound : ℕ)
    (hbound : ∀ I : Ideal (𝓞 K),
      (R.rows.filter (fun h => (R.originalIdeal h).val = I)).card ≤ bound)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((Finset.univ : Finset R.live).filter
      (fun h => (R.extractedRow C h).momentIdeal = I)).card ≤ bound := by
  let T : Finset R.live := Finset.univ.filter
    (fun h => (R.extractedRow C h).momentIdeal = I)
  let N := primePowerProduct R.primes (fun i => if pattern i then 1 else 0)
  let J : Ideal (𝓞 K) :=
    gcd (primePowerProduct R.primes R.leftMultiplicity).val
      (primePowerProduct R.primes R.rightMultiplicity).val * N.val * I.val
  have hnonunit (h : R.live) :
      nonunitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity
        (R.frequency h.val) = N := by
    rw [nonunitRadical_eq_pattern R C h.val, hpattern h]
  have hm : T.image Subtype.val ⊆ R.rows.filter
      (fun h => (R.originalIdeal h).val = J) := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hh
    have hi : (R.extractedRow C x).ideal.val = I.val :=
      congrArg (fun J : HeckeGeneral.Analysis.NonzeroIdeal K => J.val) (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp x.property).1, ?_⟩
    rw [R.extractedRow_ideal_factor C x, hnonunit x, hi]
    rfl
  calc
    _ = (T.image Subtype.val).card :=
      (Finset.card_image_of_injective T Subtype.val_injective).symm
    _ ≤ (R.rows.filter (fun h => (R.originalIdeal h).val = J)).card := Finset.card_le_card hm
    _ ≤ bound := hbound J

end N8Normalized

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p}

namespace OrdinaryData

variable (O : OrdinaryData packet)

theorem originalSource_rows (side rectangle : Bool) :
    (O.originalSource side rectangle).rows = Finset.univ := by
  cases side <;> rfl

theorem originalSource_row_momentIdeal (side rectangle : Bool) (h : O.rows.live) :
    ((O.originalSource side rectangle).row h).momentIdeal =
      (O.rows.extractedRow (Arithmetic.context c) h).momentIdeal := by
  cases side <;> rfl

theorem original_rows_fibres (I : Ideal (𝓞 K)) :
    (O.rows.rows.filter (fun h => (O.rows.originalIdeal h).val = I)).card ≤
      (Arithmetic.unitSubgroup c).index :=
  finite_original_orbit_ideal_fibre_le_index (Arithmetic.data c)
    (Arithmetic.unitSubgroup c) O.rows.rows I

theorem originalSource_fibres (pattern : Fin packet.block.primeCount → Bool)
    (hpattern : ∀ h : packet.R.live,
      actualNonunitPattern (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val) = pattern)
    (side rectangle : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((O.originalSource side rectangle).rows.filter
      (fun h => ((O.originalSource side rectangle).row h).momentIdeal = I)).card ≤
      (Arithmetic.unitSubgroup c).index := by
  rw [O.originalSource_rows]
  simp_rw [O.originalSource_row_momentIdeal]
  apply N8Normalized.extracted_fibres_of_pattern O.rows (Arithmetic.context c)
    pattern ?_ (Arithmetic.unitSubgroup c).index O.original_rows_fibres I
  intro h
  let h' : packet.R.live := ⟨h.val, Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp h.property).1).1,
      (Finset.mem_filter.mp h.property).2⟩⟩
  exact hpattern h'

theorem originalSource_fibres_realized (hpacket : packet.Realizes)
    (side rectangle : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((O.originalSource side rectangle).rows.filter
      (fun h => ((O.originalSource side rectangle).row h).momentIdeal = I)).card ≤
      (Arithmetic.unitSubgroup c).index := by
  rw [O.originalSource_rows]
  simp_rw [O.originalSource_row_momentIdeal]
  apply N8Normalized.extracted_fibres_of_nonunit O.rows (Arithmetic.context c)
    (packet.nominal false).ideals.nonunitPart.val ?_
    (Arithmetic.unitSubgroup c).index O.original_rows_fibres I
  intro h
  exact (packet.realized_nonunitPart hpacket false (O.originalLiveRow h)).symm

end OrdinaryData

namespace OrdinarySeed

variable (seed : OrdinarySeed packet) (input : ProfileInput call)
variable (support : seed.ordinary.PassiveSupport input)

theorem canonicalSource_fibreCost_bound (pattern : Fin packet.block.primeCount → Bool)
    (hpattern : ∀ h : packet.R.live,
      actualNonunitPattern (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val) = pattern)
    (side : Bool) (a : support.labels side) (rectangle : Bool) :
    SourceCost.fiber (seed.canonicalSource input support side a rectangle) ≤
      (Arithmetic.unitSubgroup c).index := by
  apply SourceCost.fiber_le
  intro I
  exact seed.ordinary.originalSource_fibres pattern hpattern side false I

theorem canonicalSource_fibreCost_realized (hpacket : packet.Realizes)
    (side : Bool) (a : support.labels side) (rectangle : Bool) :
    SourceCost.fiber (seed.canonicalSource input support side a rectangle) ≤
      (Arithmetic.unitSubgroup c).index := by
  apply SourceCost.fiber_le
  intro I
  exact seed.ordinary.originalSource_fibres_realized hpacket side false I

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Normalized.extracted_fibres_of_pattern
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData.original_rows_fibres
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.canonicalSource_fibreCost_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.canonicalSource_fibreCost_realized
