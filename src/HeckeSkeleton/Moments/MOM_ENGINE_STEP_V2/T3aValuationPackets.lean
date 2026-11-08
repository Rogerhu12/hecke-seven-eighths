module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aValuations
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aBaseCount
public import HeckeSkeleton.ExpansionModels.ActualRowEligibility

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original exceptional theta membership supplies the local character relation

The original theta family and the original recipe correction are
unramified outside the unchanged set of bad places. Removing those
factors and the actual unramified moving prefix leaves precisely the
active second factor times the actual complete residual-row character.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

namespace Call

variable {c : TargetContext K} (call : Call c)

theorem theta_unramified (θ : HeckeCharacter K) (hθ : θ ∈ call.node.data.theta)
    (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ places K c) :
    UnramifiedAt K θ q := by
  apply actualCanonicalTheta_unramified K c θ
  · rw [← call.source.source.theta_eq]
    exact hθ
  · exact hq

theorem correction_unramified (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∉ places K c) :
    UnramifiedAt K call.localizedSource.source.recipe.correction q := by
  rcases call.localizedSource.source.recipe.correction_mem PUnit.unit with h | h
  · rw [h]
    exact unramifiedAt_one K q
  · apply actualCanonicalTheta_unramified K c _
    · exact (congrArg
        (fun theta : Finset (HeckeCharacter K) =>
          call.localizedSource.source.recipe.correction ∈ theta)
        call.localizedSource.source.theta_eq).mp h
    · exact hq

end Call

private theorem unramified_append_product
    {A : SArithmeticData K}
    {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
    {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
    (correction : HeckeCharacter K) (D E : OriginalMovingFactors A P R)
    (χ : HeckeCharacter K) (q : HeightOneSpectrum (𝓞 K))
    (hprefix : UnramifiedAt K (correction * D.character) q)
    (hfull : UnramifiedAt K (correction * (D.append E).character * χ) q) :
    UnramifiedAt K (E.character * χ) q := by
  apply T3a.unramified_product_of_unramified_prefix
    (correction * D.character) E.character χ q hprefix
  simpa only [OriginalMovingFactors.append_character, mul_assoc] using hfull

namespace RawFamily

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family} {second : SecondFamily expansion}
variable {geometry : GeometryFamily second} (raw : RawFamily geometry)

/-- This uses the literal exceptional predicate of the raw leaf. The
remaining local premise is proved from its nonzero original coefficients. -/
theorem packet_original_count_dvd_six_of_moving_unramified
    (j : Fin raw.count) (h : (raw.packet j).R.live)
    (hh : h ∈ (raw.packet j).exceptionalRows)
    (i : Fin (raw.packet j).block.primeCount)
    (hi : i ∈ multiplicityOneNonunitPrimes (Arithmetic.context c)
      (raw.packet j).R.primes (raw.packet j).R.leftMultiplicity
      (raw.packet j).R.rightMultiplicity ((raw.packet j).R.frequency h.val))
    (hmoving : UnramifiedAt K
      (expansion.moving (raw.index j).val.1.1).character
      ((raw.packet j).R.primes i).val) :
    6 ∣ (normalizedFactors ((raw.packet j).R.originalIdeal h.val).val).count
      ((raw.packet j).R.primes i).val.asIdeal := by
  have hmem := (raw.packet_exceptional_character j h).mp
    (Finset.mem_filter.mp hh).2.1
  have hout : ((raw.packet j).R.primes i).val ∉ places K c :=
    (HeckeAxiom.exteriorEquiv (Arithmetic.data c)
      (primeIdeal ((raw.packet j).R.primes i))).property
        ((raw.packet j).R.primes i).val dvd_rfl
  have hfull := call.theta_unramified _ hmem
    ((raw.packet j).R.primes i).val hout
  have hlive : h.val ∈
      ((second.source (raw.index j).val.1.1).rows
        (raw.index j).val.1.2.1 (raw.index j).val.1.2.2.1
        (SourceClassKey.rowLabel (raw.index j).val.1.2)).live :=
    h.property
  simp only [SecondSource.rowCharacter, dif_pos hlive] at hfull
  have hprefix := (call.correction_unramified
    ((raw.packet j).R.primes i).val hout).mul K hmoving
  apply T3a.actualSecondRow_original_exponent_dvd_six
    (probeData K c) (momentRowCharacters K c) (Arithmetic.context c)
    (raw.packet j).R h i hi
  apply unramified_append_product
    (A := Arithmetic.data c) (P := probeData K c) (R := momentRowCharacters K c)
    call.localizedSource.source.recipe.correction
    (expansion.moving (raw.index j).val.1.1) _ _ _ hprefix
  exact hfull

end RawFamily

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Call.theta_unramified
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.packet_original_count_dvd_six_of_moving_unramified
