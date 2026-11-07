module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S3ExpansionData

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original arithmetic data for one earlier prime pool

This constructor adds only the finite CRT support and the original
row/frozen norm bookkeeping. It changes no source row or coefficient.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support
open HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

def primeFactors {A : SArithmeticData K} (I : A.Exterior) :
    Finset (ExteriorPrime A) :=
  (primeSupport I.val).attach.image (exteriorPrimeOfSupport I)

theorem mem_primeFactors {A : SArithmeticData K} (I : A.Exterior)
    (q : ExteriorPrime A) (hq : MaskedQuotientCRT.primeExponent q I ≠ 0) :
    q ∈ primeFactors I := by
  have hd : q.val.asIdeal ∣ I.val := by
    by_contra hn
    exact hq (primeExponent_zero_of_not_dvd I q hn)
  have hs : q.val.asIdeal ∈ primeSupport I.val :=
    (prime_mem_support_iff_dvd _ _ q.val.prime I.property.1).mpr hd
  refine Finset.mem_image.mpr
    ⟨⟨q.val.asIdeal, hs⟩, Finset.mem_attach _ _, ?_⟩
  apply Subtype.ext
  apply HeightOneSpectrum.asIdeal_injective
  rfl

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem rowSize_one (source : PhysicalSource call p) : 1 ≤ source.rowSize :=
  le_max_left _ _

theorem rowExponent_nonneg (source : PhysicalSource call p) :
    0 ≤ source.rowExponent :=
  div_nonneg (Real.log_nonneg (rowSize_one source))
    (Real.log_pos call.domain.scale).le

theorem rpow_rowExponent (source : PhysicalSource call p) :
    call.base ^ source.rowExponent = source.rowSize := by
  have hlog : Real.log call.base ≠ 0 := (Real.log_pos call.domain.scale).ne'
  have he : Real.log call.base *
      (Real.log source.rowSize / Real.log call.base) = Real.log source.rowSize := by
    field_simp [hlog]
  rw [PhysicalSource.rowExponent, Real.rpow_def_of_pos call.base_pos, he,
    Real.exp_log (zero_lt_one.trans_le (rowSize_one source))]

theorem row_norm (source : PhysicalSource call p)
    (h : (Arithmetic.data c).R) (hh : h ∈ source.source.rows) :
    (Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h) ≤
      call.base ^ source.rowExponent := by
  rw [rpow_rowExponent]
  apply le_trans _ (le_max_right _ _)
  exact_mod_cast Finset.le_sup (f := fun h =>
    (⟨(Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h),
      ((Arithmetic.data c).exteriorNorm_pos (originalFrequencyIdeal h)).le⟩ : NNReal)) hh

def support (source : PhysicalSource call p)
    (primes : Finset (ExteriorPrime (Arithmetic.data c))) :
    Finset (ExteriorPrime (Arithmetic.data c)) :=
  (source.source.columns.biUnion fun i => primeFactors (source.source.ideal i)) ∪
    (source.source.rows.biUnion fun h => primeFactors (originalFrequencyIdeal h)) ∪ primes

def poolData (source : PhysicalSource call p)
    (pool : PowerScaleExteriorPool (Arithmetic.data c) ∅ call.base
      (recipeInductionSigma c / 3) p.loss)
    (hdensity : 0 < pool.rowDensity source.rowExponent
      (idealLogLength call.base source.first.residualDivisor.val)) :
    FirstGaussPoolData (Arithmetic.context c) pool source.Column where
  columns := source.source.columns
  ideal := source.source.ideal
  generator := source.source.generator
  generates := source.source.generates
  allowed := source.source.allowed
  rows := source.source.rows
  rowIdeal := originalFrequencyIdeal
  row_generates h hh := originalFrequencyIdeal_generates h (source.source.row_nonzero h hh)
  support := support source pool.primes
  column_support i hi q hq :=
    Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨i, hi, mem_primeFactors _ q hq⟩))
  row_support h hh q hq :=
    Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨h, hh, mem_primeFactors _ q hq⟩))
  pool_support := Finset.subset_union_right
  frozen := source.first.residualDivisor.val
  frozen_ne_zero := nonZeroDivisors.coe_ne_zero source.first.residualDivisor
  rowExponent := source.rowExponent
  frozenExponent := idealLogLength call.base source.first.residualDivisor.val
  rowExponent_nonneg := rowExponent_nonneg source
  row_norm := row_norm source
  frozen_norm := (rpow_idealLogLength call.base call.domain.scale _
    (nonZeroDivisors.coe_ne_zero source.first.residualDivisor)).symm.le
  density_pos := hdensity

theorem poolData_original (source : PhysicalSource call p)
    (pool : PowerScaleExteriorPool (Arithmetic.data c) ∅ call.base
      (recipeInductionSigma c / 3) p.loss)
    (hdensity : 0 < pool.rowDensity source.rowExponent
      (idealLogLength call.base source.first.residualDivisor.val)) :
    (poolData source pool hdensity).directSource source.source.coefficient =
      source.source := rfl

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

def presentation
    (pool : PowerScaleExteriorPool (Arithmetic.data c) ∅ call.base
      (recipeInductionSigma c / 3) p.loss)
    (hdensity : ∀ i, call.base ^ (recipeInductionSigma c / 3 - 2 * p.loss) ≤
      pool.rowDensity (family.source i).rowExponent
        (idealLogLength call.base (family.source i).first.residualDivisor.val)) :
    PoolPresentation family where
  pool := pool
  data i := poolData (family.source i) pool
    ((Real.rpow_pos_of_pos call.base_pos _).trans_le (hdensity i))

theorem presentation_realizes
    (pool : PowerScaleExteriorPool (Arithmetic.data c) ∅ call.base
      (recipeInductionSigma c / 3) p.loss)
    (hdensity : ∀ i, call.base ^ (recipeInductionSigma c / 3 - 2 * p.loss) ≤
      pool.rowDensity (family.source i).rowExponent
        (idealLogLength call.base (family.source i).first.residualDivisor.val)) :
    (presentation pool hdensity).Realizes where
  original i := poolData_original _ _ _
  rowIdeal _ := rfl
  frozen _ := rfl
  rowExponent _ := rfl
  frozenExponent _ := rfl
  density i := hdensity i

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3
