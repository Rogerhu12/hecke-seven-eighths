module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstCauchyContracts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstLogBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstAllowanceNormalization

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original first Poisson weight and both Cauchy allowances

The first realization fixes the weight as the actual finite supremum
of the canonical logarithmic chart. Its pointwise bound therefore
bounds that very supremum. The resulting first active saving is then
carried through the literal weighted-Cauchy outer scalar, with the two
original positive allowances retained separately.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

open EngineStep
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

def firstActiveOrbitalColumn (F : FirstPresentation call p) (v : F.source.CommonLabel) :=
  actualActiveColumn (Arithmetic.units_are_sixth c) (Arithmetic.context c)
    (F.source.block v).primes (F.source.block v).primes_injective
    (F.source.block v).leftMultiplicity (F.source.block v).rightMultiplicity

def firstWeightMajorant (F : FirstPresentation call p) (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) : ℝ :=
  CanonicalFirstLog.rowWeightBound (firstActiveOrbitalColumn F v)
    F.source.radius D.val p.tilt

def firstRowMajorant (F : FirstPresentation call p) (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) : ℝ :=
  orbitalFieldFactor K *
    (sIntegerMaskDilationRadius K (Arithmetic.data c).Sf F.source.radius
      (sIntegerMaskGenerator K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        D.val)).val ^ (p.tilt - 1) *
    ((Arithmetic.data c).exteriorNorm
      (firstActiveIdeal (F.source.block v).primes
        (F.source.block v).leftMultiplicity (F.source.block v).rightMultiplicity)) ^
      (p.tilt - 1 / 2)

theorem canonicalFirst_weight (F : FirstPresentation call p)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset)
    (q : Arithmetic.Orbit c) :
    (F.canonicalChart v D).weight q =
      CanonicalFirstLog.poissonTiltWeight (firstActiveOrbitalColumn F v)
        F.source.radius D.val p.tilt q := rfl

theorem realizedFirst_weight (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset)
    (q : Arithmetic.Orbit c) :
    (F.source.charts v D).weight q =
      CanonicalFirstLog.poissonTiltWeight (firstActiveOrbitalColumn F v)
        F.source.radius D.val p.tilt q := by
  let Chart := fun profiles : F.source.Column → F.source.Column →
      SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ =>
    FirstBlockProfileChart (E := ℝ) (Arithmetic.units_are_sixth c)
      (Arithmetic.localMeasures (K := K)) (F.source.block v)
      (Arithmetic.context c) F.source.columns F.source.columns profiles
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) F.source.radius D.val
  have hpairs : (⟨F.source.profiles, F.source.charts v D⟩ : Sigma Chart) =
      (⟨F.originalProfile, F.canonicalChart v D⟩ : Sigma Chart) :=
    Sigma.ext hF.profile (hF.chart v D)
  have hweight := congrArg (fun x : Sigma Chart => x.2.weight q) hpairs
  exact hweight.trans (canonicalFirst_weight F v D q)

/-- The bound is for the actual prescribed finite supremum. -/
theorem realizedFirst_weightBound_le (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset) :
    (F.source.pieces v D).weightBound ≤ firstWeightMajorant F v D := by
  rw [hF.weight v D]
  let B : NNReal := ⟨firstWeightMajorant F v D,
    CanonicalFirstLog.rowWeightBound_nonneg _ _ _ _⟩
  have hsup : ((F.source.source v).divisorRows D.val).sup
      (fun q => ‖(F.source.charts v D).weight q‖₊) ≤ B := by
    apply Finset.sup_le
    intro q _
    change ‖(F.source.charts v D).weight q‖ ≤ firstWeightMajorant F v D
    rw [realizedFirst_weight F hF v D q]
    exact CanonicalFirstLog.norm_poissonTiltWeight_le _ _ _ p.tilt p.tilt_pos.le q
  exact hsup

/-- The genuine active Gauss factor leaves exponent tilt minus one half. -/
theorem realizedFirst_rowBound_le (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset) :
    (F.source.pieces v D).rowBound ≤ firstRowMajorant F v D := by
  let b := F.source.block v
  let r := firstActiveOrbitalColumn F v
  have hN := generates_sIntegerElementNorm
    (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
    (firstActiveGenerator (Arithmetic.context c) b.primes b.leftMultiplicity b.rightMultiplicity)
    (firstActiveGenerator_generates (Arithmetic.context c) b.primes
      b.leftMultiplicity b.rightMultiplicity)
  change (sIntegerElementNorm K
    ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨r.modulus, r.nonzero⟩).val =
    (Arithmetic.data c).exteriorNorm
      (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) at hN
  calc
    _ ≤ firstWeightMajorant F v D * Real.sqrt
        ((Arithmetic.data c).exteriorNorm
          (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) :=
      mul_le_mul_of_nonneg_right (realizedFirst_weightBound_le F hF v D)
        (Real.sqrt_nonneg _)
    _ = _ := by
      unfold firstWeightMajorant firstRowMajorant
      rw [← hN]
      exact CanonicalFirstLog.rowWeightBound_mul_sqrt_eq r F.source.radius D.val p.tilt

/-- The original physical radius and the actual first divisor give
this exponent without any additional profile-window assumption. -/
def firstRowExponent (F : FirstPresentation call p) (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) : ℝ :=
  (idealLogLength call.base (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val -
      call.workingParameters.m) * (p.tilt - 1) +
    idealLogLength call.base (firstActiveRadical v.val.1 v.val.2) * (p.tilt - 1 / 2)

theorem realizedFirst_rowMajorant_eq_rpow (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset) :
    firstRowMajorant F v D = orbitalFieldFactor K * call.base ^ firstRowExponent F v D := by
  have hd := generates_sIntegerElementNorm
    (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val)
    (sIntegerMaskGenerator K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      D.val).val
    (originalFrequencyIdeal_generates _ (sIntegerMaskGenerator K
      ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).property)
  change (sIntegerElementNorm K
      ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        D.val)).val =
    (Ideal.absNorm (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val : ℝ) at hd
  have hd' : (sIntegerElementNorm K
      ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        D.val)).val =
      call.base ^ idealLogLength call.base
        (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val :=
    hd.trans (rpow_idealLogLength call.base call.domain.scale _
      (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).property.1).symm
  have ha : (Arithmetic.data c).exteriorNorm
      (firstActiveIdeal (F.source.block v).primes (F.source.block v).leftMultiplicity
        (F.source.block v).rightMultiplicity) =
      call.base ^ idealLogLength call.base (firstActiveRadical v.val.1 v.val.2) :=
    (F.source.block v).activeNorm_eq.trans
      (rpow_idealLogLength call.base call.domain.scale _
        (firstActiveRadical_ne_zero v.val.1 v.val.2)).symm
  unfold firstRowMajorant firstRowExponent
  change orbitalFieldFactor K *
      (F.source.radius.val * (sIntegerElementNorm K
        ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
          D.val)).val) ^ (p.tilt - 1) *
      ((Arithmetic.data c).exteriorNorm
        (firstActiveIdeal (F.source.block v).primes (F.source.block v).leftMultiplicity
          (F.source.block v).rightMultiplicity)) ^ (p.tilt - 1 / 2) = _
  rw [hF.radius, hd', ha, ← Real.rpow_add call.base_pos,
    ← Real.rpow_mul call.base_pos.le, ← Real.rpow_mul call.base_pos.le,
    mul_assoc, ← Real.rpow_add call.base_pos]
  congr 1
  congr 1
  ring

theorem realizedFirst_rowBound_le_rpow (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset) :
    (F.source.pieces v D).rowBound ≤ orbitalFieldFactor K * call.base ^ firstRowExponent F v D :=
  (realizedFirst_rowBound_le F hF v D).trans_eq
    (realizedFirst_rowMajorant_eq_rpow F hF v D)

/-- Keep the scalar inequality independent of the dependent source
carriers, so the original outer coefficient needs only one application. -/
private theorem firstCauchy_outer_scalar_le
    (fiber : ℕ) (mu phase row majorant left right : ℝ) (side : Bool)
    (hfiber : fiber = 1) (hmu : mu ≤ 1) (hphase : phase ≤ 1)
    (hphase_nonneg : 0 ≤ phase) (hrow : 0 ≤ row) (hmajorant : row ≤ majorant)
    (hleft : 0 < left) (hright : 0 < right) :
    (fiber : ℝ) * mu * phase * (row * Real.sqrt left * Real.sqrt right / 2) /
        (if side then right else left) ≤
      (majorant * Real.sqrt left * Real.sqrt right / 2) /
        (if side then right else left) := by
  rw [hfiber, Nat.cast_one, one_mul]
  have hunit : mu * phase ≤ 1 := by
    simpa only [one_mul] using
      mul_le_mul hmu hphase hphase_nonneg zero_le_one
  have hden : 0 < if side then right else left := by
    split_ifs
    · exact hright
    · exact hleft
  have hweight : 0 ≤ row * Real.sqrt left * Real.sqrt right / 2 :=
    div_nonneg
      (mul_nonneg (mul_nonneg hrow (Real.sqrt_nonneg left))
        (Real.sqrt_nonneg right)) (by norm_num)
  apply div_le_div_of_nonneg_right _ hden.le
  calc
    _ ≤ 1 * (row * Real.sqrt left * Real.sqrt right / 2) :=
      mul_le_mul_of_nonneg_right hunit hweight
    _ = row * Real.sqrt left * Real.sqrt right / 2 := one_mul _
    _ ≤ majorant * Real.sqrt left * Real.sqrt right / 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmajorant (Real.sqrt_nonneg left))
          (Real.sqrt_nonneg right)) (by norm_num)

/-- The original weighted-Cauchy coefficient, before substituting the
specific allowances. Its Mobius and finite-phase norms are at most one. -/
theorem firstCauchy_outer_le {F : FirstPresentation call p} (hF : F.Realizes)
    (key : FirstCauchyKey F) (N : F.source.Normalization) :
    FirstCauchyKey.outer key N ≤
      (firstRowMajorant F key.1 key.2.1 *
        Real.sqrt (N.left key.1 key.2.1 (FirstCauchyKey.residual key)
          (FirstCauchyKey.character key)) *
        Real.sqrt (N.right key.1 key.2.1 (FirstCauchyKey.residual key)
          (FirstCauchyKey.character key)) / 2) /
        (if FirstCauchyKey.side key then
          N.right key.1 key.2.1 (FirstCauchyKey.residual key) (FirstCauchyKey.character key)
        else N.left key.1 key.2.1 (FirstCauchyKey.residual key)
          (FirstCauchyKey.character key)) := by
  exact firstCauchy_outer_scalar_le F.source.fiber
    ‖(moebius (FirstCauchyKey.residual key).val : ℂ)‖
    ‖fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle))
      (FirstCauchyKey.character key)‖
    (FirstCauchyKey.piece key).rowBound (firstRowMajorant F key.1 key.2.1)
    (N.left key.1 key.2.1 (FirstCauchyKey.residual key) (FirstCauchyKey.character key))
    (N.right key.1 key.2.1 (FirstCauchyKey.residual key) (FirstCauchyKey.character key))
    (FirstCauchyKey.side key) hF.fiber
    (norm_ideal_moebius_le_one (FirstCauchyKey.residual key).val)
    (fixed_phase_coefficient_norm PUnit.{1} (fun _ => (1 : Circle))
      (FirstCauchyKey.character key))
    (norm_nonneg _) (FirstCauchyKey.piece key).rowBound_nonneg
    (realizedFirst_rowBound_le F hF key.1 key.2.1)
    (N.left_pos _ _ _ _) (N.right_pos _ _ _ _)

def firstAllowanceTotal (F : FirstPresentation call p) (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) : ℝ :=
  call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z +
    call.workingParameters.q + idealLogLength call.base (firstActiveRadical v.val.1 v.val.2) +
    idealLogLength call.base (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val

theorem realizedFirstCauchy_outer_le {F : FirstPresentation call p} (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes) (i : Fin family.count) :
    let key := family.index i
    let total := firstAllowanceTotal F key.1 key.2.1
    let NL := firstLeftAllowance call.base total key.1.val.1 key.1.val.2
    let NR := firstRightAllowance call.base total key.1.val.1 key.1.val.2
    (family.source i).outerWeight ≤
      (firstRowMajorant F key.1 key.2.1 * Real.sqrt NL * Real.sqrt NR / 2) /
        (if FirstCauchyKey.side key then NR else NL) := by
  rw [hfamily.outer i]
  have h := firstCauchy_outer_le hF (family.index i) family.normalization
  simpa only [hfamily.leftAllowance, hfamily.rightAllowance, firstAllowanceTotal] using h

/-- Restoring the selected allowance cancels its original Cauchy
denominator. Both allowance square roots remain in the numerator. -/
theorem realizedFirstCauchy_outer_mul_allowance_le
    {F : FirstPresentation call p} (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes) (i : Fin family.count) :
    let key := family.index i
    let total := firstAllowanceTotal F key.1 key.2.1
    let NL := firstLeftAllowance call.base total key.1.val.1 key.1.val.2
    let NR := firstRightAllowance call.base total key.1.val.1 key.1.val.2
    (family.source i).outerWeight * (if FirstCauchyKey.side key then NR else NL) ≤
      (orbitalFieldFactor K * call.base ^ firstRowExponent F key.1 key.2.1 *
        Real.sqrt NL * Real.sqrt NR / 2) := by
  have hbound := realizedFirstCauchy_outer_le hF family hfamily i
  dsimp only at hbound ⊢
  rw [realizedFirst_rowMajorant_eq_rpow F hF] at hbound
  have hden : 0 < if FirstCauchyKey.side (family.index i) then
      firstRightAllowance call.base
        (firstAllowanceTotal F (family.index i).1 (family.index i).2.1)
        (family.index i).1.val.1 (family.index i).1.val.2
    else firstLeftAllowance call.base
        (firstAllowanceTotal F (family.index i).1 (family.index i).2.1)
        (family.index i).1.val.1 (family.index i).1.val.2 := by
    split_ifs
    · exact firstRightAllowance_pos _ _ call.base_pos _ _
    · exact firstLeftAllowance_pos _ _ call.base_pos _ _
  exact (le_div_iff₀ hden).mp hbound

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.realizedFirst_weightBound_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.realizedFirst_rowBound_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.realizedFirst_rowBound_le_rpow
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.realizedFirstCauchy_outer_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.realizedFirstCauchy_outer_mul_allowance_le
