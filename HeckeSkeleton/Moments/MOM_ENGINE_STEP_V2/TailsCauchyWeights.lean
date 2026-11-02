import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsCauchyGeometry

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual first Cauchy outer weights

The canonical first row weight retains the inverse active norm. After
its genuine Gauss square root, that factor is at most one. The two
normalizations have the same total exponent; it cancels in their ratio.
Only the bounded common-ideal logarithms remain in the outer weight.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

theorem first_rowWeightBound_mul_sqrt_le
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)} [Γ.FiniteIndex]
    [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
    (r : OrbitalGaussColumn K S Γ)
    (radius : {r : ℝ // 0 < r}) (hradius : radius.val ≤ 1)
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (delta : ℝ) (hdelta : 0 ≤ delta) (hhalf : delta ≤ 1 / 2) :
    CanonicalFirstLog.rowWeightBound r radius D delta *
      Real.sqrt (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        ⟨r.modulus, r.nonzero⟩).val ≤
      orbitalFieldFactor K * radius.val⁻¹ := by
  have hN := one_le_sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
    ⟨r.modulus, r.nonzero⟩
  have hactive :
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        ⟨r.modulus, r.nonzero⟩).val ^ (delta - 1 / 2) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hN (show delta - 1 / 2 ≤ 0 by linarith)
  have hdilation : radius.val ≤
      (sIntegerMaskDilationRadius K S radius
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val := by
    change radius.val ≤ radius.val *
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val
    exact le_mul_of_one_le_right radius.property.le
      (one_le_sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) _)
  have hscale :
      (sIntegerMaskDilationRadius K S radius
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ^
          (delta - 1) ≤ radius.val⁻¹ := by
    calc
      _ ≤ radius.val ^ (delta - 1) :=
        Real.rpow_le_rpow_of_nonpos radius.property hdilation (by linarith)
      _ ≤ radius.val ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge radius.property hradius (by linarith)
      _ = _ := by rw [Real.rpow_neg radius.property.le, Real.rpow_one]
  rw [CanonicalFirstLog.rowWeightBound_mul_sqrt_eq]
  calc
    _ ≤ (orbitalFieldFactor K * radius.val⁻¹) * 1 :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hscale (orbitalFieldFactor_nonneg K)) hactive
        (Real.rpow_nonneg
          (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
            ⟨r.modulus, r.nonzero⟩).property.le _)
        (mul_nonneg (orbitalFieldFactor_nonneg K) (inv_nonneg.mpr radius.property.le))
    _ = _ := mul_one _

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem first_chart_weight_le
    (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset)
    (q : SIntegerOrbits K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (Arithmetic.unitSubgroup c)) :
    ‖(F.source.charts v D).weight q‖ ≤
      CanonicalFirstLog.rowWeightBound
        (actualActiveColumn (Arithmetic.units_are_sixth c) (Arithmetic.context c)
          (F.source.block v).primes (F.source.block v).primes_injective
          (F.source.block v).leftMultiplicity (F.source.block v).rightMultiplicity)
        F.source.radius D.val p.tilt := by
  letI : IsTotallyComplex K := Arithmetic.totallyComplex c
  letI : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ := borel _
  letI : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
  letI : ∀ v : ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))),
      MeasurableSpace (v.val.adicCompletion K)ˣ := fun _ => borel _
  letI : ∀ v : ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))),
      BorelSpace (v.val.adicCompletion K)ˣ := fun _ => ⟨rfl⟩
  have he := first_chart_project_eq F hF v D (fun _ chart => chart.weight)
  rw [he]
  exact FirstBlockProfileChart.canonicalLogWithCoefficients_weight_le
    (Arithmetic.units_are_sixth c) (Arithmetic.localMeasures (K := K))
    (Arithmetic.finiteMeasure (K := K)) (F.source.block v) (Arithmetic.context c)
    F.source.columns F.source.columns (CanonicalRowBall.archTest K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_locallyConstant K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_compactSupport K (Arithmetic.data c).Sf 1)
    F.source.radius D.val p.tilt p.tilt_pos p.tilt_half F.coefficient F.coefficient q

theorem first_piece_rowBound_le
    (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) :
    (F.source.pieces v D).rowBound ≤ orbitalFieldFactor K * call.base ^ (2 : ℝ) := by
  let b := F.source.block v
  let r := actualActiveColumn (Arithmetic.units_are_sixth c) (Arithmetic.context c)
    b.primes b.primes_injective b.leftMultiplicity b.rightMultiplicity
  let R := CanonicalFirstLog.rowWeightBound r F.source.radius D.val p.tilt
  have hR : 0 ≤ R := CanonicalFirstLog.rowWeightBound_nonneg r F.source.radius D.val p.tilt
  have hsup : ((F.source.source v).divisorRows D.val).sup
      (fun q => ‖(F.source.charts v D).weight q‖₊) ≤ (⟨R, hR⟩ : NNReal) := by
    apply Finset.sup_le
    intro q hq
    exact_mod_cast first_chart_weight_le F hF v D q
  have hweight : (F.source.pieces v D).weightBound ≤ R := by
    rw [hF.weight]
    exact_mod_cast hsup
  have hN := generates_sIntegerElementNorm
    (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
    (firstActiveGenerator (Arithmetic.context c) b.primes b.leftMultiplicity b.rightMultiplicity)
    (firstActiveGenerator_generates (Arithmetic.context c)
      b.primes b.leftMultiplicity b.rightMultiplicity)
  change (sIntegerElementNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨r.modulus, r.nonzero⟩).val =
    (Arithmetic.data c).exteriorNorm
      (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) at hN
  calc
    _ ≤ R * Real.sqrt ((Arithmetic.data c).exteriorNorm
        (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) :=
      mul_le_mul_of_nonneg_right hweight (Real.sqrt_nonneg _)
    _ = R * Real.sqrt
        (sIntegerElementNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
          ⟨r.modulus, r.nonzero⟩).val := by rw [hN]
    _ ≤ orbitalFieldFactor K * F.source.radius.val⁻¹ :=
      first_rowWeightBound_mul_sqrt_le r F.source.radius (first_radius_le_one F hF)
        D.val p.tilt p.tilt_pos.le p.tilt_half
    _ ≤ _ := mul_le_mul_of_nonneg_left (first_inverse_radius_le F hF)
      (orbitalFieldFactor_nonneg K)

theorem first_allowance_ratio_le (Z total B : ℝ) (hZ : 1 < Z)
    (I J : Ideal (𝓞 K))
    (hi0 : 0 ≤ idealLogLength Z I) (hj0 : 0 ≤ idealLogLength Z J)
    (hr0 : 0 ≤ idealLogLength Z (firstActiveRadical I J))
    (hi : idealLogLength Z I ≤ B) (hj : idealLogLength Z J ≤ B) (side : Bool) :
    Real.sqrt (firstLeftAllowance Z total I J) *
        Real.sqrt (firstRightAllowance Z total I J) /
      (if side then firstRightAllowance Z total I J else firstLeftAllowance Z total I J) ≤
        Z ^ B := by
  have hleft0 := firstAllowance_nonneg (idealLogLength Z I) (idealLogLength Z J)
    (idealLogLength Z (firstActiveRadical I J))
  have hright0 := firstAllowance_nonneg (idealLogLength Z J) (idealLogLength Z I)
    (idealLogLength Z (firstActiveRadical I J))
  have hleft : firstAllowance (idealLogLength Z I) (idealLogLength Z J)
      (idealLogLength Z (firstActiveRadical I J)) ≤ B / 2 := by
    unfold firstAllowance
    exact max_le (by linarith) (by linarith)
  have hright : firstAllowance (idealLogLength Z J) (idealLogLength Z I)
      (idealLogLength Z (firstActiveRadical I J)) ≤ B / 2 := by
    unfold firstAllowance
    exact max_le (by linarith) (by linarith)
  have hz : 0 < Z := zero_lt_one.trans hZ
  cases side <;>
    simp only [firstLeftAllowance, firstRightAllowance, Bool.false_eq_true, ↓reduceIte,
      Real.sqrt_eq_rpow, ← Real.rpow_mul hz.le, ← Real.rpow_add hz, ← Real.rpow_sub hz] <;>
    apply Real.rpow_le_rpow_of_exponent_le hZ.le <;> linarith

def firstOuterConstant (c : TargetContext K) (_p : SourceParameters c) : ℝ :=
  orbitalFieldFactor K

def firstOuterDegree (c : TargetContext K) (_p : SourceParameters c) : ℝ :=
  2 + carrierColumnExponent c

theorem firstOuterConstant_nonneg (c : TargetContext K) (p : SourceParameters c) :
    0 ≤ firstOuterConstant c p := orbitalFieldFactor_nonneg K

theorem firstOuterDegree_nonneg (c : TargetContext K) (p : SourceParameters c) :
    0 ≤ firstOuterDegree c p := by
  have h := carrierColumnExponent_nonneg c
  dsimp [firstOuterDegree]
  linarith

theorem first_key_outer_le
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hf : family.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (key : FirstCauchyKey F) :
    FirstCauchyKey.outer key family.normalization ≤
      firstOuterConstant c p * call.base ^ firstOuterDegree c p := by
  let NL := family.normalization.left key.1 key.2.1
    (FirstCauchyKey.residual key) (FirstCauchyKey.character key)
  let NR := family.normalization.right key.1 key.2.1
    (FirstCauchyKey.residual key) (FirstCauchyKey.character key)
  have hNL : 0 < NL := family.normalization.left_pos _ _ _ _
  have hNR : 0 < NR := family.normalization.right_pos _ _ _ _
  have hden : 0 < (if FirstCauchyKey.side key then NR else NL) := by
    split_ifs <;> assumption
  have hr0 : 0 ≤ Real.sqrt NL * Real.sqrt NR /
      (if FirstCauchyKey.side key then NR else NL) :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hden.le
  have hr : Real.sqrt NL * Real.sqrt NR /
      (if FirstCauchyKey.side key then NR else NL) ≤
        call.base ^ carrierColumnExponent c := by
    dsimp only [NL, NR]
    simp only [hf.leftAllowance, hf.rightAllowance]
    have hlen := first_common_lengths_le F hF input hlarge key.1
    have hzero := commonSupportPool_nonzero F.source.columns F.source.columns
      (fun i => (F.source.ideal i).val) (fun j => (F.source.ideal j).val)
      key.1.val key.1.property
    exact first_allowance_ratio_le call.base _ (carrierColumnExponent c)
      call.domain.scale key.1.val.1 key.1.val.2
      (idealLogLength_nonneg call.base call.domain.scale _ hzero.1)
      (idealLogLength_nonneg call.base call.domain.scale _ hzero.2)
      (idealLogLength_nonneg call.base call.domain.scale _ (firstActiveRadical_ne_zero _ _))
      hlen.1 hlen.2 (FirstCauchyKey.side key)
  have hmu : ‖(moebius (FirstCauchyKey.residual key).val : ℂ)‖ ≤ 1 := by
    unfold moebius
    split_ifs <;> simp
  have hphase := fixed_phase_coefficient_norm PUnit (fun _ => (1 : Circle))
    (FirstCauchyKey.character key)
  have hfinite : ‖(moebius (FirstCauchyKey.residual key).val : ℂ)‖ *
      ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle))
        (FirstCauchyKey.character key)‖ ≤ 1 :=
    (mul_le_mul hmu hphase (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hrow : (FirstCauchyKey.piece key).rowBound / 2 ≤
      orbitalFieldFactor K * call.base ^ (2 : ℝ) := by
    have hw := first_piece_rowBound_le F hF key.1 key.2.1
    have hnonneg := (FirstCauchyKey.piece key).rowBound_nonneg
    linarith
  have he : FirstCauchyKey.outer key family.normalization =
      (‖(moebius (FirstCauchyKey.residual key).val : ℂ)‖ *
        ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle))
          (FirstCauchyKey.character key)‖) *
      ((FirstCauchyKey.piece key).rowBound / 2) *
      (Real.sqrt NL * Real.sqrt NR /
        (if FirstCauchyKey.side key then NR else NL)) := by
    dsimp only [FirstCauchyKey.outer, NL, NR]
    rw [hF.fiber]
    simp only [Nat.cast_one, one_mul]
    ring
  calc
    _ = _ := he
    _ ≤ (1 * (orbitalFieldFactor K * call.base ^ (2 : ℝ))) *
        call.base ^ carrierColumnExponent c :=
      mul_le_mul
        (mul_le_mul hfinite hrow
          (div_nonneg (FirstCauchyKey.piece key).rowBound_nonneg (by norm_num))
          zero_le_one) hr hr0
        (mul_nonneg zero_le_one
          (mul_nonneg (orbitalFieldFactor_nonneg K) (Real.rpow_nonneg call.base_pos.le _)))
    _ = _ := by
      dsimp [firstOuterConstant, firstOuterDegree]
      rw [Real.rpow_add call.base_pos]
      ring

theorem first_family_outer_le
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hf : family.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (i : Fin family.count) :
    (family.source i).outerWeight ≤ firstOuterConstant c p * call.base ^ firstOuterDegree c p := by
  rw [hf.outer i]
  exact first_key_outer_le F hF family hf input hlarge (family.index i)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_piece_rowBound_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_family_outer_le
