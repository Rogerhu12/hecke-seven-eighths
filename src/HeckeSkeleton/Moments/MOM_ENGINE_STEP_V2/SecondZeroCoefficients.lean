module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroStage
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroProfileBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifierResidualSupport

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The literal coefficients entering the second signed zero

The first chart contributes its original inverse residual norm and
small logarithmic tilt. All finite reciprocal character factors have
norm at most one. The prime-pool correction preserves the product of
the coefficient norm and its actual residual ideal norm exactly.
These are identities and bounds on the original columns, before the
second transform or any diagonal summation.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

section FiniteFactors

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}

theorem firstLeftDivisorFactor_norm_le_one
    (a r : OrbitalGaussColumn K S Γ)
    (δ : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) :
    ‖firstLeftDivisorFactor a r δ‖ ≤ 1 := by
  letI := finite_sIntegerPrincipalResidue K
    (S : Set (HeightOneSpectrum (𝓞 K))) a.modulus a.nonzero
  letI := finite_sIntegerPrincipalResidue K
    (S : Set (HeightOneSpectrum (𝓞 K))) r.modulus r.nonzero
  letI := Fintype.ofFinite ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸
    Ideal.span {a.modulus})
  letI := Fintype.ofFinite ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸
    Ideal.span {r.modulus})
  rw [firstLeftDivisorFactor, norm_mul, norm_mul]
  exact (mul_le_mul
    (mul_le_mul (finiteCharacter_norm_le_one a.character _)
      (finiteCharacter_norm_le_one a.character _) (norm_nonneg _) zero_le_one)
    (finiteCharacter_norm_le_one r.character _) (norm_nonneg _) (by norm_num)).trans_eq
      (by norm_num)

theorem firstRightDivisorFactor_norm_le_one
    (a r : OrbitalGaussColumn K S Γ)
    (δ : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) :
    ‖firstRightDivisorFactor a r δ‖ ≤ 1 := by
  letI := finite_sIntegerPrincipalResidue K
    (S : Set (HeightOneSpectrum (𝓞 K))) a.modulus a.nonzero
  letI := finite_sIntegerPrincipalResidue K
    (S : Set (HeightOneSpectrum (𝓞 K))) r.modulus r.nonzero
  letI := Fintype.ofFinite ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸
    Ideal.span {a.modulus})
  letI := Fintype.ofFinite ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸
    Ideal.span {r.modulus})
  rw [firstRightDivisorFactor, norm_mul, norm_mul, norm_star]
  exact (mul_le_mul
    (mul_le_mul (finiteCharacter_norm_le_one a.character _)
      (finiteCharacter_norm_le_one a.character _) (norm_nonneg _) zero_le_one)
    (finiteCharacter_norm_le_one r.character _) (norm_nonneg _) (by norm_num)).trans_eq
      (by norm_num)

/-- The character factor is estimated before cancellation of the
actual positive norm denominator. -/
theorem normalized_column_norm_le
    (c phase : ℂ) (N t : ℝ) (hN : 0 < N) (hphase : ‖phase‖ ≤ 1) :
    ‖(c * ((N ^ t : ℝ) : ℂ) / (N : ℂ)) * phase‖ * N ≤ ‖c‖ * N ^ t := by
  rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hN,
    abs_of_pos (Real.rpow_pos_of_pos hN t)]
  calc
    _ ≤ ((‖c‖ * N ^ t) / N * 1) * N :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hphase
          (div_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hN.le _)) hN.le)) hN.le
    _ = _ := by rw [mul_one, div_mul_cancel₀ _ hN.ne']

end FiniteFactors

section FirstKey

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable (F : FirstPresentation call p) (hF : F.Realizes)

private theorem chart_coefficient_functions_of_heq
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset)
    {φ ψ : F.source.Column → F.source.Column →
      SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
    (e : φ = ψ)
    (x : FirstBlockProfileChart (E := ℝ) (Arithmetic.units_are_sixth c)
      (Arithmetic.localMeasures (K := K)) (F.source.block v)
      (Arithmetic.context c) F.source.columns F.source.columns φ
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) F.source.radius D.val)
    (y : FirstBlockProfileChart (E := ℝ) (Arithmetic.units_are_sixth c)
      (Arithmetic.localMeasures (K := K)) (F.source.block v)
      (Arithmetic.context c) F.source.columns F.source.columns ψ
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) F.source.radius D.val)
    (h : HEq x y) : x.leftCoefficient = y.leftCoefficient ∧
      x.rightCoefficient = y.rightCoefficient := by
  cases e
  have he : x = y := eq_of_heq h
  exact ⟨congrArg FirstBlockProfileChart.leftCoefficient he,
    congrArg FirstBlockProfileChart.rightCoefficient he⟩

include hF in
theorem first_chart_leftCoefficient
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset)
    (i : F.source.Column) :
    (F.source.charts v D).leftCoefficient i =
      F.coefficient i *
        ((((Arithmetic.data c).exteriorNorm ((F.source.block v).leftResidual i) ^ p.tilt : ℝ) : ℂ) /
          ((Arithmetic.data c).exteriorNorm ((F.source.block v).leftResidual i) : ℂ)) := by
  exact congrFun
    (chart_coefficient_functions_of_heq F v D hF.profile
      (F.source.charts v D) (F.canonicalChart v D) (hF.chart v D)).1 i

include hF in
theorem first_chart_rightCoefficient
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset)
    (i : F.source.Column) :
    (F.source.charts v D).rightCoefficient i =
      F.coefficient i *
        ((((Arithmetic.data c).exteriorNorm ((F.source.block v).rightResidual i) ^ p.tilt : ℝ) : ℂ) /
          ((Arithmetic.data c).exteriorNorm ((F.source.block v).rightResidual i) : ℂ)) := by
  exact congrFun
    (chart_coefficient_functions_of_heq F v D hF.profile
      (F.source.charts v D) (F.canonicalChart v D) (hF.chart v D)).2 i

theorem first_key_phase_norm (key : FirstCauchyKey F) :
    ‖FirstCauchyKey.phase key‖ = 1 := by
  unfold FirstCauchyKey.phase
  split_ifs <;> exact Circle.norm_coe _

/-- The common first divisor is retained on each nonzero original
column; no later Fourier phase is needed to identify it. -/
theorem first_key_divisor_dvd (key : FirstCauchyKey F) (i : F.source.Column)
    (hnz : FirstCauchyKey.coefficient key i ≠ 0) :
    (FirstCauchyKey.residual key).val ∣ ((FirstCauchyKey.data key).ideal i).val := by
  by_contra hn
  exact hnz (by simp only [FirstCauchyKey.coefficient, if_neg hn])

include hF in
theorem first_key_coefficient_norm_le (key : FirstCauchyKey F) (i : F.source.Column) :
    ‖FirstCauchyKey.coefficient key i‖ *
        (Arithmetic.data c).exteriorNorm ((FirstCauchyKey.data key).ideal i) ≤
      ‖F.coefficient i‖ *
        (Arithmetic.data c).exteriorNorm ((FirstCauchyKey.data key).ideal i) ^ p.tilt := by
  by_cases hdiv : (FirstCauchyKey.residual key).val ∣
      ((FirstCauchyKey.data key).ideal i).val
  · rw [FirstCauchyKey.coefficient, if_pos hdiv, norm_mul, first_key_phase_norm, mul_one]
    cases hs : FirstCauchyKey.side key
    · simp only [hs, Bool.false_eq_true, if_false, FirstCauchyKey.data]
      rw [(FirstCauchyKey.piece key).left_ideal]
      unfold FirstBlockDirectData.originalLeftCoefficient
      rw [first_chart_leftCoefficient F hF]
      have he := normalized_column_norm_le (F.coefficient i)
        (firstLeftDivisorFactor
          (generatedOriginalColumn (σ := Arithmetic.embedding c)
            (Arithmetic.units_are_sixth c) ((FirstCauchyKey.block key).leftResidual i)
            ((FirstCauchyKey.block key).leftGenerator i)
            ((FirstCauchyKey.block key).left_generates i))
          (actualActiveColumn (Arithmetic.units_are_sixth c) (Arithmetic.context c)
            (FirstCauchyKey.block key).primes (FirstCauchyKey.block key).primes_injective
            (FirstCauchyKey.block key).leftMultiplicity (FirstCauchyKey.block key).rightMultiplicity)
          (sIntegerMaskGenerator K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
            (FirstCauchyKey.divisor key).val).val)
        ((Arithmetic.data c).exteriorNorm ((FirstCauchyKey.block key).leftResidual i))
        p.tilt ((Arithmetic.data c).exteriorNorm_pos
          ((FirstCauchyKey.block key).leftResidual i))
        (firstLeftDivisorFactor_norm_le_one _ _ _)
      simp only [mul_div_assoc] at he
      dsimp only [FirstCauchyKey.block, ActualDirectFirstSource.block,
        FirstCauchyKey.divisor] at he ⊢
      exact he
    · simp only [hs, if_true, FirstCauchyKey.data]
      rw [(FirstCauchyKey.piece key).right_ideal]
      unfold FirstBlockDirectData.originalRightCoefficient
      rw [first_chart_rightCoefficient F hF]
      have he := normalized_column_norm_le (F.coefficient i)
        (firstRightDivisorFactor
          (generatedOriginalColumn (σ := Arithmetic.embedding c)
            (Arithmetic.units_are_sixth c) ((FirstCauchyKey.block key).rightResidual i)
            ((FirstCauchyKey.block key).rightGenerator i)
            ((FirstCauchyKey.block key).right_generates i))
          (actualActiveColumn (Arithmetic.units_are_sixth c) (Arithmetic.context c)
            (FirstCauchyKey.block key).primes (FirstCauchyKey.block key).primes_injective
            (FirstCauchyKey.block key).leftMultiplicity (FirstCauchyKey.block key).rightMultiplicity)
          (sIntegerMaskGenerator K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
            (FirstCauchyKey.divisor key).val).val)
        ((Arithmetic.data c).exteriorNorm ((FirstCauchyKey.block key).rightResidual i))
        p.tilt ((Arithmetic.data c).exteriorNorm_pos
          ((FirstCauchyKey.block key).rightResidual i))
        (firstRightDivisorFactor_norm_le_one _ _ _)
      simp only [mul_div_assoc] at he
      dsimp only [FirstCauchyKey.block, ActualDirectFirstSource.block,
        FirstCauchyKey.divisor] at he ⊢
      exact he
  · rw [FirstCauchyKey.coefficient, if_neg hdiv, norm_zero, zero_mul]
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg
      ((Arithmetic.data c).exteriorNorm_pos _).le _)

include hF in
theorem first_key_original_coefficient_nonzero
    (key : FirstCauchyKey F) (i : F.source.Column)
    (hnz : FirstCauchyKey.coefficient key i ≠ 0) : F.coefficient i ≠ 0 := by
  intro hz
  have h := first_key_coefficient_norm_le F hF key i
  rw [hz, norm_zero, zero_mul] at h
  have hpos := mul_pos (norm_pos_iff.mpr hnz)
    ((Arithmetic.data c).exteriorNorm_pos ((FirstCauchyKey.data key).ideal i))
  exact (not_lt_of_ge h) hpos

theorem first_key_column_mem (key : FirstCauchyKey F) (i : F.source.Column)
    (hi : i ∈ (FirstCauchyKey.data key).columns) : i ∈ F.source.columns := by
  cases hs : FirstCauchyKey.side key
  · simp only [FirstCauchyKey.data, hs, Bool.false_eq_true, if_false] at hi
    rw [(FirstCauchyKey.piece key).left_columns] at hi
    exact (Finset.mem_filter.mp hi).1
  · simp only [FirstCauchyKey.data, hs, if_true] at hi
    rw [(FirstCauchyKey.piece key).right_columns] at hi
    exact (Finset.mem_filter.mp hi).1

/-- Extracting the first common support only divides the original
ideal; the original coefficient index is unchanged. -/
theorem first_key_ideal_dvd_original (key : FirstCauchyKey F) (i : F.source.Column) :
    ((FirstCauchyKey.data key).ideal i).val ∣ (F.source.ideal i).val := by
  have hd : supportResidual (F.source.ideal i).val (primeSupport key.1.val.1) ∣
      (F.source.ideal i).val := by
    refine ⟨supportExtract (F.source.ideal i).val (primeSupport key.1.val.1), ?_⟩
    exact (support_reconstruct (F.source.ideal i).val (F.source.ideal i).property.1
      (primeSupport key.1.val.1)).symm.trans (mul_comm _ _)
  cases hs : FirstCauchyKey.side key
  · simp only [FirstCauchyKey.data, hs, Bool.false_eq_true, if_false]
    have hideal : ((FirstCauchyKey.piece key).leftData.ideal i).val =
        supportResidual (F.source.ideal i).val (primeSupport key.1.val.1) :=
      (congrArg (fun f : F.source.Column → (Arithmetic.data c).Exterior => (f i).val)
        (FirstCauchyKey.piece key).left_ideal).trans
          ((FirstCauchyKey.block key).left_residual i)
    exact Eq.mp (congrArg (fun I : Ideal (𝓞 K) => I ∣ (F.source.ideal i).val)
      hideal.symm) hd
  · simp only [FirstCauchyKey.data, hs, if_true]
    have hideal : ((FirstCauchyKey.piece key).rightData.ideal i).val =
        supportResidual (F.source.ideal i).val (primeSupport key.1.val.1) :=
      (congrArg (fun f : F.source.Column → (Arithmetic.data c).Exterior => (f i).val)
        (FirstCauchyKey.piece key).right_ideal).trans
          ((FirstCauchyKey.block key).right_residual i)
    exact Eq.mp (congrArg (fun I : Ideal (𝓞 K) => I ∣ (F.source.ideal i).val)
      hideal.symm) hd

theorem exterior_norm_le_of_dvd {A : SArithmeticData K} (I J : A.Exterior)
    (hdiv : J.val ∣ I.val) : A.exteriorNorm J ≤ A.exteriorNorm I := by
  obtain ⟨D, hD⟩ := hdiv
  have hDzero : D ≠ 0 := by
    intro hz
    exact I.property.1 (hD.trans (by rw [hz, mul_zero, Ideal.zero_eq_bot]))
  have hnormD : 1 ≤ (Ideal.absNorm D : ℝ) := idealNorm_ge_one D hDzero
  change (Ideal.absNorm J.val : ℝ) ≤ (Ideal.absNorm I.val : ℝ)
  rw [hD, map_mul, Nat.cast_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hnormD (Nat.cast_nonneg _)

include hF in
/-- This is the actual weighted coefficient bound used by the second
zero. Its negative central degree comes from the unchanged input
coefficient, and the only additional power is the original log tilt. -/
theorem first_key_weighted_coefficient_bound
    (frame : SourceFrame) (input : ProfileInput call)
    (horders : {(0, 0)} ⊆ input.orders) (hframe : call.frame = frame)
    (hannulus : FirstZeroProof.uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤
      call.base ^ p.loss)
    (T : ℝ) (hT : call.workingParameters.n₁ + call.workingParameters.n₂ +
      call.workingParameters.z + p.loss ≤ T)
    (key : FirstCauchyKey F) (i : F.source.Column)
    (hi : i ∈ (FirstCauchyKey.data key).columns) :
    ‖FirstCauchyKey.coefficient key i‖ *
        (Arithmetic.data c).exteriorNorm ((FirstCauchyKey.data key).ideal i) ≤
      ((2 * input.amplitude ^ (c.geometry.slots + 2)) *
        call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z) / 2)) * call.base ^ (T * p.tilt) := by
  have hbound : 0 ≤ ((2 * input.amplitude ^ (c.geometry.slots + 2)) *
      call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z) / 2)) := by
    exact mul_nonneg (mul_nonneg (by norm_num)
      (pow_nonneg (zero_le_one.trans input.amplitude_one_le) _))
      (Real.rpow_nonneg call.base_pos.le _)
  by_cases hnz : FirstCauchyKey.coefficient key i = 0
  · rw [hnz, norm_zero, zero_mul]
    exact mul_nonneg hbound (Real.rpow_nonneg call.base_pos.le _)
  · have horiginal := first_key_original_coefficient_nonzero F hF key i hnz
    have hiF := first_key_column_mem F key i hi
    have hnorm : (Arithmetic.data c).exteriorNorm ((FirstCauchyKey.data key).ideal i) ≤
        call.base ^ T := by
      apply (exterior_norm_le_of_dvd (F.source.ideal i) ((FirstCauchyKey.data key).ideal i)
        (first_key_ideal_dvd_original F key i)).trans
      exact (FirstZeroProof.first_active_column_norm_le frame input hframe p.loss
        hannulus F hF i hiF horiginal).trans
          (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le hT)
    have htilt : (Arithmetic.data c).exteriorNorm ((FirstCauchyKey.data key).ideal i) ^ p.tilt ≤
        call.base ^ (T * p.tilt) := by
      exact (Real.rpow_le_rpow ((Arithmetic.data c).exteriorNorm_pos _).le hnorm
        p.tilt_pos.le).trans_eq (Real.rpow_mul call.base_pos.le T p.tilt).symm
    exact (first_key_coefficient_norm_le F hF key i).trans
      (mul_le_mul (FirstZeroProof.first_coefficient_norm_le input horders F hF i hiF)
        htilt (Real.rpow_nonneg ((Arithmetic.data c).exteriorNorm_pos _).le _) hbound)

end FirstKey

section PoolCoefficient

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

/-- The genuine residual coefficient retains exactly the original
weighted norm. No prime power is paid a second time. -/
theorem residual_coefficient_norm_mul_norm
    (d : FirstGaussPoolData C P ι) (q : ExteriorPrime A) (n : ℕ)
    (a : ι → ℂ) (i : d.valuationColumns q n) :
    ‖d.residualCoefficient q n a i‖ * A.exteriorNorm (d.residualPresentation q n i).residual =
      ‖a i.val‖ * A.exteriorNorm (d.ideal i.val) := by
  rw [FirstGaussPoolData.residualCoefficient, norm_div, norm_mul,
    (d.residualPresentation q n i).columnPhase_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (A.exteriorNorm_pos _), div_mul_cancel₀ _ (A.exteriorNorm_pos _).ne']
  rw [FirstGaussPoolData.adjustedCoefficient, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (A.exteriorNorm_pos _)]

theorem residual_coefficient_nonzero_original
    (d : FirstGaussPoolData C P ι) (q : ExteriorPrime A) (n : ℕ)
    (a : ι → ℂ) (i : d.valuationColumns q n)
    (hnz : d.residualCoefficient q n a i ≠ 0) : a i.val ≠ 0 := by
  intro hz
  have he := residual_coefficient_norm_mul_norm d q n a i
  rw [hz, norm_zero, zero_mul] at he
  have hp := mul_pos (norm_pos_iff.mpr hnz)
    (A.exteriorNorm_pos (d.residualPresentation q n i).residual)
  exact (ne_of_gt hp) he

end PoolCoefficient

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof
