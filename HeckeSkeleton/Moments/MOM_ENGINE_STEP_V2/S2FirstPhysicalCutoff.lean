import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstCauchyContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S2: sharp cutoff from the original active columns

The actual modulus divides out both complete common factors and keeps
the active radical.  The cutoff maximum only uses nonzero original
Gram profiles.  Its divisor contributes its own norm, and the original
small cutoff exponent is absorbed in the declared four-loss window.

The generic identities are adapted from the A-line
`CanonicalSharpFirstFrequencies`; only base imports are needed here.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2Cutoff

open EngineStep NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable (b : FirstCommonCharacterBlock fullI fullJ DE)

theorem activeRadical_swap
    (hcommon : HeckePort.IdealMobiusDivisorSum.primeSupport DE.1 =
      HeckePort.IdealMobiusDivisorSum.primeSupport DE.2) :
    firstActiveRadical DE.2 DE.1 = firstActiveRadical DE.1 DE.2 := by
  unfold firstActiveRadical
  rw [← hcommon]
  apply Finset.prod_congr
  · apply Finset.filter_congr
    intro P _
    exact ne_comm
  · intro P _
    rfl

theorem divisor_norm (D : Finset (HeightOneSpectrum A.R)) :
    A.exteriorNorm (firstPhysicalDivisorIdeal D) =
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val := by
  exact (generates_sIntegerElementNorm (firstPhysicalDivisorIdeal D) _
    (originalFrequencyIdeal_generates _
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).property)).symm

theorem modulus_norm
    (C : A.GeneralArithmeticContext σ η hS)
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (i : ι) (j : κ) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(b.pair hΓ C profiles i j).modulus,
        (b.pair hΓ C profiles i j).modulus_ne_zero⟩).val =
      (Ideal.absNorm ((b.leftResidual i).val * ((b.rightResidual j).val *
        (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val)) : ℝ) := by
  change (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    (sIntegerNonzeroMul K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨b.leftGenerator i, (b.left_generates i).1⟩
      (sIntegerNonzeroMul K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        ⟨b.rightGenerator j, (b.right_generates j).1⟩
        ⟨firstActiveGenerator C b.primes b.leftMultiplicity b.rightMultiplicity,
          (firstActiveGenerator_generates C b.primes
            b.leftMultiplicity b.rightMultiplicity).1⟩))).val = _
  rw [sIntegerElementNorm_nonzeroMul, sIntegerElementNorm_nonzeroMul,
    generates_sIntegerElementNorm _ _ (b.left_generates i),
    generates_sIntegerElementNorm _ _ (b.right_generates j),
    generates_sIntegerElementNorm _ _
      (firstActiveGenerator_generates C b.primes b.leftMultiplicity b.rightMultiplicity)]
  simp only [map_mul, Nat.cast_mul]

theorem modulus_norm_eq_common_quotient
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(b.pair hΓ C profiles i j).modulus, (b.pair hΓ C profiles i j).modulus_ne_zero⟩).val =
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) *
        (Ideal.absNorm (firstActiveRadical DE.1 DE.2) : ℝ) /
          ((Ideal.absNorm DE.1 : ℝ) * (Ideal.absNorm DE.2 : ℝ)) := by
  have hc : 0 < (Ideal.absNorm DE.1 : ℝ) := by
    rw [← b.common_left]
    exact A.exteriorNorm_pos _
  have hd : 0 < (Ideal.absNorm DE.2 : ℝ) := by
    rw [← b.common_right]
    exact A.exteriorNorm_pos _
  rw [modulus_norm hΓ b C profiles i j,
    b.left_reconstruct left i hi, b.right_reconstruct right j hj]
  simp only [map_mul, Nat.cast_mul, b.common_left, b.common_right, b.activeIdeal_eq]
  field_simp [ne_of_gt hc, ne_of_gt hd]
  <;> ring

theorem modulus_norm_le_product
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (Z productExponent : ℝ) (hZ : 1 < Z)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (hproduct : (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ Z ^ productExponent) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(b.pair hΓ C profiles i j).modulus, (b.pair hΓ C profiles i j).modulus_ne_zero⟩).val ≤
      Z ^ (productExponent - idealLogLength Z DE.1 - idealLogLength Z DE.2 +
        idealLogLength Z (firstActiveRadical DE.1 DE.2)) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hc : DE.1 ≠ 0 := by
    rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  have hd : DE.2 ≠ 0 := by
    rw [← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  rw [modulus_norm_eq_common_quotient hΓ b C left right profiles i hi j hj]
  calc
    _ ≤ (Z ^ productExponent * (Ideal.absNorm (firstActiveRadical DE.1 DE.2) : ℝ)) /
          ((Ideal.absNorm DE.1 : ℝ) * (Ideal.absNorm DE.2 : ℝ)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hproduct (Nat.cast_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by
      rw [← rpow_idealLogLength Z hZ DE.1 hc,
        ← rpow_idealLogLength Z hZ DE.2 hd,
        ← rpow_idealLogLength Z hZ (firstActiveRadical DE.1 DE.2)
          (firstActiveRadical_ne_zero _ _),
        ← Real.rpow_add hz, ← Real.rpow_add hz, ← Real.rpow_sub hz]
      congr 1
      ring

theorem cutoff_le_product
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (M D : Finset (HeightOneSpectrum A.R)) (radius : {r : ℝ // 0 < r})
    (X : ℝ) (hX : 1 ≤ X)
    (Z productExponent rowExponent cutoffExponent : ℝ) (hZ : 1 < Z)
    (hradius : radius.val = Z ^ (-rowExponent)) (hcutoff : X ≤ Z ^ cutoffExponent)
    (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ Z ^ productExponent) :
    (b.finiteSource hΓ C left right profiles M radius X hX).divisorPhysicalCutoff D ≤
      Z ^ (productExponent - idealLogLength Z DE.1 - idealLogLength Z DE.2 +
        idealLogLength Z (firstActiveRadical DE.1 DE.2) +
        idealLogLength Z (firstPhysicalDivisorIdeal D).val - rowExponent + cutoffExponent) := by
  let exponent := productExponent - idealLogLength Z DE.1 - idealLogLength Z DE.2 +
    idealLogLength Z (firstActiveRadical DE.1 DE.2) +
    idealLogLength Z (firstPhysicalDivisorIdeal D).val - rowExponent
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hmask :
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val =
      Z ^ idealLogLength Z (firstPhysicalDivisorIdeal D).val := by
    rw [rpow_idealLogLength Z hZ _ (firstPhysicalDivisorIdeal D).property.1]
    exact (divisor_norm D).symm
  have hb := (b.finiteSource hΓ C left right profiles M radius X hX).divisorPhysicalCutoff_le_supported
    D (Z ^ exponent) (Real.rpow_nonneg hz.le _) (by
      intro i hi j hj hprofile
      have hp : profiles i j ≠ 0 := hprofile
      have hn := modulus_norm_le_product hΓ b C left right profiles Z
        productExponent hZ i hi j hj
        (hproduct i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hp)
      change ((radius.val *
        (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val *
        (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          ⟨(b.pair hΓ C profiles i j).modulus,
            (b.pair hΓ C profiles i j).modulus_ne_zero⟩).val)⁻¹)⁻¹ ≤ _
      rw [inv_inv, hradius, hmask]
      apply (mul_le_mul_of_nonneg_left hn
        (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))).trans_eq
      rw [← Real.rpow_add hz, ← Real.rpow_add hz]
      congr 1
      dsimp only [exponent]
      ring)
  calc
    _ ≤ X * Z ^ exponent := hb
    _ ≤ Z ^ cutoffExponent * Z ^ exponent :=
      mul_le_mul_of_nonneg_right hcutoff (Real.rpow_nonneg hz.le _)
    _ = _ := by
      rw [← Real.rpow_add hz]
      congr 1
      dsimp only [exponent]
      ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2Cutoff

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p}

/-- A pure geometric bridge from the actual nonzero original columns
to the first physical cutoff.  Uniform support windows are supplied by
the separate original-profile construction, with the same demand. -/
theorem physicalCutoff_le (hF : F.Realizes)
    (hcolumns : ∀ i ∈ F.source.columns, F.coefficient i ≠ 0 →
      (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤
        call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z + p.loss))
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset) :
    (F.source.source v).divisorPhysicalCutoff D.val ≤
      call.base ^ (2 * (call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z) - idealLogLength call.base v.val.1 -
        idealLogLength call.base v.val.2 +
        idealLogLength call.base (firstActiveRadical v.val.1 v.val.2) +
        idealLogLength call.base (firstPhysicalDivisorIdeal
          (A := Arithmetic.data c) D.val).val - call.workingParameters.m + 4 * p.loss) := by
  have hproduct : ∀ i ∈ F.source.columns, ∀ j ∈ F.source.columns,
      F.source.profiles i j ≠ 0 →
      (Ideal.absNorm ((F.source.ideal i).val * (F.source.ideal j).val) : ℝ) ≤
        call.base ^ (2 * (call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z + p.loss)) := by
    intro i hi j hj hprofile
    have hci : F.coefficient i ≠ 0 := by
      intro hc
      apply hprofile
      rw [hF.profile]
      simp only [FirstPresentation.originalProfile, hc, zero_mul, zero_smul]
    have hcj : F.coefficient j ≠ 0 := by
      intro hc
      apply hprofile
      rw [hF.profile]
      simp only [FirstPresentation.originalProfile, hc, star_zero, mul_zero, zero_smul]
    have hi' := hcolumns i hi hci
    have hj' := hcolumns j hj hcj
    rw [map_mul, Nat.cast_mul]
    have hb := mul_le_mul hi' hj' ((Arithmetic.data c).exteriorNorm_pos _).le
      (Real.rpow_nonneg call.base_pos.le _)
    change (Ideal.absNorm (F.source.ideal i).val : ℝ) *
      (Ideal.absNorm (F.source.ideal j).val : ℝ) ≤ _ at hb
    apply hb.trans_eq
    rw [← Real.rpow_add call.base_pos]
    congr 1
    ring
  have hb := S2Cutoff.cutoff_le_product
    (Arithmetic.units_are_sixth c) (F.source.block v) (Arithmetic.context c)
    F.source.columns F.source.columns F.source.profiles F.source.mask D.val
    F.source.radius (p.firstCutoff call) (p.firstCutoff_one call) call.base
    (2 * (call.workingParameters.n₁ + call.workingParameters.n₂ +
      call.workingParameters.z + p.loss)) call.workingParameters.m
    p.firstCutoffExponent call.domain.scale hF.radius le_rfl hproduct
  apply hb.trans
  apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
  have hsmall := p.firstCutoff_small
  have hpos := p.loss_pos
  linarith

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2.physicalCutoff_le
