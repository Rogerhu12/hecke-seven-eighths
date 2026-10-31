import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstBlocks
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondResidualSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussEnergySource

/-!
# Exact second common-support sources

The actual finite pool of complete common prime-power parts partitions
the original two-Gauss source.  Residual ideals are extracted from the
original whole column.  Allowed common generators and their products
replace the original generators by the arithmetic generator identity
before Poisson, retaining the same original Schwartz profile.

The rectangular source below keeps residual coprimality as a zero gate.
It uses the original mask and the one computed physical cutoff supplied
by `FirstFiniteSource`.  None of these source identities is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.Support UniqueFactorizationMonoid
open HeckePort.IdealMobiusDivisorSum
open MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}

def engineAllowedGenerator (C : A.GeneralArithmeticContext σ η htrace)
    (I : A.Exterior) : A.R := Classical.choose (C.allowed_integral I)

theorem engineAllowedGenerator_generates (C : A.GeneralArithmeticContext σ η htrace)
    (I : A.Exterior) : A.Generates I (engineAllowedGenerator C I) :=
  (Classical.choose_spec (Classical.choose_spec (C.allowed_integral I))).1

theorem engineAllowedGenerator_allowed (C : A.GeneralArithmeticContext σ η htrace)
    (I : A.Exterior) :
    ∃ u : Kˣ, (u : K) = (engineAllowedGenerator C I : K) ∧ A.IsAllowed C.correction.B u := by
  obtain ⟨u, hu⟩ := Classical.choose_spec (C.allowed_integral I)
  exact ⟨u, hu.2⟩

theorem allowed_mk0_of_generator (B : Subgroup A.V) (a : A.R) (ha : a ≠ 0)
    (hallowed : ∃ u : Kˣ, (u : K) = (a : K) ∧ A.IsAllowed B u) :
    A.IsAllowed B (Units.mk0 (a : K) (by exact_mod_cast ha)) := by
  obtain ⟨u, hu, hallowed⟩ := hallowed
  have he : u = Units.mk0 (a : K) (by exact_mod_cast ha) := Units.ext hu
  rwa [← he]

theorem allowed_generator_product (B : Subgroup A.V) (a b : A.R)
    (ha : ∃ u : Kˣ, (u : K) = (a : K) ∧ A.IsAllowed B u)
    (hb : ∃ u : Kˣ, (u : K) = (b : K) ∧ A.IsAllowed B u) :
    ∃ u : Kˣ, (u : K) = ((a * b : A.R) : K) ∧ A.IsAllowed B u := by
  obtain ⟨u, hu, hau⟩ := ha
  obtain ⟨v, hv, hbv⟩ := hb
  refine ⟨u * v, ?_, ?_⟩
  · simp only [Units.val_mul, hu, hv, Subalgebra.coe_mul]
  · change A.sClass (u * v) ∈ B
    rw [map_mul]
    exact B.mul_mem hau hbv

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

def FirstCommonCharacterBlock.commonLeftIdeal (b : FirstCommonCharacterBlock fullI fullJ DE) :
    A.Exterior := primePowerProduct b.primes b.leftMultiplicity

def FirstCommonCharacterBlock.commonRightIdeal (b : FirstCommonCharacterBlock fullI fullJ DE) :
    A.Exterior := primePowerProduct b.primes b.rightMultiplicity

def FirstCommonCharacterBlock.secondLeftIdeal (b : FirstCommonCharacterBlock fullI fullJ DE)
    (i : ι) : A.Exterior := ExteriorIdealEuler.mul b.commonLeftIdeal (b.leftResidual i)

def FirstCommonCharacterBlock.secondRightIdeal (b : FirstCommonCharacterBlock fullI fullJ DE)
    (j : κ) : A.Exterior := ExteriorIdealEuler.mul b.commonRightIdeal (b.rightResidual j)

theorem FirstCommonCharacterBlock.secondLeftIdeal_eq
    (b : FirstCommonCharacterBlock fullI fullJ DE) (left : Finset ι)
    (i : ι) (hi : i ∈ b.leftColumns left) : b.secondLeftIdeal i = fullI i :=
  Subtype.ext (b.left_reconstruct left i hi).symm

theorem FirstCommonCharacterBlock.secondRightIdeal_eq
    (b : FirstCommonCharacterBlock fullI fullJ DE) (right : Finset κ)
    (j : κ) (hj : j ∈ b.rightColumns right) : b.secondRightIdeal j = fullJ j :=
  Subtype.ext (b.right_reconstruct right j hj).symm

theorem FirstCommonCharacterBlock.secondLeft_generates
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace) (i : ι) :
    A.Generates (b.secondLeftIdeal i)
      (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i) :=
  generated_product b.commonLeftIdeal (b.leftResidual i) (b.secondLeftIdeal i) rfl
    _ _ (engineAllowedGenerator_generates C _) (b.left_generates i)

theorem FirstCommonCharacterBlock.secondRight_generates
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace) (j : κ) :
    A.Generates (b.secondRightIdeal j)
      (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j) :=
  generated_product b.commonRightIdeal (b.rightResidual j) (b.secondRightIdeal j) rfl
    _ _ (engineAllowedGenerator_generates C _) (b.right_generates j)

private theorem common_residual_coprime (I J : A.Exterior) (S : Finset (Ideal (𝓞 K)))
    (hI : primeSupport I.val = S) (hJ : primeSupport J.val ⊆ primeSupport J.val \ S) :
    IsCoprime I.val J.val := by
  apply (primeSupport_disjoint_iff I.property.1 J.property.1).mp
  rw [hI]
  exact Finset.disjoint_left.mpr (fun P hP hQ => (Finset.mem_sdiff.mp (hJ hQ)).2 hP)

theorem FirstCommonCharacterBlock.second_coprimalities
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (hsupport : primeSupport DE.1 = primeSupport DE.2) :
    (∀ i, IsCoprime b.commonLeftIdeal.val (b.leftResidual i).val) ∧
    (∀ i, IsCoprime b.commonRightIdeal.val (b.leftResidual i).val) ∧
    (∀ j, IsCoprime b.commonLeftIdeal.val (b.rightResidual j).val) ∧
    (∀ j, IsCoprime b.commonRightIdeal.val (b.rightResidual j).val) := by
  have hL : primeSupport b.commonLeftIdeal.val = primeSupport DE.1 := by
    rw [FirstCommonCharacterBlock.commonLeftIdeal, b.common_left]
  have hR : primeSupport b.commonRightIdeal.val = primeSupport DE.1 := by
    rw [FirstCommonCharacterBlock.commonRightIdeal, b.common_right, ← hsupport]
  have hleft (i : ι) : primeSupport (b.leftResidual i).val ⊆
      primeSupport (b.leftResidual i).val \ primeSupport DE.1 := by
    rw [b.left_residual, supportResidual_support]
    intro P hP
    exact Finset.mem_sdiff.mpr ⟨hP, (Finset.mem_sdiff.mp hP).2⟩
  have hright (j : κ) : primeSupport (b.rightResidual j).val ⊆
      primeSupport (b.rightResidual j).val \ primeSupport DE.1 := by
    rw [b.right_residual, supportResidual_support]
    intro P hP
    exact Finset.mem_sdiff.mpr ⟨hP, (Finset.mem_sdiff.mp hP).2⟩
  exact ⟨fun i => common_residual_coprime _ _ _ hL (hleft i),
    fun i => common_residual_coprime _ _ _ hR (hleft i),
    fun j => common_residual_coprime _ _ _ hL (hright j),
    fun j => common_residual_coprime _ _ _ hR (hright j)⟩

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

include hΓ in
/-- The three reciprocal phases in the complete common-support formula
are one for actual allowed generators of the coprime residual factors. -/
theorem actualCommonPhase_allowed
    (C : A.GeneralArithmeticContext σ η htrace)
    (ID IE IA IB : A.Exterior) (d e a b : A.R)
    (hd : A.Generates ID d) (he : A.Generates IE e)
    (ha : A.Generates IA a) (hb : A.Generates IB b)
    (hdAllowed : ∃ u : Kˣ, (u : K) = (d : K) ∧ A.IsAllowed C.correction.B u)
    (heAllowed : ∃ u : Kˣ, (u : K) = (e : K) ∧ A.IsAllowed C.correction.B u)
    (haAllowed : ∃ u : Kˣ, (u : K) = (a : K) ∧ A.IsAllowed C.correction.B u)
    (hbAllowed : ∃ u : Kˣ, (u : K) = (b : K) ∧ A.IsAllowed C.correction.B u)
    (hEa : IsCoprime IE.val IA.val) (hDb : IsCoprime ID.val IB.val)
    (hab : IsCoprime IA.val IB.val) :
    actualCommonPhase (σ := σ) ID IE IA IB d e a b = 1 := by
  obtain ⟨ud, hud, had⟩ := hdAllowed
  obtain ⟨ue, hue, hae⟩ := heAllowed
  obtain ⟨ua, hua, haa⟩ := haAllowed
  obtain ⟨ub, hub, hab'⟩ := hbAllowed
  have hEA := firstReciprocalPhase_allowed hΓ C IE IA e a he ha
    ue ua hue hua hae haa hEa
  have hBD := firstReciprocalPhase_allowed hΓ C IB ID b d hb hd
    ub ud hub hud hab' had hDb.symm
  have hBA := firstReciprocalPhase_allowed hΓ C IB IA b a hb ha
    ub ua hub hua hab' haa hab.symm
  dsimp only [firstReciprocalPhase, generatedOriginalColumn] at hEA hBD hBA
  simp only [generatedIdealCharacter_mk] at hEA hBD hBA
  rw [actualCommonPhase, hEA, hBD, hBA]
  simp only [one_mul]

include hΓ in
theorem FirstCommonCharacterBlock.secondPhase_one
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace)
    (hsupport : primeSupport DE.1 = primeSupport DE.2)
    (hleft : ∀ i, ∃ u : Kˣ, (u : K) = (b.leftGenerator i : K) ∧ A.IsAllowed C.correction.B u)
    (hright : ∀ j, ∃ u : Kˣ, (u : K) = (b.rightGenerator j : K) ∧ A.IsAllowed C.correction.B u)
    (i : ι) (j : κ) (hcop : IsCoprime (b.leftResidual i).val (b.rightResidual j).val) :
    actualCommonPhase (σ := σ) b.commonLeftIdeal b.commonRightIdeal
      (b.leftResidual i) (b.rightResidual j)
      (engineAllowedGenerator C b.commonLeftIdeal) (engineAllowedGenerator C b.commonRightIdeal)
      (b.leftGenerator i) (b.rightGenerator j) = 1 := by
  obtain ⟨hDa, hEa, hDb, hEb⟩ := b.second_coprimalities hsupport
  exact actualCommonPhase_allowed hΓ C _ _ _ _ _ _ _ _
    (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
    (b.left_generates i) (b.right_generates j)
    (engineAllowedGenerator_allowed C _) (engineAllowedGenerator_allowed C _)
    (hleft i) (hright j) (hEa i) (hDb j) hcop

def FirstCommonCharacterBlock.secondPair
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (j : κ) : ParentPeriodicPair K A.Sf Γ :=
  ((generatedOriginalColumn (σ := σ) hΓ (b.secondLeftIdeal i)
      (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
      (b.secondLeft_generates C i)).pair hDiff
    (generatedOriginalColumn (σ := σ) hΓ (b.secondRightIdeal j)
      (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
      (b.secondRight_generates C j)) (profiles i j)).gated
    (IsCoprime (b.leftResidual i).val (b.rightResidual j).val)

def FirstCommonCharacterBlock.secondFiniteSource
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace) (left : Finset ι) (right : Finset κ)
    (profiles : ι → κ → SchwartzMap V ℂ) (M : Finset (HeightOneSpectrum A.R))
    (radius : {r : ℝ // 0 < r}) (X : ℝ) (hX : 1 ≤ X) : FirstFiniteSource K A.Sf Γ ι κ where
  leftColumns := b.leftColumns left
  rightColumns := b.rightColumns right
  pairs := b.secondPair hΓ hDiff C profiles
  mask := M
  radius := radius
  cutoff := X
  cutoff_ge_one := hX

variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]

theorem FirstCommonCharacterBlock.secondPair_source
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace)
    (D : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ htrace C.correction.B D)
    (left : Finset ι) (right : Finset κ)
    (afull : ι → A.R) (bfull : κ → A.R)
    (hafull : ∀ i, A.Generates (fullI i) (afull i))
    (hbfull : ∀ j, A.Generates (fullJ j) (bfull j))
    (hfullLeft : ∀ i ∈ left, ∃ u : Kˣ, (u : K) = (afull i : K) ∧ A.IsAllowed C.correction.B u)
    (hfullRight : ∀ j ∈ right, ∃ u : Kˣ, (u : K) = (bfull j : K) ∧ A.IsAllowed C.correction.B u)
    (hleft : ∀ i, ∃ u : Kˣ, (u : K) = (b.leftGenerator i : K) ∧ A.IsAllowed C.correction.B u)
    (hright : ∀ j, ∃ u : Kˣ, (u : K) = (b.rightGenerator j : K) ∧ A.IsAllowed C.correction.B u)
    (profiles : ι → κ → SchwartzMap V ℂ)
    (ψ : ((v : (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right) :
    (b.secondPair hΓ hDiff C profiles i j).maskedSeries ψ radius M =
      if IsCoprime (b.leftResidual i).val (b.rightResidual j).val then
        ((generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).pair hDiff
          (generatedOriginalColumn (σ := σ) hΓ (fullJ j) (bfull j) (hbfull j))
          (profiles i j)).maskedSeries ψ radius M else 0 := by
  unfold FirstCommonCharacterBlock.secondPair
  rw [ParentPeriodicPair.gated_maskedSeries]
  congr 1
  have ha := b.secondLeft_generates C i
  have hb := b.secondRight_generates C j
  rw [b.secondLeftIdeal_eq left i hi] at ha
  rw [b.secondRightIdeal_eq right j hj] at hb
  have he := generated_gauss_pair_source_generator_change hΓ hDiff C D hD
    (fullI i) (fullJ j) (afull i) (bfull j)
    (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
    (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
    (hafull i) (hbfull j) ha hb
    (allowed_mk0_of_generator _ _ (hafull i).1 (hfullLeft i (Finset.mem_filter.mp hi).1))
    (allowed_mk0_of_generator _ _ (hbfull j).1 (hfullRight j (Finset.mem_filter.mp hj).1))
    (allowed_mk0_of_generator _ _ ha.1
      (allowed_generator_product _ _ _ (engineAllowedGenerator_allowed C _) (hleft i)))
    (allowed_mk0_of_generator _ _ hb.1
      (allowed_generator_product _ _ _ (engineAllowedGenerator_allowed C _) (hright j)))
    (profiles i j) ψ radius M
  simpa only [b.secondLeftIdeal_eq left i hi, b.secondRightIdeal_eq right j hj] using he

/-- The second source is partitioned by its actual complete common labels.
The choice of allowed product generators is internal to each block. -/
theorem common_support_gauss_sources
    (C : A.GeneralArithmeticContext σ η htrace)
    (D : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ htrace C.correction.B D)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (afull : ι → A.R) (bfull : κ → A.R)
    (hafull : ∀ i, A.Generates (fullI i) (afull i))
    (hbfull : ∀ j, A.Generates (fullJ j) (bfull j))
    (hfullLeft : ∀ i ∈ left, ∃ u : Kˣ, (u : K) = (afull i : K) ∧ A.IsAllowed C.correction.B u)
    (hfullRight : ∀ j ∈ right, ∃ u : Kˣ, (u : K) = (bfull j : K) ∧ A.IsAllowed C.correction.B u)
    (profiles : ι → κ → SchwartzMap V ℂ)
    (ψ : ((v : (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R)) :
    (∑ i ∈ left, ∑ j ∈ right,
      ((generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).pair hDiff
        (generatedOriginalColumn (σ := σ) hΓ (fullJ j) (bfull j) (hbfull j))
        (profiles i j)).maskedSeries ψ radius M) =
      ∑ DE : commonSupportPool left right (fun i => (fullI i).val) (fun j => (fullJ j).val),
        let b := canonicalFirstCommonBlock C left right fullI fullJ DE.val DE.property
        ∑ i ∈ b.leftColumns left, ∑ j ∈ b.rightColumns right,
          (b.secondPair hΓ hDiff C profiles i j).maskedSeries ψ radius M := by
  rw [sum_common_support_blocks left right (fun i => (fullI i).val) (fun j => (fullJ j).val)]
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro DE _
  let b := canonicalFirstCommonBlock C left right fullI fullJ DE.val DE.property
  change (∑ i ∈ b.leftColumns left, ∑ j ∈ b.rightColumns right, _) = _
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← b.left_residual i, ← b.right_residual j]
  exact (b.secondPair_source hΓ hDiff C D hD left right afull bfull hafull hbfull
    hfullLeft hfullRight
    (canonicalFirstCommonBlock_allowed C left right fullI fullJ DE.val DE.property).1
    (canonicalFirstCommonBlock_allowed C left right fullI fullJ DE.val DE.property).2
    profiles ψ radius M i hi j hj).symm

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.common_support_gauss_sources
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.second_coprimalities
