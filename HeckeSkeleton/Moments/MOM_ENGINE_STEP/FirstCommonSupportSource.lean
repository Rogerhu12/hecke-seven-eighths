import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCharacterSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonSupportPartition

/-!
# Actual common-support rectangles for the first source

The independent column filters contain the complete extracted ideals.
Residual coprimality is a literal zero gate, and the principal common
characters remain part of the original orbital mask. All regroupings
and transforms are proved from the individual original characters.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.Moments.Support
open HeckePort.Moments.Active UniqueFactorizationMonoid MeasureTheory

variable {K : Type} [Field K] [NumberField K]

section Gate

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ

def ParentPeriodicPair.gated (p : ParentPeriodicPair K S Γ) (P : Prop) [Decidable P] :
    ParentPeriodicPair K S Γ where
  modulus := p.modulus
  modulus_ne_zero := p.modulus_ne_zero
  residue x := if P then p.residue x else 0
  invariant u a := by
    by_cases hP : P <;> simp only [hP, if_true, if_false, p.invariant]
  profile := p.profile

theorem ParentPeriodicPair.gated_of_true (p : ParentPeriodicPair K S Γ)
    (P : Prop) [Decidable P] (hP : P) : p.gated P = p := by
  cases p
  simp only [ParentPeriodicPair.gated, if_pos hP]

theorem ParentPeriodicPair.gated_orbitWeight (p : ParentPeriodicPair K S Γ)
    (P : Prop) [Decidable P] (q : Q) :
    (p.gated P).orbitWeight q = if P then p.orbitWeight q else 0 := by
  refine Quotient.inductionOn q ?_
  intro x
  simp only [ParentPeriodicPair.orbitWeight, ParentPeriodicPair.gated,
    sIntegerPeriodicOrbitWeight_mk]

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

theorem ParentPeriodicPair.gated_maskedTerm (p : ParentPeriodicPair K S Γ)
    (P : Prop) [Decidable P]
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS)) (q : Q) :
    (p.gated P).maskedTerm ψ radius M q = if P then p.maskedTerm ψ radius M q else 0 := by
  unfold ParentPeriodicPair.maskedTerm
  rw [p.gated_orbitWeight]
  by_cases hP : P <;>
    simp only [hP, if_true, if_false, ParentPeriodicPair.orbitProfile,
      ParentPeriodicPair.gated, mul_zero, zero_mul]

theorem ParentPeriodicPair.gated_maskedSeries (p : ParentPeriodicPair K S Γ)
    (P : Prop) [Decidable P]
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS)) :
    (p.gated P).maskedSeries ψ radius M = if P then p.maskedSeries ψ radius M else 0 := by
  change (∑' q, (p.gated P).maskedTerm ψ radius M q) = _
  simp_rw [p.gated_maskedTerm]
  by_cases hP : P <;>
    simp only [hP, ite_true, ite_false, tsum_zero, ParentPeriodicPair.maskedSeries,
      sIntegerWeightedOrbitalSeries, ParentPeriodicPair.maskedTerm,
      ParentPeriodicPair.orbitProfile]

theorem ParentPeriodicPair.gated_fourierWeight (p : ParentPeriodicPair K S Γ)
    (P : Prop) [Decidable P]
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (δ : OS) (q : Q) :
    sIntegerPeriodicFourierOrbitWeight K (S : Set (HeightOneSpectrum (𝓞 K))) hDiff Γ
        (p.gated P).modulus (p.gated P).modulus_ne_zero
        (p.gated P).residue (p.gated P).invariant δ q =
      if P then sIntegerPeriodicFourierOrbitWeight K (S : Set (HeightOneSpectrum (𝓞 K))) hDiff Γ
        p.modulus p.modulus_ne_zero p.residue p.invariant δ q else 0 := by
  by_cases hP : P
  · rw [p.gated_of_true P hP, if_pos hP]
  · refine Quotient.inductionOn q ?_
    intro x
    rw [sIntegerPeriodicFourierOrbitWeight_mk]
    simp only [ParentPeriodicPair.gated, if_neg hP, sIntegerPeriodicDivisorFourier,
      PeriodicFourier.divisorTransform, PeriodicFourier.fourier, PeriodicFourier.dilate,
      zero_mul, Finset.sum_const_zero]

variable [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

theorem ParentPeriodicPair.gated_transformedRow (p : ParentPeriodicPair K S Γ)
    (P : Prop) [Decidable P]
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) (q : Q) :
    (p.gated P).transformedRow μv hDiff finiteTest radius D q =
      if P then p.transformedRow μv hDiff finiteTest radius D q else 0 := by
  by_cases hP : P
  · rw [p.gated_of_true P hP, if_pos hP]
  · unfold ParentPeriodicPair.transformedRow sIntegerPeriodicFourierProfileTerm
    rw [p.gated_fourierWeight]
    simp only [if_neg hP, zero_mul, mul_zero]

end Gate

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- Exact common prime-power products and their genuine residual generators. -/
structure FirstCommonCharacterBlock {ι κ : Type*}
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K)) where
  primeCount : ℕ
  primes : Fin primeCount → ExteriorPrime A
  primes_injective : Function.Injective primes
  leftMultiplicity : Fin primeCount → ℕ
  rightMultiplicity : Fin primeCount → ℕ
  left_positive : ∀ t, 0 < leftMultiplicity t
  right_positive : ∀ t, 0 < rightMultiplicity t
  common_left : (primePowerProduct primes leftMultiplicity).val = DE.1
  common_right : (primePowerProduct primes rightMultiplicity).val = DE.2
  leftResidual : ι → A.Exterior
  rightResidual : κ → A.Exterior
  left_residual : ∀ i, (leftResidual i).val =
    supportResidual (fullI i).val (primeSupport DE.1)
  right_residual : ∀ j, (rightResidual j).val =
    supportResidual (fullJ j).val (primeSupport DE.1)
  leftGenerator : ι → A.R
  rightGenerator : κ → A.R
  left_generates : ∀ i, A.Generates (leftResidual i) (leftGenerator i)
  right_generates : ∀ j, A.Generates (rightResidual j) (rightGenerator j)

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

def FirstCommonCharacterBlock.leftColumns (b : FirstCommonCharacterBlock fullI fullJ DE)
    (left : Finset ι) : Finset ι :=
  left.filter (fun i => supportExtract (fullI i).val (primeSupport DE.1) = DE.1)

def FirstCommonCharacterBlock.rightColumns (b : FirstCommonCharacterBlock fullI fullJ DE)
    (right : Finset κ) : Finset κ :=
  right.filter (fun j => supportExtract (fullJ j).val (primeSupport DE.1) = DE.2)

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

def FirstCommonCharacterBlock.pair (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (j : κ) : ParentPeriodicPair K A.Sf Γ :=
  ((generatedOriginalColumn (σ := σ) hΓ (b.leftResidual i) (b.leftGenerator i)
      (b.left_generates i)).originalTriple
    (generatedOriginalColumn (σ := σ) hΓ (b.rightResidual j) (b.rightGenerator j)
      (b.right_generates j))
    (actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity) (profiles i j)).gated
    (IsCoprime (b.leftResidual i).val (b.rightResidual j).val)

def FirstCommonCharacterBlock.mask (b : FirstCommonCharacterBlock fullI fullJ DE)
    (M : Finset (HeightOneSpectrum A.R)) : Finset (HeightOneSpectrum A.R) :=
  M ∪ firstPrincipalPrimeMask b.primes b.leftMultiplicity b.rightMultiplicity

def FirstCommonCharacterBlock.finiteSource (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS) (left : Finset ι) (right : Finset κ)
    (profiles : ι → κ → SchwartzMap V ℂ) (M : Finset (HeightOneSpectrum A.R))
    (radius : {r : ℝ // 0 < r}) (X : ℝ) (hX : 1 ≤ X) :
    FirstFiniteSource K A.Sf Γ ι κ where
  leftColumns := b.leftColumns left
  rightColumns := b.rightColumns right
  pairs := b.pair hΓ C profiles
  mask := b.mask M
  radius := radius
  cutoff := X
  cutoff_ge_one := hX

theorem FirstCommonCharacterBlock.left_reconstruct (b : FirstCommonCharacterBlock fullI fullJ DE)
    (left : Finset ι) (i : ι) (hi : i ∈ b.leftColumns left) :
    (fullI i).val = (primePowerProduct b.primes b.leftMultiplicity).val *
      (b.leftResidual i).val := by
  have he := support_reconstruct (fullI i).val (fullI i).property.1 (primeSupport DE.1)
  rw [← b.left_residual i, (Finset.mem_filter.mp hi).2, ← b.common_left] at he
  exact he.symm

theorem FirstCommonCharacterBlock.right_reconstruct (b : FirstCommonCharacterBlock fullI fullJ DE)
    (right : Finset κ) (j : κ) (hj : j ∈ b.rightColumns right) :
    (fullJ j).val = (primePowerProduct b.primes b.rightMultiplicity).val *
      (b.rightResidual j).val := by
  have he := support_reconstruct (fullJ j).val (fullJ j).property.1 (primeSupport DE.1)
  rw [← b.right_residual j, (Finset.mem_filter.mp hj).2, ← b.common_right] at he
  exact he.symm

set_option maxHeartbeats 2000000 in
theorem firstActiveIdeal_dvd_common {τ : Type*} [Fintype τ] [DecidableEq τ]
    (p : τ → ExteriorPrime A) (m n : τ → ℕ) (hm : ∀ t, 0 < m t) :
    (firstActiveIdeal p m n).val ∣ (primePowerProduct p m).val := by
  change (∏ i : activeSupport Finset.univ m n, (p i.val).val.asIdeal ^ 1) ∣
    ∏ i : τ, (p i).val.asIdeal ^ m i
  simp only [pow_one, Finset.prod_coe_sort]
  apply dvd_trans (b := ∏ i ∈ activeSupport Finset.univ m n, (p i).val.asIdeal ^ m i)
  · apply Finset.prod_dvd_prod_of_dvd
    intro i hi
    simpa only [pow_one] using
      pow_dvd_pow ((p i).val.asIdeal) (Nat.succ_le_iff.mpr (hm i))
  · exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

theorem FirstCommonCharacterBlock.generator_coprime
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (hcop : IsCoprime (b.leftResidual i).val (b.rightResidual j).val) :
    IsCoprime (b.leftGenerator i)
        (b.rightGenerator j * firstActiveGenerator C b.primes b.leftMultiplicity b.rightMultiplicity) ∧
      IsCoprime (b.rightGenerator j)
        (firstActiveGenerator C b.primes b.leftMultiplicity b.rightMultiplicity) := by
  have hd : (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val ∣ DE.1 := by
    rw [← b.common_left]
    exact firstActiveIdeal_dvd_common b.primes _ _ b.left_positive
  have hleft := (extracted_residual_coprime (fullI i).val (fullI i).val (primeSupport DE.1)).symm
  have hright := (extracted_residual_coprime (fullI i).val (fullJ j).val (primeSupport DE.1)).symm
  rw [(Finset.mem_filter.mp hi).2, ← b.left_residual i] at hleft
  rw [(Finset.mem_filter.mp hi).2, ← b.right_residual j] at hright
  have hab := generated_elements_coprime (b.leftResidual i) (b.rightResidual j)
    (b.leftGenerator i) (b.rightGenerator j) (b.left_generates i) (b.right_generates j) hcop
  have har := generated_elements_coprime (b.leftResidual i)
    (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
    (b.leftGenerator i) (firstActiveGenerator C b.primes b.leftMultiplicity b.rightMultiplicity)
    (b.left_generates i) (firstActiveGenerator_generates C _ _ _)
    (hleft.of_isCoprime_of_dvd_right hd)
  have hbr := generated_elements_coprime (b.rightResidual j)
    (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
    (b.rightGenerator j) (firstActiveGenerator C b.primes b.leftMultiplicity b.rightMultiplicity)
    (b.right_generates j) (firstActiveGenerator_generates C _ _ _)
    (hright.of_isCoprime_of_dvd_right hd)
  exact ⟨hab.mul_right har, hbr⟩

variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]

/-- The actual complete label pool partitions the original first source. -/
theorem common_support_original_sources
    (C : A.GeneralArithmeticContext σ η hS) (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (afull : ι → A.R) (bfull : κ → A.R)
    (hafull : ∀ i, A.Generates (fullI i) (afull i))
    (hbfull : ∀ j, A.Generates (fullJ j) (bfull j))
    (blocks : ∀ DE ∈ commonSupportPool left right (fun i => (fullI i).val)
      (fun j => (fullJ j).val), FirstCommonCharacterBlock fullI fullJ DE)
    (profiles : ι → κ → SchwartzMap V ℂ)
    (ψ : ((v : (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R)) :
    (∑ i ∈ left, ∑ j ∈ right,
      ((generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).originalPair
        (generatedOriginalColumn (σ := σ) hΓ (fullJ j) (bfull j) (hbfull j))
        (profiles i j)).maskedSeries ψ radius M) =
      ∑ DE : commonSupportPool left right (fun i => (fullI i).val) (fun j => (fullJ j).val),
        ∑ i ∈ (blocks DE.val DE.property).leftColumns left,
        ∑ j ∈ (blocks DE.val DE.property).rightColumns right,
          ((blocks DE.val DE.property).pair hΓ C profiles i j).maskedSeries ψ radius
            ((blocks DE.val DE.property).mask M) := by
  rw [sum_common_support_blocks left right (fun i => (fullI i).val) (fun j => (fullJ j).val)]
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro DE _
  let b := blocks DE.val DE.property
  change (∑ i ∈ b.leftColumns left, ∑ j ∈ b.rightColumns right,
    if IsCoprime (supportResidual (fullI i).val (primeSupport DE.val.1))
        (supportResidual (fullJ j).val (primeSupport DE.val.1)) then _ else 0) = _
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← b.left_residual i, ← b.right_residual j]
  unfold FirstCommonCharacterBlock.pair
  rw [ParentPeriodicPair.gated_maskedSeries]
  split_ifs with hcop
  · exact actual_first_character_source_series hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity b.left_positive b.right_positive
      (b.leftResidual i) (b.rightResidual j) (fullI i) (fullJ j)
      (b.left_reconstruct left i hi) (b.right_reconstruct right j hj)
      (b.leftGenerator i) (b.rightGenerator j) (afull i) (bfull j)
      (b.left_generates i) (b.right_generates j) (hafull i) (hbfull j)
      (profiles i j) ψ radius M
  · rfl

variable [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]

/-- First-stage kernel Cauchy on the literal complete common-support block. -/
theorem FirstCommonCharacterBlock.kernel_bound
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (M : Finset (HeightOneSpectrum A.R)) (radius : {r : ℝ // 0 < r}) (X : ℝ) (hX : 1 ≤ X)
    (D : Finset (HeightOneSpectrum A.R))
    (F : 𝓢(E, ℂ)) (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (q : Q → ℂ) (c : ι → ℂ) (d : κ → ℂ) (x : ι → E) (y : κ → E) (z : Q → E)
    (hphase : ∀ i j, IsCoprime (b.leftResidual i).val (b.rightResidual j).val →
      firstReciprocalPhase
        (generatedOriginalColumn (σ := σ) hΓ (b.leftResidual i) (b.leftGenerator i) (b.left_generates i))
        (generatedOriginalColumn (σ := σ) hΓ (b.rightResidual j) (b.rightGenerator j)
          (b.right_generates j)) = (phaseTable (rayLeft i, rayRight j) : ℂ))
    (hprofile : ∀ t ∈ (b.finiteSource hΓ C left right profiles M radius X hX).rows,
      ∀ i ∈ b.leftColumns left, ∀ j ∈ b.rightColumns right,
      IsCoprime (b.leftResidual i).val (b.rightResidual j).val →
      ((generatedOriginalColumn (σ := σ) hΓ (b.leftResidual i) (b.leftGenerator i)
          (b.left_generates i)).originalTriple
        (generatedOriginalColumn (σ := σ) hΓ (b.rightResidual j) (b.rightGenerator j)
          (b.right_generates j))
        (actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity) (profiles i j)).transformedProfile
            μv finiteTest radius D t = q t * (c i * star (d j)) * F (z t + x i + y j)) :
    let source := b.finiteSource hΓ C left right profiles M radius X hX
    let a := fun i => generatedOriginalColumn (σ := σ) hΓ
      (b.leftResidual i) (b.leftGenerator i) (b.left_generates i)
    let a' := fun j => generatedOriginalColumn (σ := σ) hΓ
      (b.rightResidual j) (b.rightGenerator j) (b.right_generates j)
    let r := actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity
    let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
    let common := fun t : Q => (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
      (r.character (Ideal.Quotient.mk _ δ) *
        actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff r.modulus r.nonzero r.character t.out.val)
    ‖∑ t ∈ source.rows, ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
      (source.pairs i j).transformedRow μv hDiff finiteTest radius D t‖ ≤
      firstResidualKernelCost hDiff Ray F source.rows (fun t => t.out.val)
        source.leftColumns source.rightColumns
        (fun i => (b.leftResidual i).val) (fun j => (b.rightResidual j).val)
        a a' rayLeft rayRight phaseTable common q
        (fun i => c i * firstLeftDivisorFactor (a i) r δ)
        (fun j => d j * firstRightDivisorFactor (a' j) r δ) x y := by
  dsimp only
  have hb := first_source_kernel_bound hDiff Ray μv F
    (b.finiteSource hΓ C left right profiles M radius X hX).rows
    (b.leftColumns left) (b.rightColumns right)
    (fun i => (b.leftResidual i).val) (fun j => (b.rightResidual j).val)
    (fun j _ => (b.rightResidual j).property.1)
    (fun i => generatedOriginalColumn (σ := σ) hΓ
      (b.leftResidual i) (b.leftGenerator i) (b.left_generates i))
    (fun j => generatedOriginalColumn (σ := σ) hΓ
      (b.rightResidual j) (b.rightGenerator j) (b.right_generates j))
    (actualActiveColumn hΓ C b.primes b.primes_injective b.leftMultiplicity b.rightMultiplicity)
    profiles (fun i hi j hj hc => b.generator_coprime C left right i hi j hj hc)
    rayLeft rayRight phaseTable hphase finiteTest radius D q c d x y z hprofile
  simpa only [FirstCommonCharacterBlock.finiteSource, FirstCommonCharacterBlock.pair,
    ParentPeriodicPair.gated_transformedRow] using hb

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.common_support_original_sources
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.kernel_bound

