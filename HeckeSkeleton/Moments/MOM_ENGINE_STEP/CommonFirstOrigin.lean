import HeckeSkeleton.Moments.MOM_ENGINE_STEP.WholeGramOrigin

/-!
# The original additive origin through the first common-support split

The first principal mask is an actual inclusion-exclusion mask even at
the additive origin.  The pointwise normalized-character identity holds
there too, so summing all original mask divisors transports the origin
through the first common-support split without an annularity assumption.

The complete original Gram source, before its common-support partition,
has a square at zero.  Positivity is used only after all original common
labels have been reassembled.  No positivity of an individual block is
required, and no multiplicative character at zero is replaced by a
Gauss residue at zero.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory UniqueFactorizationMonoid
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments
open HeckePort.Moments.Active HeckePort.Moments.Support
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

section Mask

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- At zero every original mask-divisor membership indicator is one.
The complete Möbius sum is still the literal avoidance mask. -/
theorem origin_mask_moebius_sum (M : Finset (HeightOneSpectrum R)) :
    (∑ D ∈ M.powerset, (moebius (IdealMobiusMask.primeProduct D) : ℂ)) =
      IdealMobiusMask.avoidanceMask M (0 : R) := by
  simpa [IdealMobiusMask.membershipIndicator] using
    (IdealMobiusMask.avoidanceMask_moebius_expansion M (0 : R)).symm

theorem origin_mask_union (M N : Finset (HeightOneSpectrum R)) (x : R) :
    IdealMobiusMask.avoidanceMask (M ∪ N) x =
      IdealMobiusMask.avoidanceMask M x * IdealMobiusMask.avoidanceMask N x := by
  simp only [IdealMobiusMask.avoidanceMask, Finset.mem_union, or_imp, forall_and]
  split_ifs <;> simp_all

/-- A nonempty principal mask cancels its full additive-origin sum. -/
theorem origin_mask_zero (M : Finset (HeightOneSpectrum R)) :
    IdealMobiusMask.avoidanceMask M (0 : R) = if M = ∅ then 1 else 0 := by
  by_cases hM : M = ∅
  · simp [hM, IdealMobiusMask.avoidanceMask]
  · have hnot : ¬ ∀ p ∈ M, (0 : R) ∉ p.asIdeal := by
      intro h
      obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hM
      exact h p hp p.asIdeal.zero_mem
    simp only [IdealMobiusMask.avoidanceMask, if_neg hnot, if_neg hM]

end Mask

variable {K : Type} [Field K] [NumberField K]

section OriginalGram

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex]

/-- The complete actual divisor sum at the original additive origin. -/
theorem ParentPeriodicPair.sum_originZero_powerset (p : ParentPeriodicPair K S Γ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum
      (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))) :
    (∑ D ∈ M.powerset, p.originZero h D) =
      IdealMobiusMask.avoidanceMask M 0 * p.originZero h ∅ := by
  rw [p.originZero_empty, ← origin_mask_moebius_sum M]
  simp only [ParentPeriodicPair.originZero, Finset.sum_mul, mul_assoc]

theorem OrbitalGaussColumn.originalPair_residue_zero
    (a b : OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ) :
    (a.originalPair b φ).residue 0 = a.character 0 * star (b.character 0) := by
  simp only [OrbitalGaussColumn.originalPair, map_zero]

theorem OrbitalGaussColumn.originalTriple_residue_zero
    (a b r : OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ) :
    (a.originalTriple b r φ).residue 0 =
      a.character 0 * star (b.character 0) * r.character 0 := by
  letI := finite_sIntegerPrincipalResidue K
    (S : Set (HeightOneSpectrum (𝓞 K))) b.modulus b.nonzero
  simp only [OrbitalGaussColumn.originalTriple, map_zero, MulChar.star_apply']

theorem OrbitalGaussColumn.originalPair_originZero_empty
    (c d : OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (a b : ℂ) (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    (c.originalPair d ((a * star b) • φ)).originZero h ∅ =
      ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
        sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0 *
          ((a * c.character 0) * star (b * d.character 0)) := by
  rw [ParentPeriodicPair.originZero_empty, originalPair_residue_zero]
  change _ * (_ * sIntegerTensorTerm K S
    (traceSchwartzToMixed K ((a * star b) • φ)) h 0) = _
  rw [originalTensor_smul, star_mul]
  ring

/-- The first source uses the original multiplicative characters at
zero, with their true values also on the unit quotient. -/
theorem original_originZero_sum_eq_square
    {ι : Type*} (columns : Finset ι) (coefficient : ι → ℂ)
    (col : ι → OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    (∑ i ∈ columns, ∑ j ∈ columns,
      ((col i).originalPair (col j)
        ((coefficient i * star (coefficient j)) • φ)).originZero h ∅) =
      ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
        sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0 *
          ((‖∑ i ∈ columns, coefficient i * (col i).character 0‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def]
  simp only [OrbitalGaussColumn.originalPair_originZero_empty, star_sum,
    Finset.sum_mul_sum, Finset.mul_sum]

theorem original_originZero_sum_nonneg
    {ι : Type*} (columns : Finset ι) (coefficient : ι → ℂ)
    (col : ι → OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hpositive : 0 ≤ (sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0).re) :
    0 ≤ (∑ i ∈ columns, ∑ j ∈ columns,
      ((col i).originalPair (col j)
        ((coefficient i * star (coefficient j)) • φ)).originZero h ∅).re := by
  rw [original_originZero_sum_eq_square]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg hpositive) (sq_nonneg _)

theorem canonical_rowBall_original_originZero_sum_nonneg
    {ι : Type*} (columns : Finset ι) (coefficient : ι → ℂ)
    (col : ι → OrbitalGaussColumn K S Γ) (B : ℝ) :
    0 ≤ (∑ i ∈ columns, ∑ j ∈ columns,
      ((col i).originalPair (col j)
        ((coefficient i * star (coefficient j)) • CanonicalRowBall.archTest K S B)).originZero
          (rowBallFiniteFamily K S B) ∅).re := by
  apply original_originZero_sum_nonneg
  rw [CanonicalRowBall.originalTensor_zero, Complex.ofReal_re]
  exact inv_nonneg.mpr (CanonicalRowBall.mass_pos K S).le

theorem canonical_rowBall_original_masked_originZero_sum_nonneg
    {ι : Type*} (columns : Finset ι) (coefficient : ι → ℂ)
    (col : ι → OrbitalGaussColumn K S Γ) (B : ℝ)
    (M : Finset (HeightOneSpectrum
      (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))) :
    0 ≤ (∑ i ∈ columns, ∑ j ∈ columns, ∑ D ∈ M.powerset,
      ((col i).originalPair (col j)
        ((coefficient i * star (coefficient j)) • CanonicalRowBall.archTest K S B)).originZero
          (rowBallFiniteFamily K S B) D).re := by
  by_cases hM : M = ∅
  · subst M
    simpa only [Finset.powerset_empty, Finset.sum_singleton] using
      canonical_rowBall_original_originZero_sum_nonneg columns coefficient col B
  · simp only [ParentPeriodicPair.sum_originZero_powerset, origin_mask_zero,
      if_neg hM, zero_mul, Finset.sum_const_zero, Complex.zero_re, le_refl]

end OriginalGram

section FirstCommon

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

/-- The principal-mask identity is valid on all ring elements, including
zero; it is not limited to the nonzero orbital carrier. -/
theorem firstPrincipalMask_eq_element_mask
    (C : A.GeneralArithmeticContext σ η hS)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (x : A.R) :
    firstPrincipalMask C p m n x =
      IdealMobiusMask.avoidanceMask (firstPrincipalPrimeMask p m n) x := by
  unfold firstPrincipalMask IdealMobiusMask.avoidanceMask
  have he :
      (∀ q ∈ firstPrincipalPrimeMask p m n, x ∉ q.asIdeal) ↔
        ¬ ∃ i ∈ principalSupport Finset.univ m n, generator C (p i) ∣ x := by
    simp only [firstPrincipalPrimeMask, Finset.mem_image, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂, not_exists, not_and]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    change x ∉ A.extendIdeal (primeIdeal (p i)) ↔ ¬ generator C (p i) ∣ x
    rw [← (generator_generates C (p i)).2, Ideal.mem_span_singleton]
  by_cases hp : ∃ i ∈ principalSupport Finset.univ m n, generator C (p i) ∣ x <;>
    simp only [he, hp, if_true, if_false, not_true_eq_false, not_false_eq_true]

@[simp] theorem generatedOriginalColumn_character_zero
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    (generatedOriginalColumn (σ := σ) hΓ I a ha).character 0 =
      σ (A.sexticResidue I 0) := by
  simpa only [map_zero] using
    generatedOriginalColumn_character_mk (σ := σ) hΓ I a ha (0 : A.R)

variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex]

/-- The exact first character decomposition at zero, after summing all
literal mask divisors on both sides. -/
theorem actual_first_character_originZero
    (C : A.GeneralArithmeticContext σ η hS)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (IA IB IFull JFull : A.Exterior)
    (hI : IFull.val = (primePowerProduct p m).val * IA.val)
    (hJ : JFull.val = (primePowerProduct p n).val * IB.val)
    (a b afull bfull : A.R)
    (ha : A.Generates IA a) (hb : A.Generates IB b)
    (hafull : A.Generates IFull afull) (hbfull : A.Generates JFull bfull)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum A.R)) :
    (∑ D ∈ M.powerset,
      ((generatedOriginalColumn (σ := σ) hΓ IFull afull hafull).originalPair
        (generatedOriginalColumn (σ := σ) hΓ JFull bfull hbfull) φ).originZero finiteTest D) =
    ∑ D ∈ (M ∪ firstPrincipalPrimeMask p m n).powerset,
      ((generatedOriginalColumn (σ := σ) hΓ IA a ha).originalTriple
        (generatedOriginalColumn (σ := σ) hΓ IB b hb)
        (actualActiveColumn hΓ C p hp m n) φ).originZero finiteTest D := by
  have he := actual_full_pair_active C p hp m n hm hn IA IB IFull JFull hI hJ (0 : A.R)
  simp only [map_zero] at he
  rw [ParentPeriodicPair.sum_originZero_powerset,
    ParentPeriodicPair.sum_originZero_powerset, origin_mask_union,
    ← firstPrincipalMask_eq_element_mask C p m n 0,
    ParentPeriodicPair.originZero_empty, ParentPeriodicPair.originZero_empty,
    OrbitalGaussColumn.originalPair_residue_zero,
    OrbitalGaussColumn.originalTriple_residue_zero]
  simp only [generatedOriginalColumn_character_zero]
  rw [he]
  dsimp only [OrbitalGaussColumn.originalPair, OrbitalGaussColumn.originalTriple,
    actualActiveColumn]
  ring

/-- Every complete original first common label is reassembled, with its
actual principal mask and residual-coprimality gate. -/
theorem common_support_original_originZeroTerm
    (C : A.GeneralArithmeticContext σ η hS)
    {ι κ : Type*} (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (afull : ι → A.R) (bfull : κ → A.R)
    (hafull : ∀ i, A.Generates (fullI i) (afull i))
    (hbfull : ∀ j, A.Generates (fullJ j) (bfull j))
    (blocks : ∀ DE ∈ commonSupportPool left right (fun i => (fullI i).val)
      (fun j => (fullJ j).val), FirstCommonCharacterBlock fullI fullJ DE)
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
    (X : ℝ) (hX : 1 ≤ X) :
    (∑ DE : commonSupportPool left right (fun i => (fullI i).val) (fun j => (fullJ j).val),
      ((blocks DE.val DE.property).finiteSource hΓ C left right profiles M radius X hX).originZeroTerm
        finiteTest) =
      ∑ i ∈ left, ∑ j ∈ right, ∑ D ∈ M.powerset,
        ((generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).originalPair
          (generatedOriginalColumn (σ := σ) hΓ (fullJ j) (bfull j) (hbfull j))
          (profiles i j)).originZero finiteTest D := by
  symm
  rw [sum_common_support_blocks left right (fun i => (fullI i).val) (fun j => (fullJ j).val)]
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro DE _
  let b := blocks DE.val DE.property
  change (∑ i ∈ b.leftColumns left, ∑ j ∈ b.rightColumns right,
    if IsCoprime (supportResidual (fullI i).val (primeSupport DE.val.1))
        (supportResidual (fullJ j).val (primeSupport DE.val.1)) then _ else 0) =
    ∑ i ∈ b.leftColumns left, ∑ j ∈ b.rightColumns right,
      ∑ D ∈ (b.mask M).powerset, (b.pair hΓ C profiles i j).originZero finiteTest D
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← b.left_residual i, ← b.right_residual j]
  unfold FirstCommonCharacterBlock.pair
  by_cases hcop : IsCoprime (b.leftResidual i).val (b.rightResidual j).val
  · rw [if_pos hcop, ParentPeriodicPair.gated_of_true _ _ hcop]
    exact actual_first_character_originZero hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity b.left_positive b.right_positive
      (b.leftResidual i) (b.rightResidual j) (fullI i) (fullJ j)
      (b.left_reconstruct left i hi) (b.right_reconstruct right j hj)
      (b.leftGenerator i) (b.rightGenerator j) (afull i) (bfull j)
      (b.left_generates i) (b.right_generates j) (hafull i) (hbfull j)
      (profiles i j) finiteTest M
  · simp only [if_neg hcop, ParentPeriodicPair.originZero, ParentPeriodicPair.gated,
      if_neg hcop, zero_mul, mul_zero, Finset.sum_const_zero]

/-- The canonical first row-ball origin is nonnegative only after its
entire actual common-support family has been summed. -/
theorem common_support_canonical_original_origin_nonneg
    (C : A.GeneralArithmeticContext σ η hS)
    {ι : Type*} (columns : Finset ι) (I : ι → A.Exterior)
    (generator : ι → A.R) (generates : ∀ i, A.Generates (I i) (generator i))
    (blocks : ∀ DE ∈ commonSupportPool columns columns (fun i => (I i).val)
      (fun j => (I j).val), FirstCommonCharacterBlock I I DE)
    (coefficient : ι → ℂ) (B : ℝ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
    (X : ℝ) (hX : 1 ≤ X) :
    0 ≤ (∑ DE : commonSupportPool columns columns (fun i => (I i).val) (fun j => (I j).val),
      ((blocks DE.val DE.property).finiteSource hΓ C columns columns
        (fun i j => (coefficient i * star (coefficient j)) • CanonicalRowBall.archTest K A.Sf B)
        M radius X hX).originZeroTerm (rowBallFiniteFamily K A.Sf B)).re := by
  rw [common_support_original_originZeroTerm hΓ C columns columns I I
    generator generator generates generates blocks]
  exact canonical_rowBall_original_masked_originZero_sum_nonneg columns coefficient
    (fun i => generatedOriginalColumn (σ := σ) hΓ (I i) (generator i) (generates i)) B M

end FirstCommon

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentPeriodicPair.sum_originZero_powerset
#print axioms HeckeSkeleton.Moments.EngineStep.original_originZero_sum_eq_square
#print axioms HeckeSkeleton.Moments.EngineStep.actual_first_character_originZero
#print axioms HeckeSkeleton.Moments.EngineStep.common_support_original_originZeroTerm
#print axioms HeckeSkeleton.Moments.EngineStep.common_support_canonical_original_origin_nonneg
