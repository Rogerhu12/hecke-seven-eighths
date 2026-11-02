import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroLocal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ForcedPowerfulDiagonal

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original first divisor in the signed second zero

The complete Gauss origin has stronger support than a general powerful
ideal: every prime exponent of either original modulus is divisible by
six. Thus the product in either the dual Euler term or the origin term
is a square. A squarefree original first divisor still divides its
square root. Counting that root retains the full inverse divisor norm,
including for the signed zero used by the V2 contract.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory UniqueFactorizationMonoid
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- The actual local exponent theorem is transported to arbitrary
original generators before constructing a square root of the ideal. -/
theorem generated_residue_zero_square
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (hnonzero : (generatedOriginalColumn (σ := σ) hΓ I a ha).residue hDiff 0 ≠ 0) :
    ∃ root : Ideal (𝓞 K), I.val = root ^ 2 := by
  let p := exteriorPrimeOfSupport I
  let n := fun P : primeSupport I.val => (normalizedFactors I.val).count P.val
  have hp : Function.Injective p := by
    intro P Q hPQ
    apply Subtype.ext
    exact congrArg (fun q : ExteriorPrime A => q.val.asIdeal) hPQ
  have hn : ∀ P : primeSupport I.val, 0 < n P := by
    intro P
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property)
  have hrecipe : primePowerProduct p n = I := exterior_support_primePowerProduct I
  let b := primePowerProductGenerator C p n
  have hb : A.Generates I b := hrecipe ▸ primePowerProduct_generates C p n
  letI : Finite (A.R ⧸ Ideal.span {a}) := by
    rw [ha.2]
    exact A.exteriorResidue_finite I
  letI : Fintype (A.R ⧸ Ideal.span {a}) := Fintype.ofFinite _
  letI : Finite (A.R ⧸ Ideal.span {b}) := by
    rw [hb.2]
    exact A.exteriorResidue_finite I
  letI : Fintype (A.R ⧸ Ideal.span {b}) := Fintype.ofFinite _
  let T := actualSIntegerTrace K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff
  have hazero : completeResidueGauss T a (generatedIdealCharacter (σ := σ) I a ha) 0 ≠ 0 := by
    change completeResidueGauss T a (generatedIdealCharacter (σ := σ) I a ha) 0 ≠ 0 at hnonzero
    exact hnonzero
  have hbzero : completeResidueGauss T b (generatedIdealCharacter (σ := σ) I b hb) 0 ≠ 0 := by
    rw [← generated_zero_gauss_generator_change T I a b ha hb]
    exact hazero
  have hbzero' : completeResidueGauss T (primePowerProductGenerator C p n)
      (generatedIdealCharacter (σ := σ) (primePowerProduct p n)
        (primePowerProductGenerator C p n) (primePowerProduct_generates C p n)) 0 ≠ 0 := by
    simpa only [b, hrecipe] using hbzero
  have hsix := actual_zero_gauss_nonzero_exponents C T p hp n hn hbzero'
  refine ⟨∏ P : primeSupport I.val, P.val ^ (n P / 2), ?_⟩
  calc
    I.val = (primePowerProduct p n).val := congrArg Subtype.val hrecipe.symm
    _ = (∏ P : primeSupport I.val, P.val ^ (n P / 2)) ^ 2 := by
      rw [← Finset.prod_pow]
      change (∏ P : primeSupport I.val, P.val ^ n P) =
        ∏ P : primeSupport I.val, (P.val ^ (n P / 2)) ^ 2
      apply Finset.prod_congr rfl
      intro P _
      rw [← pow_mul, Nat.div_mul_cancel ((by norm_num : 2 ∣ 6).trans (hsix P))]

/-- No diagonal equality is asserted for the origin. Each separate
modulus is a square, and the original product is their product square. -/
theorem generated_originZero_square
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (I J : A.Exterior) (a b : A.R) (ha : A.Generates I a) (hb : A.Generates J b)
    (φ : SchwartzMap V ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (D : Finset (HeightOneSpectrum A.R))
    (hnonzero : ((generatedOriginalColumn (σ := σ) hΓ I a ha).pair hDiff
      (generatedOriginalColumn (σ := σ) hΓ J b hb) φ).originZero finiteTest D ≠ 0) :
    ∃ root : Ideal (𝓞 K), I.val * J.val = root ^ 2 := by
  have hres :
      (generatedOriginalColumn (σ := σ) hΓ I a ha).residue hDiff 0 *
        star ((generatedOriginalColumn (σ := σ) hΓ J b hb).residue hDiff 0) ≠ 0 := by
    intro hz
    apply hnonzero
    rw [ParentPeriodicPair.originZero, OrbitalGaussColumn.pair_residue_zero,
      hz, zero_mul, mul_zero]
  obtain ⟨rI, hrI⟩ := generated_residue_zero_square hΓ C hDiff I a ha
    (mul_ne_zero_iff.mp hres).1
  obtain ⟨rJ, hrJ⟩ := generated_residue_zero_square hΓ C hDiff J b hb
    (fun hz => (mul_ne_zero_iff.mp hres).2 (by rw [hz, star_zero]))
  exact ⟨rI * rJ, by rw [hrI, hrJ, mul_pow]⟩

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

theorem second_originZero_square
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (D : Finset (HeightOneSpectrum A.R))
    (hnonzero : (b.secondPair hΓ hDiff C profiles i j).originZero finiteTest D ≠ 0) :
    ∃ root : Ideal (𝓞 K), (fullI i).val * (fullJ j).val = root ^ 2 := by
  unfold FirstCommonCharacterBlock.secondPair at hnonzero
  rw [ParentPeriodicPair.gated_originZero] at hnonzero
  split_ifs at hnonzero with hcop
  · have he := generated_originZero_square hΓ C hDiff
      (b.secondLeftIdeal i) (b.secondRightIdeal j) _ _
      (b.secondLeft_generates C i) (b.secondRight_generates C j)
      (profiles i j) finiteTest D hnonzero
    simpa only [b.secondLeftIdeal_eq left i hi,
      b.secondRightIdeal_eq right j hj] using he
  · exact False.elim (hnonzero rfl)

/-- A squarefree first divisor remains in a square root of the full
product. This uses the actual ideal factorization, not a norm surrogate. -/
theorem squarefree_dvd_square_root (D root : Ideal (𝓞 K))
    (hD : Squarefree D) (hroot : root ≠ 0) (hdiv : D ∣ root ^ 2) : D ∣ root := by
  have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hD.ne_zero
    (pow_ne_zero 2 hroot)).mp hdiv
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hD.ne_zero hroot).mpr
  rw [Multiset.le_iff_count]
  intro P
  have hP := Multiset.count_le_of_le P hle
  rw [normalizedFactors_pow, Multiset.count_nsmul] at hP
  have hDone := Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors hD.ne_zero).mp hD) P
  omega

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- A nonzero signed zero term has an actual square product. The
two possible contributions keep their distinct support arguments. -/
theorem second_signedZero_square
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (haδ : IsCoprime (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hbδ : IsCoprime (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hnonzero : (b.secondPair hΓ hDiff C profiles i j).transformedZero
      μv hDiff finiteTest radius D ≠ 0) :
    ∃ root : Ideal (𝓞 K), (fullI i).val * (fullJ j).val = root ^ 2 := by
  by_cases hd : (b.secondPair hΓ hDiff C profiles i j).dualZero
      μv hDiff finiteTest radius D = 0
  · have ho : (b.secondPair hΓ hDiff C profiles i j).originZero finiteTest D ≠ 0 := by
      intro hz
      apply hnonzero
      rw [ParentPeriodicPair.transformedZero_eq_dual_sub_origin, hd, hz, sub_self]
    exact second_originZero_square hΓ b C hDiff finiteTest left right profiles i hi j hj D ho
  · have he : fullI i = fullJ j := by
      by_contra hne
      exact hd (b.secondDualZero_of_ne hΓ μv C hDiff finiteTest left right profiles
        i hi j hj hne radius D haδ hbδ)
    exact ⟨(fullI i).val, by rw [← he, pow_two]⟩

/-- The actual signed second zero retains the complete inverse norm
of a squarefree first residual divisor. Both the Euler diagonal and
the Gauss origin are counted through their actual square root ideals. -/
theorem second_signedZero_diagonal_supported_of_squarefree_divisor
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ (C : A.GeneralArithmeticContext σ η hS) {ι κ : Type*}
      (left : Finset ι) (right : Finset κ)
      (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior),
    ∀ blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val,
    ∀ (profiles : ι → κ → SchwartzMap V ℂ)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
      (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
      (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
      (factors : ι × κ → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ),
    (∀ v, ((left ×ˢ right).filter (fun ij => factors ij = v)).card ≤ multiplicity) →
    (∀ ij ∈ left ×ˢ right, PowerfulDiagonal.tupleIdeal (factors ij) =
      (fullI ij.1).val * (fullJ ij.2).val) →
    ∀ (S : Ideal (𝓞 K)), Squarefree S →
    (∀ ij ∈ left ×ˢ right, profiles ij.1 ij.2 ≠ 0 → S ∣ (fullI ij.1).val) →
    ∀ N Amp : ℝ, 1 ≤ N → 0 ≤ Amp →
    (∀ ij ∈ left ×ˢ right, profiles ij.1 ij.2 ≠ 0 →
      (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ N) →
    (∀ DE, ∀ i ∈ (blocks DE).leftColumns left, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonLeftIdeal * (blocks DE).leftGenerator i)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ DE, ∀ j ∈ (blocks DE).rightColumns right, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonRightIdeal * (blocks DE).rightGenerator j)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ v ∈ firstZeroPairs left right fullI fullJ,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        (∑ D ∈ M.powerset,
          (firstZeroDivisorWeight radius D * A.exteriorNorm (fullI v.2.1) +
            ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
              A.exteriorNorm (fullI v.2.1) * A.exteriorNorm (fullJ v.2.2))) ≤
          Amp / Real.sqrt N) →
    (∑ DE, ‖((blocks DE).secondFiniteSource hΓ hDiff C left right profiles M radius cutoff hcutoff).zeroTerm
      μv hDiff finiteTest‖) ≤ Cbound * multiplicity * Amp * N ^ ε /
        (Ideal.absNorm S : ℝ) := by
  obtain ⟨seminorms, C₀, hC₀, hzero⟩ :=
    second_signedZero_amplitude_uniform (σ := σ) hΓ μv finiteTest
  obtain ⟨Cdiag, hCdiag, hdiag⟩ :=
    ForcedPowerfulDiagonal.square_tuple_card_of_fibers (K := K) k ε hε
  refine ⟨seminorms, Cdiag * (1 + C₀), mul_pos hCdiag (by linarith), ?_⟩
  intro C ι κ left right fullI fullJ blocks profiles hDiff radius M cutoff hcutoff
    factors multiplicity hfiber hfactor S hSsquare hSdiv N Amp hN hAmp hnorm hleftmask hrightmask hprofile
  let allPairs := firstZeroPairs left right fullI fullJ
  let amp := secondZeroPairAmplitude hΓ μv C left right fullI fullJ
    blocks profiles hDiff finiteTest radius M
  let pairs := allPairs.filter (fun v => amp v ≠ 0)
  have hampnonneg (v : FirstZeroLabel left right fullI fullJ × (ι × κ)) : 0 ≤ amp v := norm_nonneg _
  have hmem (v) (hv : v ∈ allPairs) := (mem_firstZeroPairs left right fullI fullJ v).mp hv
  have hblock (v) (hv : v ∈ allPairs) :
      v.2.1 ∈ (blocks v.1).leftColumns left ∧
      v.2.2 ∈ (blocks v.1).rightColumns right ∧
      IsCoprime ((blocks v.1).leftResidual v.2.1).val ((blocks v.1).rightResidual v.2.2).val :=
    ((blocks v.1).mem_iff_label left right
      (commonSupportPool_support_eq left right (fun i => (fullI i).val)
        (fun j => (fullJ j).val) v.1.val v.1.property) _ _).mpr (hmem v hv)
  have hpoint (v) (hv : v ∈ allPairs) : amp v ≤
      C₀ * (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        (∑ D ∈ M.powerset,
          (firstZeroDivisorWeight radius D * A.exteriorNorm (fullI v.2.1) +
            ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
              A.exteriorNorm (fullI v.2.1) * A.exteriorNorm (fullJ v.2.2)))) := by
    change ‖∑ D ∈ M.powerset,
      ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
        μv hDiff finiteTest radius D‖ ≤ _
    calc
      _ ≤ ∑ D ∈ M.powerset,
          ‖((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
            μv hDiff finiteTest radius D‖ := norm_sum_le _ _
      _ ≤ ∑ D ∈ M.powerset,
          C₀ * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
            (firstZeroDivisorWeight radius D * A.exteriorNorm (fullI v.2.1) +
              ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
                A.exteriorNorm (fullI v.2.1) * A.exteriorNorm (fullJ v.2.2)) := by
        apply Finset.sum_le_sum
        intro D hD
        exact hzero C fullI fullJ v.1.val (blocks v.1) left right profiles hDiff
          v.2.1 (hblock v hv).1 v.2.2 (hblock v hv).2.1 radius D
          (hleftmask v.1 _ (hblock v hv).1 D hD)
          (hrightmask v.1 _ (hblock v hv).2.1 D hD)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hall (v) (hv : v ∈ pairs) : v ∈ allPairs := (Finset.mem_filter.mp hv).1
  have hij (v) (hv : v ∈ allPairs) : v.2 ∈ left ×ˢ right :=
    Finset.mem_product.mpr ⟨(hmem v hv).1, (hmem v hv).2.1⟩
  have hfiber' (w : Fin k → Ideal (𝓞 K)) :
      (pairs.filter (fun v => factors v.2 = w)).card ≤ multiplicity := by
    let T := pairs.filter (fun v => factors v.2 = w)
    have hi : Set.InjOn
        (fun v : FirstZeroLabel left right fullI fullJ × (ι × κ) => v.2)
        (T : Set (FirstZeroLabel left right fullI fullJ × (ι × κ))) := by
      intro v hv u hu he
      exact firstZeroPairs_projection_injective left right fullI fullJ
        (hall v (Finset.mem_filter.mp hv).1)
        (hall u (Finset.mem_filter.mp hu).1) he
    have hs : T.image Prod.snd ⊆ (left ×ˢ right).filter (fun ij => factors ij = w) := by
      intro ij hij'
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hij'
      exact Finset.mem_filter.mpr
        ⟨hij v (hall v (Finset.mem_filter.mp hv).1), (Finset.mem_filter.mp hv).2⟩
    have hc := (Finset.card_le_card hs).trans (hfiber w)
    rw [Finset.card_image_of_injOn hi] at hc
    exact hc
  have hcoef (v) (hv : v ∈ pairs) : amp v ≤ (C₀ * Amp) / Real.sqrt N := by
    calc
      _ ≤ C₀ * (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
          (∑ D ∈ M.powerset,
            (firstZeroDivisorWeight radius D * A.exteriorNorm (fullI v.2.1) +
              ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
                A.exteriorNorm (fullI v.2.1) * A.exteriorNorm (fullJ v.2.2)))) :=
          hpoint v (hall v hv)
      _ ≤ C₀ * (Amp / Real.sqrt N) :=
        mul_le_mul_of_nonneg_left (hprofile v (hall v hv)) hC₀
      _ = _ := by ring
  have hprofileNonzero (v) (hv : v ∈ pairs) : profiles v.2.1 v.2.2 ≠ 0 := by
    intro hφ
    have hp : amp v ≤ 0 := by
      simpa only [hφ, map_zero, zero_mul, mul_zero] using hpoint v (hall v hv)
    exact (Finset.mem_filter.mp hv).2 (le_antisymm hp (hampnonneg v))
  have hsquare (v) (hv : v ∈ pairs) :
      ∃ root : Ideal (𝓞 K), (fullI v.2.1).val * (fullJ v.2.2).val = root ^ 2 := by
    have hav := hall v hv
    have hex : ∃ D ∈ M.powerset,
        ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
          μv hDiff finiteTest radius D ≠ 0 := by
      by_contra hn
      apply (Finset.mem_filter.mp hv).2
      change ‖∑ D ∈ M.powerset,
        ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
          μv hDiff finiteTest radius D‖ = 0
      have hz : ∀ D ∈ M.powerset,
          ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
            μv hDiff finiteTest radius D = 0 := by
        intro D hD
        by_contra hterm
        exact hn ⟨D, hD, hterm⟩
      rw [Finset.sum_eq_zero hz, norm_zero]
    obtain ⟨D, hD, hterm⟩ := hex
    exact second_signedZero_square hΓ μv (blocks v.1) C hDiff finiteTest
      left right profiles v.2.1 (hblock v hav).1 v.2.2 (hblock v hav).2.1
      radius D (hleftmask v.1 _ (hblock v hav).1 D hD)
      (hrightmask v.1 _ (hblock v hav).2.1 D hD) hterm
  let root : FirstZeroLabel left right fullI fullJ × (ι × κ) → Ideal (𝓞 K) :=
    fun v => if hv : v ∈ pairs then (hsquare v hv).choose else 1
  have hroot (v) (hv : v ∈ pairs) :
      (fullI v.2.1).val * (fullJ v.2.2).val = root v ^ 2 := by
    simp only [root, dif_pos hv]
    exact (hsquare v hv).choose_spec
  have hrootzero (v) (hv : v ∈ pairs) : root v ≠ 0 := by
    intro hz
    have he := hroot v hv
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at he
    exact (mul_ne_zero (fullI v.2.1).property.1 (fullJ v.2.2).property.1) he
  have hrootdiv (v) (hv : v ∈ pairs) : S ∣ root v := by
    apply squarefree_dvd_square_root S (root v) hSsquare (hrootzero v hv)
    rw [← hroot v hv]
    exact dvd_mul_of_dvd_left
      (hSdiv v.2 (hij v (hall v hv)) (hprofileNonzero v hv)) _
  have hc := hdiag pairs (fun v => factors v.2) multiplicity hfiber' root S N
    hSsquare.ne_zero hN hrootzero
    (fun v hv => (hfactor v.2 (hij v (hall v hv))).trans (hroot v hv))
    hrootdiv (by
      intro v hv
      rw [hfactor v.2 (hij v (hall v hv))]
      exact hnorm v.2 (hij v (hall v hv)) (hprofileNonzero v hv))
  have hrestrict : (∑ v ∈ allPairs, amp v) = ∑ v ∈ pairs, amp v := by
    dsimp only [pairs]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases ha : amp v = 0
    · rw [if_neg (fun hne => hne ha), ha]
    · rw [if_pos ha]
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hNS : 0 < (Ideal.absNorm S : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hSsquare.ne_zero))
  calc
    _ ≤ ∑ v ∈ allPairs, amp v :=
      second_zero_blocks_le_pair_sum hΓ μv C left right fullI fullJ blocks profiles
        hDiff finiteTest radius M cutoff hcutoff
    _ = ∑ v ∈ pairs, amp v := hrestrict
    _ ≤ ∑ _v ∈ pairs, (C₀ * Amp) / Real.sqrt N := Finset.sum_le_sum hcoef
    _ = (pairs.card : ℝ) * ((C₀ * Amp) / Real.sqrt N) := by simp
    _ ≤ (Cdiag * multiplicity * Real.sqrt N * N ^ ε / (Ideal.absNorm S : ℝ)) *
        ((C₀ * Amp) / Real.sqrt N) :=
      mul_le_mul_of_nonneg_right hc (div_nonneg (mul_nonneg hC₀ hAmp) hsqrt.le)
    _ = Cdiag * multiplicity * (C₀ * Amp) * N ^ ε / (Ideal.absNorm S : ℝ) := by
      field_simp [ne_of_gt hsqrt, ne_of_gt hNS]
      <;> ring
    _ = (Cdiag * C₀) * ((multiplicity : ℝ) * Amp * N ^ ε) /
        (Ideal.absNorm S : ℝ) := by ring
    _ ≤ (Cdiag * (1 + C₀)) * ((multiplicity : ℝ) * Amp * N ^ ε) /
        (Ideal.absNorm S : ℝ) := by
      apply div_le_div_of_nonneg_right _ hNS.le
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : C₀ ≤ 1 + C₀) hCdiag.le)
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hAmp)
        (Real.rpow_nonneg hNpos.le _)
    _ = (Cdiag * (1 + C₀)) * multiplicity * Amp * N ^ ε /
        (Ideal.absNorm S : ℝ) := by ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof
