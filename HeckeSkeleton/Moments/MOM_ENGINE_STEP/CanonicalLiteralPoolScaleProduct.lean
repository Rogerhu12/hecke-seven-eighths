import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolScalars
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralScaleProduct

/-!
# Original occurrence scale bounds for the actual pool tables

Each bound starts at the original profile support and the original
comparison-scale product. The existing atlas gives the same frozen
ideal. No transformed scale window or completed child estimate is
assumed. Both original rectangles retain the identical product.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum
open MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)

local notation "original" => (Q.arithmeticAtoms ξ).constantAtoms W a Z t
local notation "raw" => (original).raw Y₁ Y₂
local notation "seed" => Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
local notation "c" => ((original).values Y₁ Y₂).coefficient centered

variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock
  (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).columnExterior
  (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).columnExterior DE)
variable (C : A.GeneralArithmeticContext σ η htrace)
variable (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
variable (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
variable (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
variable (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
variable (δ₁ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁half : δ₁ ≤ 1 / 2)
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad Z ell eps}
variable {M : Finset (HeightOneSpectrum A.R)} {cutoff : ℝ} {hcutoff : 1 ≤ cutoff}
variable (p : FirstBlockPoolData
  (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns φ
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half) pool M cutoff hcutoff)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

/-- The original prime window, actual retained count and full frozen
scale bound for this original left main label. -/
theorem literalLeftMainAtoms_originalScale
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.leftSourceCovers (raw).originalAtlas S χ).main.labels)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {amplitude : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window seminorms (data ξ) amplitude)
    (B : ℝ) (hB : 1 ≤ B) (ht : t ∈ heightDomain)
    (hwindow : ∀ x ∈ window, x ≤ B)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    (hcomparison : Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂)) :
    (literalLeftMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label).PrimeNormWindow B ∧
      ((p.leftSourceCovers (raw).originalAtlas S χ).main.branch label).slotCount ≤ cap ∧
      ∀ r, (literalLeftMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label).scaleProduct r *
        (Ideal.absNorm DE.1 : ℝ) ≤
          B ^ cap * Z ^ (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) := by
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.1 label
  let T := (p.leftSourceCovers (raw).originalAtlas S χ).main.branch label
  have e := literalLeftMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  let input := (seed).secondInput (σ := σ) branch P R (unitExterior A) firstFixed
    (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  have hp := Q.literalOriginalAtoms_primeNormWindow ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ profiles B ht hwindow
  have hi : input.PrimeNormWindow B := hp.extract branch
  have ha := hi.onAtlas_dictionary T _ e
  refine ⟨ha.deleteMask _, ?_, ?_⟩
  · change T.slotCount ≤ cap
    rw [congrArg Sigma.fst e]
    exact (by simpa only [Fintype.card_fin] using
      (Finset.card_le_univ branch.keep)).trans hcap
  · intro r
    have hfrozen : frozenSourceIdeal branch.plainDivisor₁ branch.plainDivisor₂
        branch.keep branch.witness.2 = DE.1 := by
      exact branch.frozenSourceIdeal_eq.trans
        ((raw).originalAtlas.branch_product (primeSupport DE.1) DE.1 label)
    have h := (seed).extract_scaleProduct_mul_frozenNorm_le hp hB cap hcap branch r
    rw [hfrozen, Q.literalOriginalAtoms_scaleProduct ξ W a Z t Y₁ Y₂ centered
      hZ hY₁ hY₂ r hcomparison] at h
    simpa only [literalLeftMainAtoms,
      CanonicalLiteralRectangles.Atoms.deleteMask_scaleProduct,
      CanonicalLiteralRectangles.Atoms.onAtlas_scaleProduct,
      CanonicalLiteralRectangles.Atoms.secondInput_scaleProduct] using h

/-- The original prime window, actual retained count and full frozen
scale bound for this original right main label. -/
theorem literalRightMainAtoms_originalScale
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.rightSourceCovers (raw).originalAtlas S χ).main.labels)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {amplitude : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window seminorms (data ξ) amplitude)
    (B : ℝ) (hB : 1 ≤ B) (ht : t ∈ heightDomain)
    (hwindow : ∀ x ∈ window, x ≤ B)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    (hcomparison : Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂)) :
    (literalRightMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label).PrimeNormWindow B ∧
      ((p.rightSourceCovers (raw).originalAtlas S χ).main.branch label).slotCount ≤ cap ∧
      ∀ r, (literalRightMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label).scaleProduct r *
        (Ideal.absNorm DE.2 : ℝ) ≤
          B ^ cap * Z ^ (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) := by
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.2 label
  let T := (p.rightSourceCovers (raw).originalAtlas S χ).main.branch label
  have e := literalRightMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  let input := (seed).secondInput (σ := σ) branch P R (unitExterior A) firstFixed
    (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  have hp := Q.literalOriginalAtoms_primeNormWindow ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ profiles B ht hwindow
  have hi : input.PrimeNormWindow B := hp.extract branch
  have ha := hi.onAtlas_dictionary T _ e
  refine ⟨ha.deleteMask _, ?_, ?_⟩
  · change T.slotCount ≤ cap
    rw [congrArg Sigma.fst e]
    exact (by simpa only [Fintype.card_fin] using
      (Finset.card_le_univ branch.keep)).trans hcap
  · intro r
    have hfrozen : frozenSourceIdeal branch.plainDivisor₁ branch.plainDivisor₂
        branch.keep branch.witness.2 = DE.2 := by
      exact branch.frozenSourceIdeal_eq.trans
        ((raw).originalAtlas.branch_product (primeSupport DE.1) DE.2 label)
    have h := (seed).extract_scaleProduct_mul_frozenNorm_le hp hB cap hcap branch r
    rw [hfrozen, Q.literalOriginalAtoms_scaleProduct ξ W a Z t Y₁ Y₂ centered
      hZ hY₁ hY₂ r hcomparison] at h
    simpa only [literalRightMainAtoms,
      CanonicalLiteralRectangles.Atoms.deleteMask_scaleProduct,
      CanonicalLiteralRectangles.Atoms.onAtlas_scaleProduct,
      CanonicalLiteralRectangles.Atoms.secondInput_scaleProduct] using h

/-- The original prime window, actual retained count and full frozen
scale bound for this original left pool label. -/
theorem literalLeftPoolAtoms_originalScale
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).labels)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {amplitude : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window seminorms (data ξ) amplitude)
    (B : ℝ) (hB : 1 ≤ B) (ht : t ∈ heightDomain)
    (hwindow : ∀ x ∈ window, x ≤ B)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    (hcomparison : Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂)) :
    (literalLeftPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ q n label).PrimeNormWindow B ∧
      (((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).branch label).slotCount ≤ cap ∧
      ∀ r, (literalLeftPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ q n label).scaleProduct r *
        (Ideal.absNorm (DE.1 * q.val.val.asIdeal ^ n) : ℝ) ≤
          B ^ cap * Z ^ (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) := by
  let branch := (p.divisorPools.leftData S).combinedBranchForLabel (raw).originalAtlas
    (primeSupport DE.1) DE.1 ((p.divisorPools.left_columns S).trans p.left_columns)
    q.val n label
  let T := ((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).branch label
  have e := literalLeftPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  let input := (seed).secondInput (σ := σ) branch P R (powerIdeal q.val n) firstFixed
    (powerIdeal q.val (2 * n)) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (generator C q.val ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (generator_power_generates C q.val (2 * n))
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  have hp := Q.literalOriginalAtoms_primeNormWindow ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ profiles B ht hwindow
  have hi : input.PrimeNormWindow B := hp.extract branch
  have ha := hi.onAtlas_dictionary T _ e
  refine ⟨ha.deleteMask _, ?_, ?_⟩
  · change T.slotCount ≤ cap
    rw [congrArg Sigma.fst e]
    exact (by simpa only [Fintype.card_fin] using
      (Finset.card_le_univ branch.keep)).trans hcap
  · intro r
    have hfrozen : frozenSourceIdeal branch.plainDivisor₁ branch.plainDivisor₂
        branch.keep branch.witness.2 = (DE.1 * q.val.val.asIdeal ^ n) := by
      have hw := ((p.divisorPools.leftData S).combinedBranchForLabel_spec
        (raw).originalAtlas (primeSupport DE.1) DE.1
        ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label).2
      have he := (p.divisorPools.leftData S).combined_extract_of_mem
        (primeSupport DE.1) DE.1
        ((p.divisorPools.left_columns S).trans p.left_columns)
        (fun i => by rw [p.divisorPools.left_ideal S, p.left_ideal];
          exact b.left_residual i) q.val n
        ((raw).originalAtlas.reindex.index branch.witness) hw
      rw [(raw).originalAtlas.reindex.ideal_product branch.witness
        (branch.original_subset branch.witness_mem),
        branch.extract_ideal branch.witness branch.witness_mem] at he
      exact branch.frozenSourceIdeal_eq.trans he
    have h := (seed).extract_scaleProduct_mul_frozenNorm_le hp hB cap hcap branch r
    rw [hfrozen, Q.literalOriginalAtoms_scaleProduct ξ W a Z t Y₁ Y₂ centered
      hZ hY₁ hY₂ r hcomparison] at h
    simpa only [literalLeftPoolAtoms,
      CanonicalLiteralRectangles.Atoms.deleteMask_scaleProduct,
      CanonicalLiteralRectangles.Atoms.onAtlas_scaleProduct,
      CanonicalLiteralRectangles.Atoms.secondInput_scaleProduct] using h

/-- The original prime window, actual retained count and full frozen
scale bound for this original right pool label. -/
theorem literalRightPoolAtoms_originalScale
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).labels)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {amplitude : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window seminorms (data ξ) amplitude)
    (B : ℝ) (hB : 1 ≤ B) (ht : t ∈ heightDomain)
    (hwindow : ∀ x ∈ window, x ≤ B)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    (hcomparison : Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂)) :
    (literalRightPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ q n label).PrimeNormWindow B ∧
      (((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).branch label).slotCount ≤ cap ∧
      ∀ r, (literalRightPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ q n label).scaleProduct r *
        (Ideal.absNorm (DE.2 * q.val.val.asIdeal ^ n) : ℝ) ≤
          B ^ cap * Z ^ (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) := by
  let branch := (p.divisorPools.rightData S).combinedBranchForLabel (raw).originalAtlas
    (primeSupport DE.1) DE.2 ((p.divisorPools.right_columns S).trans p.right_columns)
    q.val n label
  let T := ((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).branch label
  have e := literalRightPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  let input := (seed).secondInput (σ := σ) branch P R (powerIdeal q.val n) firstFixed
    (powerIdeal q.val (2 * n)) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (generator C q.val ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (generator_power_generates C q.val (2 * n))
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  have hp := Q.literalOriginalAtoms_primeNormWindow ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ profiles B ht hwindow
  have hi : input.PrimeNormWindow B := hp.extract branch
  have ha := hi.onAtlas_dictionary T _ e
  refine ⟨ha.deleteMask _, ?_, ?_⟩
  · change T.slotCount ≤ cap
    rw [congrArg Sigma.fst e]
    exact (by simpa only [Fintype.card_fin] using
      (Finset.card_le_univ branch.keep)).trans hcap
  · intro r
    have hfrozen : frozenSourceIdeal branch.plainDivisor₁ branch.plainDivisor₂
        branch.keep branch.witness.2 = (DE.2 * q.val.val.asIdeal ^ n) := by
      have hw := ((p.divisorPools.rightData S).combinedBranchForLabel_spec
        (raw).originalAtlas (primeSupport DE.1) DE.2
        ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label).2
      have he := (p.divisorPools.rightData S).combined_extract_of_mem
        (primeSupport DE.1) DE.2
        ((p.divisorPools.right_columns S).trans p.right_columns)
        (fun i => by rw [p.divisorPools.right_ideal S, p.right_ideal];
          exact b.right_residual i) q.val n
        ((raw).originalAtlas.reindex.index branch.witness) hw
      rw [(raw).originalAtlas.reindex.ideal_product branch.witness
        (branch.original_subset branch.witness_mem),
        branch.extract_ideal branch.witness branch.witness_mem] at he
      exact branch.frozenSourceIdeal_eq.trans he
    have h := (seed).extract_scaleProduct_mul_frozenNorm_le hp hB cap hcap branch r
    rw [hfrozen, Q.literalOriginalAtoms_scaleProduct ξ W a Z t Y₁ Y₂ centered
      hZ hY₁ hY₂ r hcomparison] at h
    simpa only [literalRightPoolAtoms,
      CanonicalLiteralRectangles.Atoms.deleteMask_scaleProduct,
      CanonicalLiteralRectangles.Atoms.onAtlas_scaleProduct,
      CanonicalLiteralRectangles.Atoms.secondInput_scaleProduct] using h

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftMainAtoms_originalScale
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightMainAtoms_originalScale
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftPoolAtoms_originalScale
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightPoolAtoms_originalScale
