import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalDirectParentWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectNormalizedChildren

set_option linter.unusedSectionVars false

/-!
# The literal direct-source exceptional terminal

The direct entrance uses the same original theta-class atom data and
the same fixed finite Fourier controls. Its exact outer scalar has the
two original orbital fibres and the Cauchy half. There is no prime pool,
tag, density or moving-prime length. The actual direct finite image and
its source fibre are proved internally by the earlier direct lemmas.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.Moments.Support
open CommonSupportMass UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ} {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := U) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}
variable {theta : Finset (HeckeCharacter K)}
local notation "Orbit" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

namespace ActualDirectFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal) {cap : ℕ} (hcap : L.slotCount ≤ cap)
variable (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
local notation "Labels" => R.arithmeticLabels L hcap exceptional N
local notation "Index" => R.originalIndex L hcap exceptional N

/-- The raw direct data are bound to each literal theta-class leaf.
The first fibre is the original parent's stored orbital fibre, and the
second one is retained in the exact outer identity. -/
structure ExceptionalOriginalData
    (profiles : theta × theta → ExceptionalOriginalProfilePair K)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent)
    (degree J₁ J₂ fiberCap : ℕ) (P loss : ℝ)
    (lower : R.liveLeaves L exceptional N → ℝ) where
  characters : ∀ i : R.liveLeaves L exceptional N, PairedFiniteCharacters theta Orbit
  predicate : ∀ i, (R.parentLeaf L exceptional N i.val).exceptional = (characters i).exceptional
  primeIndex : (i : R.liveLeaves L exceptional N) → theta × theta → Type
  primeFintype : ∀ i χ, Fintype (primeIndex i χ)
  primeDecidableEq : ∀ i χ, DecidableEq (primeIndex i χ)
  rows : ∀ i χ,
    letI := primeFintype i χ
    letI := primeDecidableEq i χ
    ActualSecondCorrelationRows A σ Orbit (primeIndex i χ)
  atoms : ∀ i χ,
    letI := primeFintype i χ
    letI := primeDecidableEq i χ
    ExceptionalLeafRawCase (C := C) (rows i χ) (profiles χ) ε maskExponent hε hmask
      cap degree J₁ J₂
      (exceptionalCatalogueOrder (U := U) (E := E) (σ := σ) (η := η) (hS := hS)
        profiles ε maskExponent hε hmask)
      fiberCap s.fiber Z P a.m a.q loss (lower i) 1 0
      ((R.parentLeaf L exceptional N i.val).thetaClassLeaf (characters i) χ)
      (Index i) (characters i)

variable {R L hcap exceptional N}

theorem exceptional_parent_leaf_le
    (profiles : theta × theta → ExceptionalOriginalProfilePair K)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent)
    (degree J₁ J₂ fiberCap : ℕ) (P loss : ℝ)
    (lower : R.liveLeaves L exceptional N → ℝ)
    (raw : R.ExceptionalOriginalData L hcap exceptional N
      profiles ε maskExponent hε hmask degree J₁ J₂ fiberCap P loss lower)
    (hZ : 1 < Z) (hP : 1 ≤ P) (i : R.liveLeaves L exceptional N) :
    (R.parentLeaf L exceptional N i.val).exceptionalCost / Z ^ (a.m + a.q) ≤
      ((Fintype.card (theta × theta) : ℝ) *
        exceptionalBudgetAtomConstant (K := K) (U := U) (E := E) cap fiberCap J₁ J₂
          (exceptionalCatalogueConstant (U := U) (E := E) (σ := σ) (η := η) (hS := hS)
            profiles ε maskExponent hε hmask)) *
      P ^ exceptionalBudgetProfileDegree cap degree * Z ^ loss *
        (Labels).carrier.exceptionalDyadWeight Z (lower i) (Index i) := by
  sorry

end ActualDirectFirstSource.SecondStages

variable {Θ : Type*} [Fintype Θ]

/-- The literal direct-source exceptional budget, normalized by the
original parent. The actual source supplies its own finite index,
admissibility and fibre, with no aggregate premise. -/
theorem actual_direct_exceptionalBudget_from_original_atoms
    (profiles : theta × theta → ExceptionalOriginalProfilePair K)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent)
    (cap dimension width degree J₁ J₂ fiberCap : ℕ)
    (normBox δ₁ δ₂ δ₃ loss : ℝ)
    (hbox : 0 ≤ normBox) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) :
    ∃ Cex : ℝ, 0 < Cex ∧ ∀ Z : ℝ, 1 < Z → ∀ P : ℝ, 1 ≤ P →
    ∀ {omega psi : HeckeCharacter K} (centered : Bool) (d : MomentData K omega psi) (a : RealParameters)
      (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X)
      (s : ActualDirectFirstSource (E := U) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
      (R : s.SecondStages (E := E) (hDiff := hDiff))
      (L : SourceCartesianAtlas s.columns s.ideal) (hcap : L.slotCount ≤ cap)
      (exceptional : R.prepared.CoverHybridPredicates L) (N : s.Normalization),
    ∀ rows : R.prepared.OriginalFibreRows Θ dimension width normBox Z,
    ∀ oldMask : Ideal (𝓞 K), Squarefree oldMask → oldMask ≠ 0 →
      (∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val) →
    ∀ maskIdeal : Ideal (𝓞 K), maskIdeal ≠ 0 →
      OriginalMaskPrimeData s.mask maskIdeal →
      (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ normBox →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ normBox) →
    ∀ (lower : R.prepared.liveLeaves L exceptional N → ℝ) (mesh : ℝ),
      (∀ i, (Ideal.absNorm (R.prepared.innerDivisor L i.val) : ℝ) ≤ Z ^ (lower i + mesh)) →
    ∀ raw : R.prepared.ExceptionalOriginalData L hcap exceptional N
      profiles ε maskExponent hε hmask degree J₁ J₂ fiberCap P loss lower,
      R.prepared.exceptionalBudget L exceptional N / Z ^ (a.m + a.q) ≤
        Cex * P ^ exceptionalBudgetProfileDegree cap degree *
          Z ^ (loss + δ₁ + δ₂ + δ₃ + mesh) / (Ideal.absNorm oldMask : ℝ) := by
  sorry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.exceptional_parent_leaf_le
#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_exceptionalBudget_from_original_atoms
