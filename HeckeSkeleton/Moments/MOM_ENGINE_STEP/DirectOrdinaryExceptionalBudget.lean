import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryActualExceptionalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalDirectParentWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectNormalizedChildren

/-!
# The literal direct-source ordinary exceptional terminal

The ordinary range uses the two complete original columns and their
zero-order Fourier measure mass. Its exact outer scalar retains the
two original orbital fibres and the Cauchy half. The actual direct
finite image, arithmetic admissibility and source fibre are supplied by
the existing direct-source theorems. The budget follows from individual
ordinary atom windows, including the literal zero-row case.
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

/-- Ordinary atom data are bound to each literal theta-class leaf.
The first fibre is the original parent's stored orbital fibre, and the
second one is retained in the exact outer identity. -/
structure OrdinaryExceptionalOriginalData
    (R : s.SecondStages (E := E) (hDiff := hDiff))
    (L : SourceCartesianAtlas s.columns s.ideal) (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (profiles : theta × theta → ExceptionalOriginalProfilePair K)
    (degree fiberCap : ℕ) (P loss : ℝ)
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
    OrdinaryExceptionalLeafRawCase (C := C) (rows i χ) (profiles χ)
      cap degree fiberCap s.fiber Z P a.m a.q loss (lower i) 1 0
      ((R.parentLeaf L exceptional N i.val).thetaClassLeaf (characters i) χ)
      (R.originalIndex L hcap exceptional N i) (characters i)

variable {R L hcap exceptional N}

theorem ordinary_exceptional_parent_leaf_le
    (profiles : theta × theta → ExceptionalOriginalProfilePair K)
    (degree fiberCap : ℕ) (P loss : ℝ)
    (lower : R.liveLeaves L exceptional N → ℝ)
    (raw : R.OrdinaryExceptionalOriginalData L hcap exceptional N
      profiles degree fiberCap P loss lower)
    (hZ : 1 < Z) (hP : 1 ≤ P) (i : R.liveLeaves L exceptional N) :
    (R.parentLeaf L exceptional N i.val).exceptionalCost / Z ^ (a.m + a.q) ≤
      ((Fintype.card (theta × theta) : ℝ) *
        exceptionalBudgetAtomConstant (K := K) (U := U) (E := E) cap fiberCap 0 0
          (ordinaryExceptionalCatalogueConstant profiles)) *
      P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss *
        Labels.carrier.exceptionalDyadWeight Z (lower i) (Index i) := by
  let volume := ordinaryExceptionalCatalogueConstant profiles
  let atom := exceptionalBudgetAtomConstant (K := K) (U := U) (E := E) cap fiberCap 0 0 volume
  have hv : 0 ≤ volume := (ordinaryExceptionalCatalogueConstant_pos profiles).le
  have hleaf (χ : theta × theta) :
      ((R.parentLeaf L exceptional N i.val).thetaClassLeaf (raw.characters i) χ).exceptionalCost /
        Z ^ (a.m + a.q) ≤
      atom * P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss *
        Labels.carrier.exceptionalDyadWeight Z (lower i) (Index i) := by
    letI := raw.primeFintype i χ
    letI := raw.primeDecidableEq i χ
    simpa only [mul_one, add_zero] using
      (raw.atoms i χ).cost_le hZ hP zero_le_one volume hv
        (ordinaryExceptionalCatalogueConstant_le profiles χ)
  rw [(R.parentLeaf L exceptional N i.val).exceptionalCost_eq_theta_sum
    (raw.characters i) (raw.predicate i), Finset.sum_div]
  calc
    _ ≤ ∑ _χ : theta × theta,
        atom * P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss *
          Labels.carrier.exceptionalDyadWeight Z (lower i) (Index i) :=
      Finset.sum_le_sum fun χ _ => hleaf χ
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp only [atom, volume]; ring

end ActualDirectFirstSource.SecondStages

variable {Θ : Type*} [Fintype Θ]

/-- The literal ordinary direct-source exceptional budget, normalized by the
original parent. The actual source supplies its own finite index,
admissibility and fibre, with no aggregate premise. -/
theorem actual_direct_ordinary_exceptionalBudget_from_original_atoms
    (profiles : theta × theta → ExceptionalOriginalProfilePair K)
    (cap dimension width degree fiberCap : ℕ)
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
    ∀ raw : R.prepared.OrdinaryExceptionalOriginalData L hcap exceptional N
      profiles degree fiberCap P loss lower,
      R.prepared.exceptionalBudget L exceptional N / Z ^ (a.m + a.q) ≤
        Cex * P ^ ordinaryExceptionalBudgetProfileDegree cap degree *
          Z ^ (loss + δ₁ + δ₂ + δ₃ + mesh) / (Ideal.absNorm oldMask : ℝ) := by
  obtain ⟨Ca, hCa, hmass⟩ := actual_direct_exceptional_index_mass
    (A := A) (C := C) (W := U) (E := E) (Θ := Θ)
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (finiteTest := finiteTest)
    cap dimension width normBox δ₁ δ₂ δ₃ hbox hδ₁ hδ₂ hδ₃
  let volume := ordinaryExceptionalCatalogueConstant profiles
  let atom := exceptionalBudgetAtomConstant (K := K) (U := U) (E := E) cap fiberCap 0 0 volume
  let total := (Fintype.card (theta × theta) : ℝ) * atom
  have hv : 0 ≤ volume := (ordinaryExceptionalCatalogueConstant_pos profiles).le
  have hatom : 0 ≤ atom := exceptionalBudgetAtomConstant_nonneg _ _ _ _ volume hv
  have ht : 0 ≤ total := mul_nonneg (Nat.cast_nonneg _) hatom
  refine ⟨(total + 1) * Ca, mul_pos (by linarith) hCa, ?_⟩
  intro Z hZ P hP omega psi centered d a t Y₁ Y₂ X hX s R L hcap
    exceptional N rows oldMask hs hs0 hmaskOld maskIdeal hmask0 mask hmaskN hN lower mesh hwindow raw
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hm := hmass Z hZ.le centered d a t Y₁ Y₂ X hX s R L hcap exceptional N
    rows oldMask hs hs0 hmaskOld maskIdeal hmask0 mask hmaskN hN lower mesh hwindow
  let dyad := fun i : R.prepared.liveLeaves L exceptional N =>
    (R.prepared.arithmeticLabels L hcap exceptional N).carrier.exceptionalDyadWeight
      Z (lower i) (R.prepared.originalIndex L hcap exceptional N i)
  have hleaf (i : R.prepared.liveLeaves L exceptional N) :
      (R.prepared.parentLeaf L exceptional N i.val).exceptionalCost / Z ^ (a.m + a.q) ≤
        total * P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss * dyad i :=
    ActualDirectFirstSource.SecondStages.ordinary_exceptional_parent_leaf_le profiles
      degree fiberCap P loss lower raw hZ hP i
  have hscalar : 0 ≤ total * P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss :=
    mul_nonneg (mul_nonneg ht (pow_nonneg (zero_le_one.trans hP) _)) (Real.rpow_nonneg hz.le _)
  have hnorm : 0 < (Ideal.absNorm oldMask : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0))
  calc
    _ = ∑ i : R.prepared.liveLeaves L exceptional N,
        (R.prepared.parentLeaf L exceptional N i.val).exceptionalCost / Z ^ (a.m + a.q) := by
      simp only [ActualDirectFirstSource.SecondStages.exceptionalBudget,
        ActualDirectFirstSource.SecondStages.liveLeaf, Finset.sum_div]
    _ ≤ ∑ i : R.prepared.liveLeaves L exceptional N,
        total * P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss * dyad i :=
      Finset.sum_le_sum fun i _ => hleaf i
    _ = (total * P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss) * ∑ i, dyad i :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (total * P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss) *
        (Ca * Z ^ (δ₁ + δ₂ + δ₃ + mesh) / (Ideal.absNorm oldMask : ℝ)) :=
      mul_le_mul_of_nonneg_left hm hscalar
    _ = (total * Ca) * P ^ ordinaryExceptionalBudgetProfileDegree cap degree *
        Z ^ (loss + δ₁ + δ₂ + δ₃ + mesh) / (Ideal.absNorm oldMask : ℝ) := by
      rw [show loss + δ₁ + δ₂ + δ₃ + mesh = loss + (δ₁ + δ₂ + δ₃ + mesh) by ring,
        Real.rpow_add hz loss (δ₁ + δ₂ + δ₃ + mesh)]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hCa.le)
          (pow_nonneg (zero_le_one.trans hP) _))
        (Real.rpow_nonneg hz.le _)) hnorm.le

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.ordinary_exceptional_parent_leaf_le
#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_ordinary_exceptionalBudget_from_original_atoms
