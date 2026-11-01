import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalFirstSource
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.FixedDyadicCutoff

/-!
# The actual canonical first source has positive inverse energies

The original two exterior-ideal ranges, canonical coefficients, all
prime marks, puncture, label weights and unit sector occur on the left.
The independently reconstructed residual ranges and their full mutual
Moebius divisor pool occur on the right. The cutoff is the one fixed
dyadic logarithmic bump, not a source-dependent choice.

The inverse square-root conductor factors are retained as literal norm
weights in the columns. No source identity or energy inequality is a
field of the data or a hypothesis of the main theorem.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalFirstEnergy

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open IdealMobiusMask FirstSourceDecomposition FirstSourceReindexing FirstSourceEnergy
  FirstSourceColumns FirstSourceFrozen CanonicalFirstSource CommonKernel
open HeckeSkeleton.Moments.MOMInvStep.FullMobius
open scoped Classical BigOperators ComplexConjugate FourierTransform ContDiff nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "NI" => (Ideal (𝓞 K))⁰
local notation "E" => CanonicalIdealRow.exteriorMonoid K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

def nonzeroRange (N : Finset Ext) : Finset NI := N.image Subtype.val

theorem nonzeroRange_squarefree (N : Finset Ext) (hN : ∀ n ∈ N, Squarefree n.val.val) :
    ∀ I ∈ nonzeroRange K S N, Squarefree I.val := by
  intro I hI
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hI
  exact hN n hn

theorem sum_nonzeroRange (N : Finset Ext) (w : NI → ℂ) :
    (∑ I ∈ nonzeroRange K S N, w I) = ∑ n ∈ N, w n.val := by
  exact Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)

def extendExterior (w : Ext → ℂ) (I : NI) : ℂ :=
  if hI : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ Sset then w ⟨I, hI⟩ else 0

@[simp] theorem extendExterior_val (w : Ext → ℂ) (I : Ext) :
    extendExterior K S w I.val = w I := by
  rw [extendExterior, dif_pos I.property]

def cubeSupport (b₁ b₂ : Ext) := primeSupport (b₁.val * b₂.val)
def leftSupport (r₁ b₁ b₂ : Ext) := extractedSupport r₁.val b₁.val b₂.val
def rightSupport (r₂ b₁ b₂ : Ext) := extractedSupport r₂.val b₁.val b₂.val
def commonSupport (r₁ r₂ b₁ b₂ : Ext) :=
  FirstSourceDecomposition.commonSupport r₁.val r₂.val b₁.val b₂.val

def leftDomain (N : Finset Ext) (r₁ r₂ b₁ b₂ : Ext) :=
  columnDomain (nonzeroRange K S N) (cubeSupport K S b₁ b₂)
    (leftSupport K S r₁ b₁ b₂) (commonSupport K S r₁ r₂ b₁ b₂)

def rightDomain (N : Finset Ext) (r₁ r₂ b₁ b₂ : Ext) :=
  columnDomain (nonzeroRange K S N) (cubeSupport K S b₁ b₂)
    (rightSupport K S r₂ b₁ b₂) (commonSupport K S r₁ r₂ b₁ b₂)

theorem leftSupport_subset (r₁ b₁ b₂ : Ext) :
    leftSupport K S r₁ b₁ b₂ ⊆ cubeSupport K S b₁ b₂ := Finset.inter_subset_right

theorem rightSupport_subset (r₂ b₁ b₂ : Ext) :
    rightSupport K S r₂ b₁ b₂ ⊆ cubeSupport K S b₁ b₂ := Finset.inter_subset_right

theorem commonSupport_disjoint (r₁ r₂ b₁ b₂ : Ext) :
    Disjoint (commonSupport K S r₁ r₂ b₁ b₂) (cubeSupport K S b₁ b₂) :=
  Finset.sdiff_disjoint

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

theorem residual_val_eq_original (n₁ n₂ b₁ b₂ : Ext) :
    (residualIdeal K S D n₁ n₂ b₁ b₂ false).val =
      originalResidual K (cubeSupport K S b₁ b₂) n₁.val n₂.val ∧
    (residualIdeal K S D n₁ n₂ b₁ b₂ true).val =
      originalResidual K (cubeSupport K S b₁ b₂) n₂.val n₁.val := by
  constructor
  · apply Subtype.ext
    change (CanonicalGroupedGauss.leftIdeal K S D n₁ n₂ b₁ b₂).val.val = _
    rw [CanonicalGroupedGauss.leftIdeal_val, CanonicalConductor.u₁_eq_residual]
    rfl
  · apply Subtype.ext
    change (CanonicalGroupedGauss.rightIdeal K S D n₁ n₂ b₁ b₂).val.val = _
    rw [CanonicalGroupedGauss.rightIdeal_val, CanonicalConductor.u₂_eq_residual]
    rfl

/-- The square-root conductor factor attached to one residual ideal. -/
def normWeight (I : NI) : ℂ := (Real.sqrt (I.val.absNorm : ℝ) : ℂ)⁻¹

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]

/-- Only the actual test functions and positive physical scales. -/
structure Profile where
  finiteTest : ((v : Sset) → v.val.adicCompletion K) → ℂ
  finiteTest_continuous : Continuous finiteTest
  finiteTest_compact : HasCompactSupport finiteTest
  archTest : SchwartzMap V ℂ
  radius : {r : ℝ // 0 < r}
  leftScale : {r : ℝ // 0 < r}
  rightScale : {r : ℝ // 0 < r}

def Profile.value (P : Profile K S) (u v : NI) : ℂ :=
  sUnitOrbitalProfile K Sset
    (sLocalTensorTestFunction K Sset (traceSchwartzFourier K P.archTest) P.finiteTest)
    ⟨P.radius.val / ((normScale K P.leftScale u).val * (normScale K P.rightScale v).val),
      div_pos P.radius.property (mul_pos (normScale K P.leftScale u).property
        (normScale K P.rightScale v).property)⟩

def Profile.density (P : Profile K S) (ξ : LogPlane) : ℂ :=
  orbitalDensity K Sset Γ P.finiteTest P.finiteTest_continuous P.finiteTest_compact
    dyadicCutoff dyadicCutoff_contDiff dyadicCutoff_hasCompactSupport P.archTest P.radius ξ

variable {σ : Type*}

def movingColumn (C : CanonicalBlock.ColumnData K S σ) (G : HeckeCharacter K)
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (f z : E) (d : OS)
    (ξ : CanonicalSectors.UnitClasses K Sset Γ) (u : NI) : ℂ :=
  normWeight K u * extendExterior K S
    (fixedMarkedInverse K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ) u

def outerScalar (C : CanonicalBlock.ColumnData K S σ)
    (r₁ r₂ b₁ b₂ : Ext) (f₁ f₂ z : E) (d : OS)
    (ξ : CanonicalSectors.UnitClasses K Sset Γ) : ℂ :=
  cubeFourierScalar K S D r₁ r₂ b₁ b₂ d
      (CanonicalSectors.rowElement K Sset Γ D (CanonicalIdealRow.toExterior K S z, ξ)).val *
    (C.labelWeight b₁ (CanonicalIdealRow.toExterior K S f₁) *
      outerCoefficient K S D C.lambda C.background r₁ r₂ b₁ b₂ false f₁) *
    conj (C.labelWeight b₂ (CanonicalIdealRow.toExterior K S f₂) *
      outerCoefficient K S D C.lambda C.background r₁ r₂ b₁ b₂ true f₂)

def originalSource (C : CanonicalBlock.ColumnData K S σ) (N₁ N₂ : Finset Ext)
    (r₁ r₂ b₁ b₂ : Ext) (f₁ f₂ z : E) (d : OS)
    (ξ : CanonicalSectors.UnitClasses K Sset Γ) (P : Profile K S) : ℂ :=
  ∑ n₁ ∈ N₁, ∑ n₂ ∈ N₂,
    if SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂ then
      CanonicalBlock.canonicalColumn K S D C (CanonicalIdealRow.toExterior K S f₁) b₁ n₁ *
      conj (CanonicalBlock.canonicalColumn K S D C (CanonicalIdealRow.toExterior K S f₂) b₂ n₂) *
      pairFourier K S D n₁ n₂ b₁ b₂ d
        (CanonicalSectors.rowElement K Sset Γ D (CanonicalIdealRow.toExterior K S z, ξ)).val *
      normWeight K (residualIdeal K S D n₁ n₂ b₁ b₂ false).val *
      conj (normWeight K (residualIdeal K S D n₁ n₂ b₁ b₂ true).val) *
      P.value K S (residualIdeal K S D n₁ n₂ b₁ b₂ false).val
        (residualIdeal K S D n₁ n₂ b₁ b₂ true).val else 0

def reindexedSource (C : CanonicalBlock.ColumnData K S σ) (G : HeckeCharacter K)
    (N₁ N₂ : Finset Ext) (r₁ r₂ b₁ b₂ : Ext) (f₁ f₂ z : E) (d : OS)
    (ξ : CanonicalSectors.UnitClasses K Sset Γ) (P : Profile K S) : ℂ :=
  ∑ n ∈ nonzeroRange K S N₁, ∑ m ∈ nonzeroRange K S N₂,
    if Supports.Slice (cubeSupport K S b₁ b₂) (leftSupport K S r₁ b₁ b₂)
      (rightSupport K S r₂ b₁ b₂) (commonSupport K S r₁ r₂ b₁ b₂)
      (primeSupport n) (primeSupport m) then
      movingColumn K S D Γ C G r₁ r₂ b₁ b₂ false f₁ z d ξ
        (originalResidual K (cubeSupport K S b₁ b₂) n m) *
      conj (movingColumn K S D Γ C G r₁ r₂ b₁ b₂ true f₂ z d ξ
        (originalResidual K (cubeSupport K S b₁ b₂) m n)) *
      P.value K S (originalResidual K (cubeSupport K S b₁ b₂) n m)
        (originalResidual K (cubeSupport K S b₁ b₂) m n) else 0

theorem originalSource_eq (hallowed : AllowedGeneratorInput K Sset D)
    (C : CanonicalBlock.ColumnData K S σ) (G : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (N₁ N₂ : Finset Ext) (hN₁ : ∀ n ∈ N₁, Squarefree n.val.val)
    (hN₂ : ∀ n ∈ N₂, Squarefree n.val.val)
    (r₁ r₂ b₁ b₂ : Ext) (f₁ f₂ z : E) (d : OS)
    (ξ : CanonicalSectors.UnitClasses K Sset Γ) (P : Profile K S) :
    originalSource K S D Γ C N₁ N₂ r₁ r₂ b₁ b₂ f₁ f₂ z d ξ P =
      outerScalar K S D Γ C r₁ r₂ b₁ b₂ f₁ f₂ z d ξ *
        reindexedSource K S D Γ C G N₁ N₂ r₁ r₂ b₁ b₂ f₁ f₂ z d ξ P := by
  unfold originalSource reindexedSource
  rw [sum_nonzeroRange K S N₁]
  simp_rw [sum_nonzeroRange K S N₂]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n₁ hn₁
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n₂ hn₂
  change (if SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂ then _ else 0) =
    outerScalar K S D Γ C r₁ r₂ b₁ b₂ f₁ f₂ z d ξ *
      (if SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂ then _ else 0)
  by_cases h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂
  · simp only [if_pos h]
    rw [canonical_pair_sector K S D Γ hallowed C G hcal
      n₁ n₂ r₁ r₂ b₁ b₂ (hN₁ n₁ hn₁) (hN₂ n₂ hn₂) h]
    obtain ⟨hu, hv⟩ := residual_val_eq_original K S D n₁ n₂ b₁ b₂
    rw [← hu, ← hv]
    simp only [movingColumn, extendExterior_val, outerScalar, map_mul]
    ring
  · simp only [if_neg h, mul_zero]

def positiveEnergy (P : Profile K S) (T U : Finset (Finset (HeightOneSpectrum (𝓞 K))))
    (X : {r : ℝ // 0 < r}) (coordinate : LogPlane → ℝ) (a : NI → ℂ) : ℝ :=
  ∑ e ∈ divisorPool T primeProduct, ‖(moebius e : ℂ)‖ *
    ∫ ξ : LogPlane, ‖P.density K S Γ ξ‖ *
      ‖∑ W ∈ U with e ∣ primeProduct W,
        a (nonzeroProduct W) * columnPhase (coordinate ξ)
          (Real.log (normScale K X (nonzeroProduct W)).val)‖ ^ 2

/-- The actual full first source is bounded by the two independently
constructed positive residual energies. The only source-range inputs
are squarefreeness and literal dyadic ideal-norm windows. -/
theorem literal_first_source_energy (hallowed : AllowedGeneratorInput K Sset D)
    (C : CanonicalBlock.ColumnData K S σ) (G : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (N₁ N₂ : Finset Ext) (hN₁ : ∀ n ∈ N₁, Squarefree n.val.val)
    (hN₂ : ∀ n ∈ N₂, Squarefree n.val.val)
    (r₁ r₂ b₁ b₂ : Ext) (f₁ f₂ z : E) (d : OS)
    (ξ : CanonicalSectors.UnitClasses K Sset Γ) (P : Profile K S)
    (hleft : ∀ U ∈ leftDomain K S N₁ r₁ r₂ b₁ b₂,
      P.leftScale.val ≤ ((primeProduct U).absNorm : ℝ) ∧
        ((primeProduct U).absNorm : ℝ) ≤ 2 * P.leftScale.val)
    (hright : ∀ W ∈ rightDomain K S N₂ r₁ r₂ b₁ b₂,
      P.rightScale.val ≤ ((primeProduct W).absNorm : ℝ) ∧
        ((primeProduct W).absNorm : ℝ) ≤ 2 * P.rightScale.val) :
    ‖originalSource K S D Γ C N₁ N₂ r₁ r₂ b₁ b₂ f₁ f₂ z d ξ P‖ ≤
      ‖outerScalar K S D Γ C r₁ r₂ b₁ b₂ f₁ f₂ z d ξ‖ *
      (Real.sqrt (positiveEnergy K S Γ P (leftDomain K S N₁ r₁ r₂ b₁ b₂)
        (leftDomain K S N₁ r₁ r₂ b₁ b₂) P.leftScale (fun η : LogPlane => η.fst)
        (movingColumn K S D Γ C G r₁ r₂ b₁ b₂ false f₁ z d ξ)) *
       Real.sqrt (positiveEnergy K S Γ P (leftDomain K S N₁ r₁ r₂ b₁ b₂)
        (rightDomain K S N₂ r₁ r₂ b₁ b₂) P.rightScale (fun η : LogPlane => η.snd)
        (fun u => conj (movingColumn K S D Γ C G r₁ r₂ b₁ b₂ true f₂ z d ξ u)))) := by
  have hcut : ∀ U ∈ leftDomain K S N₁ r₁ r₂ b₁ b₂,
      ∀ W ∈ rightDomain K S N₂ r₁ r₂ b₁ b₂,
      dyadicCutoff (logPoint (Real.log (normScale K P.leftScale (nonzeroProduct U)).val)
        (Real.log (normScale K P.rightScale (nonzeroProduct W)).val)) = 1 := by
    intro U hU W hW
    exact dyadicCutoff_one_of_height_intervals _ _ _ _
      P.leftScale.property P.rightScale.property
      (hleft U hU).1 (hleft U hU).2 (hright W hW).1 (hright W hW).2
  have he := actual_first_orbital_source_energy K Sset Γ
    P.finiteTest P.finiteTest_continuous P.finiteTest_compact
    dyadicCutoff dyadicCutoff_contDiff dyadicCutoff_hasCompactSupport
    (nonzeroRange K S N₁) (nonzeroRange K S N₂)
    (nonzeroRange_squarefree K S N₁ hN₁) (nonzeroRange_squarefree K S N₂ hN₂)
    (cubeSupport K S b₁ b₂) (leftSupport K S r₁ b₁ b₂) (rightSupport K S r₂ b₁ b₂)
    (commonSupport K S r₁ r₂ b₁ b₂) (leftSupport_subset K S r₁ b₁ b₂)
    (rightSupport_subset K S r₂ b₁ b₂) (commonSupport_disjoint K S r₁ r₂ b₁ b₂)
    P.archTest P.radius P.leftScale P.rightScale
    (movingColumn K S D Γ C G r₁ r₂ b₁ b₂ false f₁ z d ξ)
    (fun u => conj (movingColumn K S D Γ C G r₁ r₂ b₁ b₂ true f₂ z d ξ u)) hcut
  rw [originalSource_eq K S D Γ hallowed C G hcal N₁ N₂ hN₁ hN₂,
    norm_mul]
  exact mul_le_mul_of_nonneg_left he (norm_nonneg _)

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalFirstEnergy

end
