import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCoveredFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalCoordinateSubpower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalSourceSlotCaps
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSecondStages

/-!
# The pool-free original entrance has the same uniform finite fibres

The literal direct source cover is constructed from the original
Cartesian atlas.  Its two earlier support-key counts and all inherited
slot caps are proved here from that atlas.  The actual covered source
fibre then uses the same original-prime mask bounds and four divisor
counts as the amplified construction, with no pool parameter or density.

The final two adapters instantiate this theorem on the actual left and
right `FirstBlockDirectData.SecondStages`, retaining the first original
divisor and its original finite phase.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.Support
open HeckePort.Moments.MobiusRegroup HeckePort.IdealMobiusDivisorSum WholeAllocation

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
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance directCoveredFibreMassCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

namespace DirectGaussData

variable {ι : Type*} {originalColumns : Finset ι} {originalIdeal : ι → A.Exterior}
variable (d : DirectGaussData C ι)
variable (T : SourceCartesianAtlas originalColumns originalIdeal)
variable (S : Finset (Ideal (𝓞 K))) (D₀ : Ideal (𝓞 K))
variable (hcolumns : d.columns =
  originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D₀))
variable (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val S)
variable (c : ι → ℂ)
variable (s : ActualGaussStage (E := E) hΓ μv hDiff (d.directSource c) finiteTest)

local notation "CV" => d.sourceCartesianCover T S D₀ hcolumns hideal c

/-- Uniform small-power bound on the genuine direct-source index
fibre. The original first cover is constructed, never supplied with an
aggregate size estimate. -/
theorem covered_index_fibre_subpower
    (cap dimension width : ℕ) (hcap : T.slotCount ≤ cap)
    (B ε Z : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hZ : 1 ≤ Z)
    (hleft : ∀ v : s.CoveredClassKey CV CV, v.leftSlots ≤ cap)
    (hright : ∀ v : s.CoveredClassKey CV CV, v.rightSupportSlots ≤ cap)
    {J ρ Θ : Type*} [Fintype Θ]
    (index : s.CoveredLeafKey CV CV → J)
    (allocation : J → OriginalAllocationFingerprint K cap)
    (hindex : ∀ b, allocation (index b) =
      ActualGaussStage.coveredAllocationFingerprint hleft hright b)
    (leaves : Finset (s.CoveredLeafKey CV CV)) (j : J)
    (DE : commonSupportPool (d.directSource c).columns (d.directSource c).columns
      (fun i => ((d.directSource c).ideal i).val) (fun j => ((d.directSource c).ideal j).val))
    (hcommon : ∀ b ∈ leaves, index b = j → b.1.1 = DE)
    (hrow : ∀ b ∈ leaves, b.1.rowLabel ∈ s.actualRowLabels b.1.1 b.1.2.1)
    (support : Finset ρ)
    (code : s.mask.powerset → Q → OriginalFiniteFibre.RowCode support Θ dimension width)
    (encode : ∀ D : s.mask.powerset,
      OriginalFiniteFibre.RowCode support Θ dimension width →
        Fin ((s.charts DE D).rowLabelCount + 1))
    (hcode : ∀ D : s.mask.powerset, ∀ h ∈ (s.sources DE).rows,
      (s.charts DE D).rowLabel h = encode D (code D h))
    (hDE : DE.val.1 ≠ 0 ∧ DE.val.2 ≠ 0) (hD₀ : D₀ ≠ 0)
    (Rmask Rrow : Ideal (𝓞 K)) (hRmask : Rmask ≠ 0) (hRrow : Rrow ≠ 0)
    (WM : OriginalMaskPrimeData s.mask Rmask) (WR : OriginalMaskPrimeData support Rrow)
    (hNmask : (Ideal.absNorm Rmask : ℝ) ≤ Z ^ B)
    (hNrow : (Ideal.absNorm Rrow : ℝ) ≤ Z ^ B)
    (hND₀ : (Ideal.absNorm D₀ : ℝ) ≤ Z ^ B)
    (hND : (Ideal.absNorm DE.val.1 : ℝ) ≤ Z ^ B)
    (hNE : (Ideal.absNorm DE.val.2 : ℝ) ≤ Z ^ B) :
    ((leaves.filter (fun b => index b = j)).card : ℝ) ≤
      OriginalFiniteFibre.coordinateConstant (K := K) cap (Fintype.card Θ)
        dimension width B ε hB hε * Z ^ ε := by
  have hslots : ∀ a, ((CV).branch a).slotCount ≤ cap := fun a =>
    (d.sourceCartesianCover_slotCount_le T S D₀ hcolumns hideal c a).trans hcap
  have hkeys : (CV).labels.card ≤ idealDivisorCount D₀ ^ (cap + 2) :=
    T.labels_card_le_cap cap hcap S D₀ hD₀
  have hraw := ActualGaussStage.covered_index_fibre_card_le_coordinates hleft hright
    index allocation hindex leaves j DE hcommon hrow support dimension width code encode hcode
      hDE hslots hslots
  have hn : (leaves.filter (fun b => index b = j)).card ≤
      OriginalFiniteFibre.coordinateCount s.mask support D₀ D₀ DE.val.1 DE.val.2
        cap (Fintype.card Θ) dimension width := by
    refine hraw.trans ?_
    unfold OriginalFiniteFibre.coordinateCount
    change _ ≤ 2 ^ s.mask.card * idealDivisorCount D₀ ^ (cap + 2) *
      idealDivisorCount D₀ ^ (cap + 2) *
        (2 ^ support.card * Fintype.card Θ * (width + 1) ^ dimension) *
          idealDivisorCount DE.val.1 ^ (cap + 2) * idealDivisorCount DE.val.2 ^ (cap + 2)
    gcongr <;> assumption
  have hnreal : ((leaves.filter (fun b => index b = j)).card : ℝ) ≤
      (OriginalFiniteFibre.coordinateCount s.mask support D₀ D₀ DE.val.1 DE.val.2
        cap (Fintype.card Θ) dimension width : ℝ) := by exact_mod_cast hn
  exact hnreal.trans (OriginalFiniteFibre.coordinateCount_le
    cap (Fintype.card Θ) dimension width B ε hB hε Z hZ
    s.mask support Rmask Rrow D₀ D₀ DE.val.1 DE.val.2 hRmask hRrow
    hNmask hNrow hND₀ hND₀ hND hNE WM WR)

end DirectGaussData

namespace FirstBlockDirectData.SecondStages

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart M X hX}
variable (s : p.SecondStages (E := E) (hDiff := hDiff))

/-- The theorem above, instantiated on the exact original left stage
and the exact cover used by its stored canonical leaves. -/
abbrev left_fibre_subpower (LA : SourceCartesianAtlas left fullI)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :=
  p.leftData.covered_index_fibre_subpower LA (primeSupport DE.1) DE.1
    p.left_columns (fun i => by rw [p.left_ideal]; exact b.left_residual i)
    (p.leftDivisorCoefficient S χ) (s.left S χ)

/-- The right direct stage uses the original right common ideal and
its true residual-column atlas, under the same fixed constant. -/
abbrev right_fibre_subpower (RA : SourceCartesianAtlas right fullJ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :=
  p.rightData.covered_index_fibre_subpower RA (primeSupport DE.1) DE.2
    p.right_columns (fun j => by rw [p.right_ideal]; exact b.right_residual j)
    (p.rightDivisorCoefficient S χ) (s.right S χ)

end FirstBlockDirectData.SecondStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.DirectGaussData.covered_index_fibre_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.left_fibre_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.right_fibre_subpower
