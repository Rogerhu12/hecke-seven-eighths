import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCoveredFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalCoordinateSubpower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalSourceSlotCaps

/-!
# Uniform fibres for the actual main and valuation source covers

The first two support-key bounds below come from the actual cover
constructors.  The second two come from the actual common extraction.
Both Boolean subset factors use original prime identifications.  The
result concerns the literal `CoveredLeafKey` fibre of the supplied
arithmetic index; there is no aggregate fibre bound among its inputs.
The selected constant depends only on the fixed original cap, norm
window, character classifier and dyadic box, before the moving source.
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
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local instance actualCoveredFibreMassCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

private theorem fibre_uniform_from_original_counts
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
    (LC RC : SourceCartesianCover G.columns G.ideal)
    (cap dimension width : ℕ) (B ε Z : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hZ : 1 ≤ Z)
    (hleft : ∀ v : s.CoveredClassKey LC RC, v.leftSlots ≤ cap)
    (hright : ∀ v : s.CoveredClassKey LC RC, v.rightSupportSlots ≤ cap)
    {J ρ Θ : Type*} [Fintype Θ]
    (index : s.CoveredLeafKey LC RC → J)
    (allocation : J → OriginalAllocationFingerprint K cap)
    (hindex : ∀ b, allocation (index b) =
      ActualGaussStage.coveredAllocationFingerprint hleft hright b)
    (leaves : Finset (s.CoveredLeafKey LC RC)) (j : J)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (hcommon : ∀ b ∈ leaves, index b = j → b.1.1 = DE)
    (hrow : ∀ b ∈ leaves, b.1.rowLabel ∈ s.actualRowLabels b.1.1 b.1.2.1)
    (support : Finset ρ)
    (code : s.mask.powerset → Q → OriginalFiniteFibre.RowCode support Θ dimension width)
    (encode : ∀ D : s.mask.powerset,
      OriginalFiniteFibre.RowCode support Θ dimension width →
        Fin ((s.charts DE D).rowLabelCount + 1))
    (hcode : ∀ D : s.mask.powerset, ∀ h ∈ (s.sources DE).rows,
      (s.charts DE D).rowLabel h = encode D (code D h))
    (hDE : DE.val.1 ≠ 0 ∧ DE.val.2 ≠ 0)
    (hLC : ∀ a, (LC.branch a).slotCount ≤ cap)
    (hRC : ∀ a, (RC.branch a).slotCount ≤ cap)
    (Rmask Rrow I₁ I₂ : Ideal (𝓞 K))
    (hRmask : Rmask ≠ 0) (hRrow : Rrow ≠ 0)
    (WM : OriginalMaskPrimeData s.mask Rmask) (WR : OriginalMaskPrimeData support Rrow)
    (hNmask : (Ideal.absNorm Rmask : ℝ) ≤ Z ^ B)
    (hNrow : (Ideal.absNorm Rrow : ℝ) ≤ Z ^ B)
    (hNI₁ : (Ideal.absNorm I₁ : ℝ) ≤ Z ^ B)
    (hNI₂ : (Ideal.absNorm I₂ : ℝ) ≤ Z ^ B)
    (hND : (Ideal.absNorm DE.val.1 : ℝ) ≤ Z ^ B)
    (hNE : (Ideal.absNorm DE.val.2 : ℝ) ≤ Z ^ B)
    (hkeyL : LC.labels.card ≤ idealDivisorCount I₁ ^ (cap + 2))
    (hkeyR : RC.labels.card ≤ idealDivisorCount I₂ ^ (cap + 2)) :
    ((leaves.filter (fun b => index b = j)).card : ℝ) ≤
      OriginalFiniteFibre.coordinateConstant (K := K) cap (Fintype.card Θ)
        dimension width B ε hB hε * Z ^ ε := by
  have hraw := covered_index_fibre_card_le_coordinates hleft hright
    index allocation hindex leaves j DE hcommon hrow support dimension width code encode hcode
      hDE hLC hRC
  have hn : (leaves.filter (fun b => index b = j)).card ≤
      OriginalFiniteFibre.coordinateCount s.mask support I₁ I₂ DE.val.1 DE.val.2
        cap (Fintype.card Θ) dimension width := by
    refine hraw.trans ?_
    unfold OriginalFiniteFibre.coordinateCount
    change _ ≤ 2 ^ s.mask.card * idealDivisorCount I₁ ^ (cap + 2) *
      idealDivisorCount I₂ ^ (cap + 2) *
        (2 ^ support.card * Fintype.card Θ * (width + 1) ^ dimension) *
          idealDivisorCount DE.val.1 ^ (cap + 2) * idealDivisorCount DE.val.2 ^ (cap + 2)
    gcongr <;> assumption
  have hnreal : ((leaves.filter (fun b => index b = j)).card : ℝ) ≤
      (OriginalFiniteFibre.coordinateCount s.mask support I₁ I₂ DE.val.1 DE.val.2
        cap (Fintype.card Θ) dimension width : ℝ) := by exact_mod_cast hn
  exact hnreal.trans (OriginalFiniteFibre.coordinateCount_le
    cap (Fintype.card Θ) dimension width B ε hB hε Z hZ
    s.mask support Rmask Rrow I₁ I₂ DE.val.1 DE.val.2 hRmask hRrow
    hNmask hNrow hNI₁ hNI₂ hND hNE WM WR)

end ActualGaussStage

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
variable {originalColumns : Finset ι} {originalIdeal : ι → A.Exterior}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

namespace FirstGaussPoolData

variable (d : FirstGaussPoolData C P ι)
variable (T : SourceCartesianAtlas originalColumns originalIdeal)
variable (S : Finset (Ideal (𝓞 K))) (D₀ : Ideal (𝓞 K))
variable (hcolumns : d.columns =
  originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D₀))
variable (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val S)
variable (c : ι → ℂ)

section Main

variable (s : ActualGaussStage (E := E) hΓ μv hDiff (d.mainSource c) finiteTest)
local notation "CV" => d.mainSourceCartesianCover T S D₀ hcolumns hideal c

/-- The actual main-source fibre has a uniform small power.  Both
earlier cover counts and both inherited slot caps are proved from its
original atlas; no finite-fibre or cover-count estimate is assumed. -/
theorem main_covered_index_fibre_subpower
    (cap dimension width : ℕ) (hcap : T.slotCount ≤ cap)
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hZ : 1 ≤ Z)
    (hleft : ∀ v : s.CoveredClassKey CV CV, v.leftSlots ≤ cap)
    (hright : ∀ v : s.CoveredClassKey CV CV, v.rightSupportSlots ≤ cap)
    {J ρ Θ : Type*} [Fintype Θ]
    (index : s.CoveredLeafKey CV CV → J)
    (allocation : J → OriginalAllocationFingerprint K cap)
    (hindex : ∀ b, allocation (index b) =
      ActualGaussStage.coveredAllocationFingerprint hleft hright b)
    (leaves : Finset (s.CoveredLeafKey CV CV)) (j : J)
    (DE : commonSupportPool (d.mainSource c).columns (d.mainSource c).columns
      (fun i => ((d.mainSource c).ideal i).val) (fun j => ((d.mainSource c).ideal j).val))
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
    (d.mainSourceCartesianCover_slotCount_le T S D₀ hcolumns hideal c a).trans hcap
  have hkeys : (CV).labels.card ≤ idealDivisorCount D₀ ^ (cap + 2) :=
    d.mainSourceCartesianCover_card_le T S D₀ hcolumns hideal cap hcap hD₀ c
  exact ActualGaussStage.fibre_uniform_from_original_counts s CV CV
    cap dimension width B ε Z hB hε hZ hleft hright
    index allocation hindex leaves j DE hcommon hrow support code encode hcode hDE hslots hslots
    Rmask Rrow D₀ D₀ hRmask hRrow WM WR hNmask hNrow hND₀ hND₀ hND hNE hkeys hkeys

end Main

section Residual

variable (p : ExteriorPrime A) (n : ℕ)
variable (s : ActualGaussStage (E := E) hΓ μv hDiff (d.residualSource p n c) finiteTest)
local notation "CV" => d.residualSourceCartesianCover T S D₀ hcolumns hideal p n c

/-- The actual valuation source retains p and n in its index.  Its
cover cost is the divisor count of the true extracted ideal D₀ p^n,
so there is no extra cardinality factor for the prime pool. -/
theorem residual_covered_index_fibre_subpower
    (cap dimension width : ℕ) (hcap : T.slotCount ≤ cap)
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hZ : 1 ≤ Z)
    (hleft : ∀ v : s.CoveredClassKey CV CV, v.leftSlots ≤ cap)
    (hright : ∀ v : s.CoveredClassKey CV CV, v.rightSupportSlots ≤ cap)
    {J ρ Θ : Type*} [Fintype Θ]
    (index : s.CoveredLeafKey CV CV → J)
    (allocation : J → OriginalAllocationFingerprint K cap)
    (hindex : ∀ b, allocation (index b) =
      ActualGaussStage.coveredAllocationFingerprint hleft hright b)
    (leaves : Finset (s.CoveredLeafKey CV CV)) (j : J)
    (DE : commonSupportPool (d.residualSource p n c).columns (d.residualSource p n c).columns
      (fun i => ((d.residualSource p n c).ideal i).val)
        (fun j => ((d.residualSource p n c).ideal j).val))
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
    (hNcombined : (Ideal.absNorm (D₀ * p.val.asIdeal ^ n) : ℝ) ≤ Z ^ B)
    (hND : (Ideal.absNorm DE.val.1 : ℝ) ≤ Z ^ B)
    (hNE : (Ideal.absNorm DE.val.2 : ℝ) ≤ Z ^ B) :
    ((leaves.filter (fun b => index b = j)).card : ℝ) ≤
      OriginalFiniteFibre.coordinateConstant (K := K) cap (Fintype.card Θ)
        dimension width B ε hB hε * Z ^ ε := by
  have hslots : ∀ a, ((CV).branch a).slotCount ≤ cap := fun a =>
    (d.residualSourceCartesianCover_slotCount_le T S D₀ hcolumns hideal p n c a).trans hcap
  have hkeys : (CV).labels.card ≤ idealDivisorCount (D₀ * p.val.asIdeal ^ n) ^ (cap + 2) :=
    d.residualSourceCartesianCover_card_le T S D₀ hcolumns hideal cap hcap hD₀ p n c
  exact ActualGaussStage.fibre_uniform_from_original_counts s CV CV
    cap dimension width B ε Z hB hε hZ hleft hright
    index allocation hindex leaves j DE hcommon hrow support code encode hcode hDE hslots hslots
    Rmask Rrow (D₀ * p.val.asIdeal ^ n) (D₀ * p.val.asIdeal ^ n)
    hRmask hRrow WM WR hNmask hNrow hNcombined hNcombined hND hNE hkeys hkeys

end Residual
end FirstGaussPoolData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.main_covered_index_fibre_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.residual_covered_index_fibre_subpower
