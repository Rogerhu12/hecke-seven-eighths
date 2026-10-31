import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedFreeEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualPositiveIndex
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveRetained

/-!
# The actual first free energy is the next Poisson input

The second input below is constructed from the first production family,
its retained label, its original mask divisor, and the fixed positive
orbital row majorant. The positive row cap is explicit: a proved larger
cap can therefore be selected before the second transform. The complete
column pool and its wide Schwartz support are proved from the first
centered family, not postulated for a new source.

The fresh common/divisor/frequency index is identified with the positive
reconstruction index. Its common ideal remains fixed when the independent
second Moebius overlap is subsequently adjoined.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstToSecondData

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstColumnAssembly
  FirstParentRows FirstOuterCenters InverseRowMajorant CommonKernel
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K
variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ))

def quotient (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o) : Ext :=
  FirstMobiusGeometry.overlapIdeal K S D T.scale
    (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val false e

def triple (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o) :
    OuterTriple K :=
  firstTriple K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
    o.1.val o.2.1.val (quotient K S D T o e)

def label (o : OuterIndex K S D T) : Ext :=
  CanonicalIdealRow.toExterior K S
    (retainedLabel K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
      o.1.val o.2.1.val)

/-- One scale for the complete fixed-center pool, independent of every
arithmetic reconstruction, label and row. -/
def sourceScale (U : {r : ℝ // 0 < r}) : ℝ :=
  T.columns.base ^ (Real.log U.val / Real.log T.columns.base)

theorem sourceScale_eq (hbase : 1 < T.columns.base) (U : {r : ℝ // 0 < r}) :
    sourceScale K S T U = U.val :=
  FirstCompleteFamily.norm_scale T.columns.base U.val hbase U.property

variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)

/-- Literal first output, now packaged for the actual second transform.
The field frequencyBound is unused by the adaptive cutoff construction. -/
def data (hbase : 1 < T.columns.base)
    (R : OuterIndex K S D T → {r : ℝ // 0 < r})
    (U : {r : ℝ // 0 < r}) (J : Finset σ) (s : ℝ)
    (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o) :
    SecondParentProduction.Data K S σ Θ ψ where
  columns := FirstCenteredFamily.family K S T.columns Θ ψ G hν hG J U.val (-(1 / 2 : ℝ)) s
  triple := triple K S D T o e
  label := label K S D T o
  divisor := FirstLocalizedEnergy.divisor K S D T o
  archTest := Physical.ActualGramMajorantDraft.rowBallArchTest K S 1
  localTest := Physical.ActualGramMajorantDraft.rowBallFiniteFamily K S 1
  locallyConstant := Physical.ActualGramMajorantDraft.rowBallFiniteFamily_locallyConstant K S 1
  compactSupport := Physical.ActualGramMajorantDraft.rowBallFiniteFamily_compactSupport K S 1
  radius := rowRadius (R o)
  frequencyBound := 1
  base_gt_one := hbase
  cutoffSupport := WideMellinTests.weightedTest_support (-(1 / 2 : ℝ)) s
  fullPool := by
    change squarefreePool K Sset (2 * U.val) =
      squarefreePool K Sset
        (2 * T.columns.base ^ (Real.log U.val / Real.log T.columns.base))
    rw [FirstCompleteFamily.norm_scale T.columns.base U.val hbase U.property]

variable (hbase : 1 < T.columns.base)
variable (R : OuterIndex K S D T → {r : ℝ // 0 < r})
variable (U : {r : ℝ // 0 < r}) (J : Finset σ) (s : ℝ)

@[simp] theorem data_scale (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) :
    SecondParentProduction.scale K S (data K S D T Θ ψ G hν hG hbase R U J s o e) =
      sourceScale K S T U := rfl

theorem data_scale_eq (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) :
    SecondParentProduction.scale K S (data K S D T Θ ψ G hν hG hbase R U J s o e) = U.val :=
  sourceScale_eq K S T hbase U

@[simp] theorem data_radius (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) :
    (data K S D T Θ ψ G hν hG hbase R U J s o e).radius = rowRadius (R o) := rfl

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [Γ.FiniteIndex]

/-- The energy is the one in the first production integral, with its
actual coefficients and its fixed divisor still inside the inverse row. -/
theorem first_freeEnergy_eq_second (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) :
    FirstFreeMellinEnergy.freeEnergyAt K S Γ D T.columns Θ ψ G hν hG J U.val
      (-(1 / 2 : ℝ)) (triple K S D T o e) (label K S D T o).val.val
      (FirstLocalizedEnergy.divisor K S D T o).val (R o) s =
    let Q := data K S D T Θ ψ G hν hG hbase R U J s o e
    (DivisorInverseColumn.weightedEnergy K S Γ D Q.columns Q.triple Q.label.val.val
      Q.divisor.val Q.archTest Q.localTest ∅ Q.radius).re := rfl

variable (H₂ : ∀ o : OuterIndex K S D T, (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))) → Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)) → ℝ)

def actualCutoff : ActualPositiveIndex.Cutoff K S D T (sourceScale K S T U) :=
  fun o _ g δ => H₂ o g.val δ.val

/-- These are exactly the indices of the actual second production, with
its independent full-Moebius overlap adjoined after the common ideal. -/
abbrev ProductionIndex :=
  Σ o : OuterIndex K S D T, Σ e : FirstOuterCenters.Overlap K S D T o,
    Σ i : SecondAdaptiveRetained.IndexAt K S D Γ
        (data K S D T Θ ψ G hν hG hbase R U J s o e) (H₂ o),
      SecondMobiusGeometry.overlapPool K S (sourceScale K S T U) i.1.val

def indexEquiv :
    ProductionIndex K S D T Θ ψ G hν hG hbase R U J s Γ H₂ ≃
      ActualPositiveIndex.Index K S D Γ T (sourceScale K S T U)
        (actualCutoff K S D T U H₂) where
  toFun := fun i => ⟨i.1, i.2.1, i.2.2.1.1, i.2.2.1.2.1, i.2.2.1.2.2, i.2.2.2⟩
  invFun := fun i => ⟨i.1, i.2.1, ⟨i.2.2.1, i.2.2.2.1, i.2.2.2.2.1⟩, i.2.2.2.2.2⟩
  left_inv := by rintro ⟨o,e,⟨g,δ,z⟩,v⟩; rfl
  right_inv := by rintro ⟨o,e,g,δ,z,v⟩; rfl

def bare (hmask : T.mask = ∅)
    (i : ProductionIndex K S D T Θ ψ G hν hG hbase R U J s Γ H₂) :
    PositiveAssignedSource.BareSource (K := K) (S := S) (D := D) (Γ := Γ)
      (N := FirstParentEnergy.columnPool K S T) (X := sourceScale K S T U) :=
  ActualPositiveIndex.bare K S D Γ T hmask (sourceScale K S T U)
    (actualCutoff K S D T U H₂)
    (indexEquiv K S D T Θ ψ G hν hG hbase R U J s Γ H₂ i)

theorem bare_injective (hmask : T.mask = ∅) :
    Function.Injective (bare K S D T Θ ψ G hν hG hbase R U J s Γ H₂ hmask) :=
  (ActualPositiveIndex.bare_injective K S D Γ T hmask (sourceScale K S T U)
    (actualCutoff K S D T U H₂)).comp
      (indexEquiv K S D T Θ ψ G hν hG hbase R U J s Γ H₂).injective

theorem bare_common (hmask : T.mask = ∅)
    (i : ProductionIndex K S D T Θ ψ G hν hG hbase R U J s Γ H₂) :
    (bare K S D T Θ ψ G hν hG hbase R U J s Γ H₂ hmask i).common = i.2.2.1.1.val := rfl

theorem bare_firstLabel (hmask : T.mask = ∅)
    (i : ProductionIndex K S D T Θ ψ G hν hG hbase R U J s Γ H₂) :
    (bare K S D T Θ ψ G hν hG hbase R U J s Γ H₂ hmask i).firstLabel =
      (data K S D T Θ ψ G hν hG hbase R U J s i.1 i.2.1).label := rfl

theorem bare_newRow (hmask : T.mask = ∅)
    (i : ProductionIndex K S D T Θ ψ G hν hG hbase R U J s Γ H₂) :
    ((SecondAdaptiveRetained.selectedRowAt K S D Γ
        (data K S D T Θ ψ G hν hG hbase R U J s i.1 i.2.1) (H₂ i.1) i.2.2.1).val.val,
      SecondAdaptiveRetained.selectedSectorAt K S D Γ
        (data K S D T Θ ψ G hν hG hbase R U J s i.1 i.2.1) (H₂ i.1) i.2.2.1) =
      (bare K S D T Θ ψ G hν hG hbase R U J s Γ H₂ hmask i).newRow :=
  (bare K S D T Θ ψ G hν hG hbase R U J s Γ H₂ hmask i).literal_row

/-- The whole finite source is preserved under the actual index map.
This applies before or after fixing any finite norm box and does not
assume a source identity or a reconstruction energy bound. -/
theorem production_source_sum {A : Type*} [AddCommMonoid A]
    (hmask : T.mask = ∅)
    (F : PositiveAssignedSource.BareSource (K := K) (S := S) (D := D) (Γ := Γ)
      (N := FirstParentEnergy.columnPool K S T) (X := sourceScale K S T U) → A) :
    (∑ B ∈ ActualPositiveIndex.source K S D Γ T hmask (sourceScale K S T U)
      (actualCutoff K S D T U H₂) Finset.univ, F B) =
      ∑ i : ProductionIndex K S D T Θ ψ G hν hG hbase R U J s Γ H₂,
        F (bare K S D T Θ ψ G hν hG hbase R U J s Γ H₂ hmask i) := by
  rw [ActualPositiveIndex.source_sum]
  exact ((indexEquiv K S D T Θ ψ G hν hG hbase R U J s Γ H₂).sum_comp
    (fun i => F (ActualPositiveIndex.bare K S D Γ T hmask (sourceScale K S T U)
      (actualCutoff K S D T U H₂) i))).symm

/-- The fine cutoff uses the frozen common ideal and actual second
divisor. In particular it is independent of both child residual columns. -/
def fineCutoff (Z tau : ℝ) (o : OuterIndex K S D T) :
    Ext → Finset (HeightOneSpectrum OS) → ℝ :=
  SecondAdaptiveCutoff.fineCutoff K S (rowRadius (R o)) (sourceScale K S T U) Z tau

theorem fineIndex_eq (Z tau : ℝ) (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) :
    SecondAdaptiveRetained.FineIndex K S D Γ
      (data K S D T Θ ψ G hν hG hbase R U J s o e) Z tau =
    SecondAdaptiveRetained.IndexAt K S D Γ
      (data K S D T Θ ψ G hν hG hbase R U J s o e)
      (fineCutoff K S D T R U Z tau o) := rfl

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstToSecondData

end
