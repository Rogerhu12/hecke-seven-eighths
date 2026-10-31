import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualParentFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectCoveredFibreMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectLeafNormWindows

/-!
# Original finite fibres for the direct parent entrance

The direct source uses the same literal allocation fingerprint and the
same dependent finite-count lemmas as the amplified source.  Its index
is computed from the actual live leaves without any prime-pool tag.
The original masks, row classifier and Cartesian atlas prove the full
fibre estimate, including any actual retained rectangle subset.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.Moments.Support
open CommonSupportMass UniqueFactorizationMonoid OriginalFiniteFibre

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
local instance : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Θ : Type*} [Fintype Θ] {cap dimension width : ℕ} {B Z : ℝ}

namespace DirectGaussData

variable {ι : Type*} {originalColumns : Finset ι} {originalIdeal : ι → A.Exterior}
variable (d : DirectGaussData C ι)
variable (T : SourceCartesianAtlas originalColumns originalIdeal)
variable (support : Finset (Ideal (𝓞 K))) (D₀ : Ideal (𝓞 K))
variable (hcolumns : d.columns = originalColumns.filter
  (fun i => supportExtract (originalIdeal i).val support = D₀))
variable (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val support)
variable (c : ι → ℂ)
variable (s : ActualGaussStage (E := E) hΓ μv hDiff (d.directSource c) finiteTest)
local notation "CV" => d.sourceCartesianCover T support D₀ hcolumns hideal c

theorem original_predicate_subpower
    (hcap : T.slotCount ≤ cap) (ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hZ : 1 ≤ Z)
    (rows : s.OriginalFibreRows Θ dimension width B Z)
    (hD₀ : D₀ ≠ 0) (hND₀ : (Ideal.absNorm D₀ : ℝ) ≤ Z ^ B)
    (hN : ∀ i ∈ d.columns, (Ideal.absNorm (d.ideal i).val : ℝ) ≤ Z ^ B)
    (pred : s.CoveredLeafKey CV CV → Prop)
    (hrow : ∀ j, pred j → s.rowPresent CV CV j)
    (pair : Ideal (𝓞 K) × Ideal (𝓞 K)) (a : OriginalAllocationFingerprint K cap)
    (hcommon : ∀ j, pred j → j.1.1.val = pair)
    (hallocation : ∀ j, pred j →
      s.cappedAllocationFingerprint CV CV
        (fun q => (d.sourceCartesianCover_slotCount_le T support D₀ hcolumns hideal c q).trans hcap)
        (fun q => (d.sourceCartesianCover_slotCount_le T support D₀ hcolumns hideal c q).trans hcap)
        j = a) :
    realCount pred ≤ coordinateConstant (K := K) cap (Fintype.card Θ)
      dimension width B ε hB hε * Z ^ ε := by
  have hbound : 0 ≤ coordinateConstant (K := K) cap (Fintype.card Θ)
      dimension width B ε hB hε * Z ^ ε :=
    mul_nonneg (coordinateConstant_pos (K := K)
      cap (Fintype.card Θ) dimension width B ε hB hε).le
      (Real.rpow_nonneg (zero_le_one.trans hZ) ε)
  by_cases hex : ∃ j, pred j
  · obtain ⟨j₀, hj₀⟩ := hex
    let DE := j₀.1.1
    let leaves := Finset.univ.filter pred
    let hs : ∀ q, (CV.branch q).slotCount ≤ cap := fun q =>
      (d.sourceCartesianCover_slotCount_le T support D₀ hcolumns hideal c q).trans hcap
    let hl := fun v : s.CoveredClassKey CV CV => v.leftSlots_le hs
    let hr := fun v : s.CoveredClassKey CV CV => v.rightSupportSlots_le hs
    let index := s.cappedAllocationFingerprint CV CV hs hs
    have hn := actual_common_pair_norm _ _ _ _ (Z ^ B)
      (fun i _ => (d.ideal i).property.1) (fun i _ => (d.ideal i).property.1) hN hN DE
    have hc := d.covered_index_fibre_subpower T support D₀ hcolumns hideal c s
      cap dimension width hcap B ε Z hB hε hZ hl hr index id (fun _ => rfl) leaves a DE
      (fun j hj _ => Subtype.ext ((hcommon j (Finset.mem_filter.mp hj).2).trans
        (hcommon j₀ hj₀).symm))
      (fun j hj => hrow j (Finset.mem_filter.mp hj).2)
      rows.support (rows.code DE) (rows.encode DE) (rows.row_label DE)
      ⟨(actual_common_pair_properties _ _ _ _ DE).1,
        (actual_common_pair_properties _ _ _ _ DE).2.1⟩ hD₀
      rows.maskIdeal rows.rowIdeal rows.mask_nonzero rows.row_nonzero
      rows.maskPrimes rows.rowPrimes rows.mask_norm rows.row_norm hND₀ hn.1 hn.2
    have he : leaves.filter (fun j => index j = a) = leaves :=
      Finset.filter_eq_self.mpr (fun j hj => hallocation j (Finset.mem_filter.mp hj).2)
    rw [he] at hc
    exact hc
  · rw [realCount_eq_zero pred (fun j hj => hex ⟨j, hj⟩)]
    exact hbound

end DirectGaussData

namespace FirstBlockDirectData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap V ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart M X hX}

namespace SecondStages

variable (R : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

def rowPresent (j : R.CoveredLeafKey LA RA) : Prop :=
  match j.2.2 with
  | .inl k => (R.left j.1 j.2.1).rowPresent
      (p.leftSourceCover LA j.1 j.2.1) (p.leftSourceCover LA j.1 j.2.1) k
  | .inr k => (R.right j.1 j.2.1).rowPresent
      (p.rightSourceCover RA j.1 j.2.1) (p.rightSourceCover RA j.1 j.2.1) k

structure OriginalFibreRows (Θ : Type*) (dimension width : ℕ) (B Z : ℝ) where
  left : ∀ S χ, (R.left S χ).OriginalFibreRows Θ dimension width B Z
  right : ∀ S χ, (R.right S χ).OriginalFibreRows Θ dimension width B Z

theorem rowPresent_of_leaf_live
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (exceptional : R.CoverHybridPredicates LA RA)
    (j : R.CoveredLeafKey LA RA)
    (hj : (R.coveredLeaf LA RA NL NR hNL hNR exceptional j).Live) :
    R.rowPresent LA RA j := by
  rcases j with ⟨S, χ, j | j⟩
  · exact (R.left S χ).rowPresent_of_fiberLeaf_live
      (p.leftSourceCover LA S χ) (p.leftSourceCover LA S χ)
      (exceptional.left S χ) chart.kernel chart.leftPoint j
      (((R.left S χ).fiberCoveredLeaf (p.leftSourceCover LA S χ) (p.leftSourceCover LA S χ)
        (exceptional.left S χ) chart.kernel chart.leftPoint j).live_of_scale_live _ _ hj)
  · exact (R.right S χ).rowPresent_of_fiberLeaf_live
      (p.rightSourceCover RA S χ) (p.rightSourceCover RA S χ)
      (exceptional.right S χ) chart.kernel (fun i => -chart.rightPoint i) j
      (((R.right S χ).fiberCoveredLeaf (p.rightSourceCover RA S χ) (p.rightSourceCover RA S χ)
        (exceptional.right S χ) chart.kernel (fun i => -chart.rightPoint i) j).live_of_scale_live _ _ hj)

theorem original_predicate_subpower
    (hLA : LA.slotCount ≤ cap) (hRA : RA.slotCount ≤ cap)
    (ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hZ : 1 ≤ Z)
    (rows : R.OriginalFibreRows Θ dimension width B Z)
    (hDE : DE.1 ≠ 0 ∧ DE.2 ≠ 0)
    (hNDE : (Ideal.absNorm DE.1 : ℝ) ≤ Z ^ B ∧ (Ideal.absNorm DE.2 : ℝ) ≤ Z ^ B)
    (hL : ∀ i ∈ left, (Ideal.absNorm (fullI i).val : ℝ) ≤ Z ^ B)
    (hR : ∀ i ∈ right, (Ideal.absNorm (fullJ i).val : ℝ) ≤ Z ^ B)
    (pred : R.CoveredLeafKey LA RA → Prop)
    (hrow : ∀ j, pred j → R.rowPresent LA RA j)
    (S₀ : Ideal (𝓞 K)) (pair : Ideal (𝓞 K) × Ideal (𝓞 K))
    (a : OriginalAllocationFingerprint K cap)
    (hS₀ : ∀ j, pred j → j.1.val = S₀)
    (hcommon : ∀ j, pred j → R.commonLabel LA RA j = pair)
    (hallocation : ∀ j, pred j → R.allocationFingerprint LA RA hLA hRA j = a) :
    realCount pred ≤ 2 * (coordinateConstant (K := K) cap (Fintype.card Θ)
      dimension width B ε hB hε * Z ^ ε) := by
  let bound := coordinateConstant (K := K) cap (Fintype.card Θ)
    dimension width B ε hB hε * Z ^ ε
  have hb : 0 ≤ bound :=
    mul_nonneg (coordinateConstant_pos (K := K)
      cap (Fintype.card Θ) dimension width B ε hB hε).le
      (Real.rpow_nonneg (zero_le_one.trans hZ) ε)
  apply realCount_sigma_fixed_le pred Subtype.val Subtype.coe_injective S₀ hS₀
    (2 * bound) (mul_nonneg (by norm_num) hb)
  intro S
  apply realCount_sigma_subsingleton_le _ (2 * bound) (mul_nonneg (by norm_num) hb)
  intro χ
  rw [realCount_sum]
  have hl := p.leftData.original_predicate_subpower LA (primeSupport DE.1) DE.1
    p.left_columns (fun i => by rw [p.left_ideal]; exact b.left_residual i)
    (p.leftDivisorCoefficient S χ) (R.left S χ)
    hLA ε hB hε hZ (rows.left S χ) hDE.1 hNDE.1 (p.left_ideal_norm_le (Z ^ B) hL)
    (fun j => pred ⟨S, χ, .inl j⟩)
    (fun j hj => hrow ⟨S, χ, .inl j⟩ hj) pair a
    (fun j hj => hcommon ⟨S, χ, .inl j⟩ hj)
    (fun j hj => hallocation ⟨S, χ, .inl j⟩ hj)
  have hr := p.rightData.original_predicate_subpower RA (primeSupport DE.1) DE.2
    p.right_columns (fun i => by rw [p.right_ideal]; exact b.right_residual i)
    (p.rightDivisorCoefficient S χ) (R.right S χ)
    hRA ε hB hε hZ (rows.right S χ) hDE.2 hNDE.2 (p.right_ideal_norm_le (Z ^ B) hR)
    (fun j => pred ⟨S, χ, .inr j⟩)
    (fun j hj => hrow ⟨S, χ, .inr j⟩ hj) pair a
    (fun j hj => hcommon ⟨S, χ, .inr j⟩ hj)
    (fun j hj => hallocation ⟨S, χ, .inr j⟩ hj)
  exact (add_le_add hl hr).trans_eq (by dsimp only [bound]; ring)

end SecondStages
end FirstBlockDirectData

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualDirectFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

def rowPresent (j : R.CoveredLeafKey L) : Prop :=
  (R j.1 j.2.1).rowPresent L L j.2.2

structure OriginalFibreRows (Θ : Type*) (dimension width : ℕ) (B Z : ℝ) where
  source : ∀ v D, (R v D).OriginalFibreRows Θ dimension width B Z

theorem rowPresent_of_live (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) : R.rowPresent L j.val :=
  (R j.val.1 j.val.2.1).rowPresent_of_leaf_live L L
    (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
    (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
    (exceptional j.val.1 j.val.2.1) j.val.2.2
    (((R j.val.1 j.val.2.1).coveredLeaf L L
      (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
      (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
      (exceptional j.val.1 j.val.2.1) j.val.2.2).live_of_scale_live _ _
        (R.liveLeaves_spec L exceptional N j))

theorem original_predicate_subpower
    (hcap : L.slotCount ≤ cap) (δ₁ δ₂ : ℝ)
    (hB : 0 ≤ B) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hZ : 1 ≤ Z)
    (rows : R.OriginalFibreRows Θ dimension width B Z)
    (maskIdeal : Ideal (𝓞 K)) (hmask0 : maskIdeal ≠ 0)
    (mask : OriginalMaskPrimeData s.mask maskIdeal)
    (hmaskN : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
    (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B)
    (pred : R.CoveredLeafKey L → Prop) (hrow : ∀ j, pred j → R.rowPresent L j)
    (firstPair : Ideal (𝓞 K) × Ideal (𝓞 K)) (S₀ : Ideal (𝓞 K))
    (secondPair : Ideal (𝓞 K) × Ideal (𝓞 K))
    (allocation : OriginalAllocationFingerprint K cap)
    (hfirst : ∀ j, pred j → j.1.val = firstPair)
    (hS₀ : ∀ j, pred j → j.2.2.1.val = S₀)
    (hsecond : ∀ j, pred j → R.commonLabel L j = secondPair)
    (halloc : ∀ j, pred j →
      (R j.1 j.2.1).allocationFingerprint L L hcap hcap j.2.2 = allocation) :
    realCount pred ≤
      2 * firstMaskConstant (K := K) B δ₁ hB hδ₁ *
        coordinateConstant (K := K) cap (Fintype.card Θ) dimension width B δ₂ hB hδ₂ *
          Z ^ (δ₁ + δ₂) := by
  let Cm := firstMaskConstant (K := K) B δ₁ hB hδ₁
  let Cc := coordinateConstant (K := K) cap (Fintype.card Θ) dimension width B δ₂ hB hδ₂
  have hCm : 0 < Cm := firstMaskConstant_pos _ _ _ _
  have hCc : 0 < Cc := coordinateConstant_pos _ _ _ _ _ _ _ _
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  apply realCount_sigma_fixed_le pred Subtype.val Subtype.coe_injective firstPair hfirst
    (2 * Cm * Cc * Z ^ (δ₁ + δ₂)) (by positivity)
  intro v
  have hn := actual_common_pair_norm _ _ _ _ (Z ^ B)
    (fun i _ => (s.ideal i).property.1) (fun i _ => (s.ideal i).property.1) hN hN v
  have hp := actual_common_pair_properties _ _ _ _ v
  have hm := firstMaskCount_le B δ₁ hB hδ₁ hZ (s.block v)
    s.mask maskIdeal hmask0 hmaskN hn.1 mask
  have hl (D : ((s.block v).mask s.mask).powerset) :
      realCount (fun j => pred ⟨v, D, j⟩) ≤ 2 * (Cc * Z ^ δ₂) :=
    (R v D).original_predicate_subpower L L hcap hcap δ₂ hB hδ₂ hZ
      (rows.source v D) ⟨hp.1, hp.2.1⟩ hn hN hN
      (fun j => pred ⟨v, D, j⟩) (fun j hj => hrow ⟨v, D, j⟩ hj)
      S₀ secondPair allocation
      (fun j hj => hS₀ ⟨v, D, j⟩ hj)
      (fun j hj => hsecond ⟨v, D, j⟩ hj)
      (fun j hj => halloc ⟨v, D, j⟩ hj)
  calc
    _ ≤ (Fintype.card (((s.block v).mask s.mask).powerset) : ℝ) * (2 * (Cc * Z ^ δ₂)) :=
      realCount_sigma_le _ _ hl
    _ = (((s.block v).mask s.mask).powerset.card : ℝ) * (2 * (Cc * Z ^ δ₂)) := by
      rw [Fintype.card_coe]
    _ ≤ (Cm * Z ^ δ₁) * (2 * (Cc * Z ^ δ₂)) :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    _ = _ := by rw [Real.rpow_add hz]; ring

abbrev ArithmeticIndex (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization) :=
  (R.arithmeticLabels L hcap exceptional N).carrier.Index

def originalIndex (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) : R.ArithmeticIndex L hcap exceptional N :=
  (R.arithmeticLabels L hcap exceptional N).index j

theorem originalIndex_fibre_subpower
    (hcap : L.slotCount ≤ cap) (δ₁ δ₂ : ℝ)
    (hB : 0 ≤ B) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hZ : 1 ≤ Z)
    (rows : R.OriginalFibreRows Θ dimension width B Z)
    (maskIdeal : Ideal (𝓞 K)) (hmask0 : maskIdeal ≠ 0)
    (mask : OriginalMaskPrimeData s.mask maskIdeal)
    (hmaskN : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
    (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.ArithmeticIndex L hcap exceptional N) :
    ((Finset.univ.filter (fun i : R.liveLeaves L exceptional N =>
        R.originalIndex L hcap exceptional N i = j)).card : ℝ) ≤
      2 * firstMaskConstant (K := K) B δ₁ hB hδ₁ *
        coordinateConstant (K := K) cap (Fintype.card Θ) dimension width B δ₂ hB hδ₂ *
          Z ^ (δ₁ + δ₂) := by
  let labels := R.arithmeticLabels L hcap exceptional N
  let firstPair := j.1.val.1
  let S₀ := j.2.1.val
  let secondPair := j.2.2.1.val.1
  let allocation := labels.indexAllocation j
  let pred : R.CoveredLeafKey L → Prop := fun i =>
    R.rowPresent L i ∧ i.1.val = firstPair ∧ i.2.2.1.val = S₀ ∧
      R.commonLabel L i = secondPair ∧
      (R i.1 i.2.1).allocationFingerprint L L hcap hcap i.2.2 = allocation
  have hc := R.original_predicate_subpower L hcap δ₁ δ₂ hB hδ₁ hδ₂ hZ rows
    maskIdeal hmask0 mask hmaskN hN pred (fun _ h => h.1)
    firstPair S₀ secondPair allocation
    (fun _ h => h.2.1) (fun _ h => h.2.2.1)
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.2.2)
  apply le_trans (realCount_injective
    (P := fun i : R.liveLeaves L exceptional N => R.originalIndex L hcap exceptional N i = j)
    (Q := pred) Subtype.val Subtype.coe_injective ?_) hc
  intro i hi
  change labels.index i = j at hi
  exact ⟨R.rowPresent_of_live L exceptional N i,
    congrArg (fun v : labels.carrier.Index => v.1.val.1) hi,
    congrArg (fun v : labels.carrier.Index => v.2.1.val) hi,
    congrArg (fun v : labels.carrier.Index => v.2.2.1.val.1) hi,
    congrArg labels.indexAllocation hi⟩

/-- The exact active label subset of the normalized direct family,
including all retained ordinary rectangles, has the uniform fibre. -/
theorem originalIndex_retained_rectangles_fibre_subpower
    (hcap : L.slotCount ≤ cap) (δ₁ δ₂ : ℝ)
    (hB : 0 ≤ B) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hZ : 1 ≤ Z)
    (rows : R.OriginalFibreRows Θ dimension width B Z)
    (maskIdeal : Ideal (𝓞 K)) (hmask0 : maskIdeal ≠ 0)
    (mask : OriginalMaskPrimeData s.mask maskIdeal)
    (hmaskN : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
    (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (active : Finset ((R.liveLeaves L exceptional N) × (Bool × Bool)))
    (j : R.ArithmeticIndex L hcap exceptional N) :
    ((Finset.univ.filter (fun i : active => R.originalIndex L hcap exceptional N i.val.1 = j)).card : ℝ) ≤
      8 * firstMaskConstant (K := K) B δ₁ hB hδ₁ *
        coordinateConstant (K := K) cap (Fintype.card Θ) dimension width B δ₂ hB hδ₂ *
          Z ^ (δ₁ + δ₂) := by
  have ha : realCount (fun i : active => R.originalIndex L hcap exceptional N i.val.1 = j) ≤
      realCount (fun i : (R.liveLeaves L exceptional N) × (Bool × Bool) =>
        R.originalIndex L hcap exceptional N i.1 = j) :=
    realCount_injective Subtype.val Subtype.coe_injective (fun _ h => h)
  have hf := R.originalIndex_fibre_subpower L hcap δ₁ δ₂ hB hδ₁ hδ₂ hZ
    rows maskIdeal hmask0 mask hmaskN hN exceptional N j
  refine ha.trans ?_
  rw [realCount_prod_left]
  have hcard : (Fintype.card (Bool × Bool) : ℝ) = 4 := by norm_num
  rw [hcard]
  exact (mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring)

end ActualDirectFirstSource.SecondStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.DirectGaussData.original_predicate_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.originalIndex_fibre_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.originalIndex_retained_rectangles_fibre_subpower
