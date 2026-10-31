import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectLeafArithmetic
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualLeafNormWindows

/-!
# Original norm windows on the genuine direct arithmetic carrier

Only the original per-column ideal window and old-mask divisibility
enter the result.  Common extraction and the actual source dictionary
transport these bounds to both independent divisors.  The prepared
live leaf supplies squarefreeness and the inherited second old mask.
No prime pool or transformed-label estimate is an input.
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
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}

namespace FirstBlockDirectData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap V ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable (p : FirstBlockDirectData chart M X hX)

theorem left_ideal_norm_le (Y : ℝ)
    (hN : ∀ i ∈ left, (Ideal.absNorm (fullI i).val : ℝ) ≤ Y)
    (i : ι) (hi : i ∈ p.leftData.columns) :
    (Ideal.absNorm (p.leftData.ideal i).val : ℝ) ≤ Y := by
  rw [p.left_columns] at hi
  rw [p.left_ideal, b.left_residual]
  exact (actual_supportResidual_norm_le _ (fullI i).property.1 _).trans
    (hN i (Finset.mem_filter.mp hi).1)

theorem right_ideal_norm_le (Y : ℝ)
    (hN : ∀ i ∈ right, (Ideal.absNorm (fullJ i).val : ℝ) ≤ Y)
    (i : κ) (hi : i ∈ p.rightData.columns) :
    (Ideal.absNorm (p.rightData.ideal i).val : ℝ) ≤ Y := by
  rw [p.right_columns] at hi
  rw [p.right_ideal, b.right_residual]
  exact (actual_supportResidual_norm_le _ (fullJ i).property.1 _).trans
    (hN i (Finset.mem_filter.mp hi).1)

theorem firstDivisor_norm_le (Y : ℝ)
    (hN : ∀ i ∈ right, (Ideal.absNorm (fullJ i).val : ℝ) ≤ Y)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) :
    (Ideal.absNorm S.val : ℝ) ≤ Y :=
  actual_divisorPool_norm_le _ _ Y (fun i _ => (p.rightData.ideal i).property.1)
    (p.right_ideal_norm_le Y hN) S

namespace SecondStages

variable {p} (R : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

theorem commonLabel_norm_le (Y : ℝ)
    (hL : ∀ i ∈ left, (Ideal.absNorm (fullI i).val : ℝ) ≤ Y)
    (hR : ∀ i ∈ right, (Ideal.absNorm (fullJ i).val : ℝ) ≤ Y)
    (j : R.CoveredLeafKey LA RA) :
    (Ideal.absNorm (R.commonLabel LA RA j).1 : ℝ) ≤ Y ∧
      (Ideal.absNorm (R.commonLabel LA RA j).2 : ℝ) ≤ Y := by
  rcases j with ⟨S, χ, j | j⟩
  · exact actual_common_pair_norm _ _ _ _ Y
      (fun i _ => (p.leftData.ideal i).property.1)
      (fun i _ => (p.leftData.ideal i).property.1)
      (p.left_ideal_norm_le Y hL) (p.left_ideal_norm_le Y hL) j.1.1
  · exact actual_common_pair_norm _ _ _ _ Y
      (fun i _ => (p.rightData.ideal i).property.1)
      (fun i _ => (p.rightData.ideal i).property.1)
      (p.right_ideal_norm_le Y hR) (p.right_ideal_norm_le Y hR) j.1.1

theorem innerDivisor_norm_le (Y : ℝ)
    (hL : ∀ i ∈ left, (Ideal.absNorm (fullI i).val : ℝ) ≤ Y)
    (hR : ∀ i ∈ right, (Ideal.absNorm (fullJ i).val : ℝ) ≤ Y)
    (j : R.CoveredLeafKey LA RA) :
    (Ideal.absNorm (R.innerDivisor LA RA j) : ℝ) ≤ Y := by
  rcases j with ⟨S, χ, j | j⟩
  · exact (R.left S χ).covered_innerDivisor_norm_le
      (p.leftSourceCover LA S χ) (p.leftSourceCover LA S χ)
      Y (p.left_ideal_norm_le Y hL) j
  · exact (R.right S χ).covered_innerDivisor_norm_le
      (p.rightSourceCover RA S χ) (p.rightSourceCover RA S χ)
      Y (p.right_ideal_norm_le Y hR) j

variable
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)

theorem prepared_live_inner_squarefree
    (exceptional : R.prepared.CoverHybridPredicates LA RA)
    (j : R.prepared.CoveredLeafKey LA RA)
    (hj : (R.prepared.coveredLeaf LA RA NL NR hNL hNR exceptional j).Live) :
    Squarefree (R.prepared.innerDivisor LA RA j) := by
  rcases j with ⟨S, χ, j | j⟩
  · have hlive := ((R.left S χ).supported.gated.fiberCoveredLeaf
      (p.leftSourceCover LA S χ) (p.leftSourceCover LA S χ) (exceptional.left S χ)
      chart.kernel chart.leftPoint j).live_of_scale_live _ _ hj
    exact ((R.left S χ).supported_gated_fiberLeaf_live
      (p.leftSourceCover LA S χ) (p.leftSourceCover LA S χ) (exceptional.left S χ)
      chart.kernel chart.leftPoint j hlive).2.2
  · have hlive := ((R.right S χ).supported.gated.fiberCoveredLeaf
      (p.rightSourceCover RA S χ) (p.rightSourceCover RA S χ) (exceptional.right S χ)
      chart.kernel (fun i => -chart.rightPoint i) j).live_of_scale_live _ _ hj
    exact ((R.right S χ).supported_gated_fiberLeaf_live
      (p.rightSourceCover RA S χ) (p.rightSourceCover RA S χ) (exceptional.right S χ)
      chart.kernel (fun i => -chart.rightPoint i) j hlive).2.2

end SecondStages
end FirstBlockDirectData

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualDirectFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

theorem prepared_live_inner_divisor_squarefree
    (exceptional : R.prepared.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.prepared.liveLeaves L exceptional N) :
    Squarefree (R.prepared.innerDivisor L j.val) := by
  have hlive := ((R.prepared j.val.1 j.val.2.1).coveredLeaf L L
    (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
    (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
    (exceptional j.val.1 j.val.2.1) j.val.2.2).live_of_scale_live _ _
      (R.prepared.liveLeaves_spec L exceptional N j)
  exact (R j.val.1 j.val.2.1).prepared_live_inner_squarefree L L
    (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
    (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
    (exceptional j.val.1 j.val.2.1) j.val.2.2 hlive

/-- Admissibility is derived from the original source windows on the
same actual live carrier, with both divisors and both allocations kept. -/
theorem arithmeticLabels_admissible {cap : ℕ} (hcap : L.slotCount ≤ cap)
    (exceptional : R.prepared.CoverHybridPredicates L) (N : s.Normalization)
    (B : ℝ) (oldMask : Ideal (𝓞 K)) (hs : Squarefree oldMask)
    (hmask : ∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val)
    (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B) :
    (R.prepared.arithmeticLabels L hcap exceptional N).carrier.Admissible
      (cap + 2) B Z oldMask := by
  apply OriginalArithmeticLabels.carrier_admissible
  · intro j
    have hp := actual_common_pair_properties _ _ _ _ j.val.1
    have hdiv : oldMask ∣ j.val.1.val.1 ∧ oldMask ∣ j.val.1.val.2 := by
      obtain ⟨ij, hij, he⟩ := Finset.mem_image.mp j.val.1.property
      have hi := (Finset.mem_product.mp hij).1
      have hj := (Finset.mem_product.mp hij).2
      have hd := actual_common_label_old_mask oldMask (s.ideal ij.1).val (s.ideal ij.2).val
        hs (s.ideal ij.1).property.1 (s.ideal ij.2).property.1 (hmask ij.1 hi) (hmask ij.2 hj)
      simpa only [he] using hd
    exact ⟨hp.1, hp.2.1, hp.2.2, hdiv.1, hdiv.2, Finset.empty_subset _⟩
  · intro j
    exact actual_common_pair_norm _ _ _ _ (Z ^ B)
      (fun i _ => (s.ideal i).property.1) (fun i _ => (s.ideal i).property.1) hN hN j.val.1
  · intro j
    have hS := R.prepared.live_first_divisor_squarefree L exceptional N j
    exact ⟨hS, hS.ne_zero⟩
  · intro j
    exact (s.pieces j.val.1 j.val.2.1).firstDivisor_norm_le (Z ^ B) hN j.val.2.2.1
  · intro j
    exact R.prepared_arithmeticLabels_second_valid L hcap exceptional N j
  · intro j
    exact (R.prepared j.val.1 j.val.2.1).commonLabel_norm_le
      L L (Z ^ B) hN hN j.val.2.2
  · intro j
    rw [R.prepared.arithmeticLabels_secondDivisor]
    exact (R.prepared_live_inner_divisor_squarefree L exceptional N j).ne_zero
  · intro j
    rw [R.prepared.arithmeticLabels_secondDivisor]
    exact (R.prepared j.val.1 j.val.2.1).innerDivisor_norm_le
      L L (Z ^ B) hN hN j.val.2.2

end ActualDirectFirstSource.SecondStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.innerDivisor_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.prepared_live_inner_divisor_squarefree
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.arithmeticLabels_admissible
