import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualLeafArithmetic

set_option linter.unusedSectionVars false

set_option Elab.async false
set_option stderrAsMessages false

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS ActualLeafNormWindows imports_done"
  log.flush

/-!
# Original ideal windows reach every actual arithmetic label

Neither common extraction nor the true amplifier quotient increases
an ideal norm. The independent second divisor divides an original
residual column, whose membership is supplied by its actual Cartesian
dictionary. This transports one original per-column norm window to the
four arithmetic coordinates of every genuine retained leaf.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LocalFiniteSums (ExteriorPrime)
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.Moments.Support
open HeckePort.IdealMobiusDivisorSum CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

theorem actual_supportResidual_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (T : Finset (Ideal (𝓞 K))) : supportResidual I T ∣ I := by
  refine ⟨supportExtract I T, ?_⟩
  exact (support_reconstruct I (by simpa only [Ideal.zero_eq_bot] using hI) T).symm.trans
    (mul_comm _ _)

theorem actual_supportResidual_norm_le (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (T : Finset (Ideal (𝓞 K))) :
    (Ideal.absNorm (supportResidual I T) : ℝ) ≤ Ideal.absNorm I :=
  norm_le_of_dvd hI (actual_supportResidual_dvd I hI T)

theorem actual_divisorPool_norm_le {ι : Type*}
    (columns : Finset ι) (ideal : ι → Ideal (𝓞 K)) (Y : ℝ)
    (hI : ∀ i ∈ columns, ideal i ≠ 0)
    (hN : ∀ i ∈ columns, (Ideal.absNorm (ideal i) : ℝ) ≤ Y)
    (S : divisorPool columns ideal) : (Ideal.absNorm S.val : ℝ) ≤ Y := by
  obtain ⟨i, hi, hSi⟩ := Finset.mem_biUnion.mp S.property
  exact (norm_le_of_dvd (hI i hi) ((mem_idealDivisors (hI i hi)).mp hSi)).trans (hN i hi)

theorem actual_common_pair_properties {ι κ : Type*}
    (left : Finset ι) (right : Finset κ)
    (I : ι → Ideal (𝓞 K)) (J : κ → Ideal (𝓞 K))
    (DE : commonSupportPool left right I J) :
    DE.val.1 ≠ 0 ∧ DE.val.2 ≠ 0 ∧ primeSupport DE.val.1 = primeSupport DE.val.2 := by
  have hn := commonSupportPool_nonzero left right I J DE.val DE.property
  exact ⟨by simpa only [Ideal.zero_eq_bot] using hn.1,
    by simpa only [Ideal.zero_eq_bot] using hn.2,
    commonSupportPool_support_eq left right I J DE.val DE.property⟩

theorem actual_common_pair_norm {ι κ : Type*}
    (left : Finset ι) (right : Finset κ)
    (I : ι → Ideal (𝓞 K)) (J : κ → Ideal (𝓞 K)) (Y : ℝ)
    (hI : ∀ i ∈ left, I i ≠ 0) (hJ : ∀ j ∈ right, J j ≠ 0)
    (hNI : ∀ i ∈ left, (Ideal.absNorm (I i) : ℝ) ≤ Y)
    (hNJ : ∀ j ∈ right, (Ideal.absNorm (J j) : ℝ) ≤ Y)
    (DE : commonSupportPool left right I J) :
    (Ideal.absNorm DE.val.1 : ℝ) ≤ Y ∧ (Ideal.absNorm DE.val.2 : ℝ) ≤ Y := by
  obtain ⟨ij, hij, he⟩ := Finset.mem_image.mp DE.property
  have hi := (Finset.mem_product.mp hij).1
  have hj := (Finset.mem_product.mp hij).2
  have hn := actual_common_label_norm_le (I ij.1) (J ij.2) (hI ij.1 hi) (hJ ij.2 hj)
  rw [he] at hn
  exact ⟨hn.1.trans (hNI ij.1 hi), hn.2.trans (hNJ ij.2 hj)⟩

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
local instance actualLeafNormWindowsCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

namespace ActualGaussStage

variable {G : ActualGaussSource C ι}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
variable (LC RC : SourceCartesianCover G.columns G.ideal)

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS ActualLeafNormWindows helpers_done__covered_innerDivisor_norm_le_before"
  log.flush

/-- The actual second Möbius divisor is bounded through its original
right column. All three support filters are retained in this proof. -/
theorem covered_innerDivisor_norm_le (Y : ℝ)
    (hN : ∀ i ∈ G.columns, (Ideal.absNorm (G.ideal i).val : ℝ) ≤ Y)
    (j : s.CoveredLeafKey LC RC) : Nat.cast (R := ℝ) (Ideal.absNorm j.2.1.val) ≤ Y := by
  let v := j.1
  have hcolumns :
      ∀ i ∈ childCartesianColumns
          v.rightReindex.plain₁ v.rightReindex.plain₂ v.rightReindex.slots,
        (Ideal.absNorm (v.block.rightResidual (v.rightReindex.index i)).val : ℝ) ≤ Y := by
    intro i hi
    have hf := v.rightReindex.maps i hi
    have hc := (RC.branch v.2.2.2.1).commonFibre_subset
      (primeSupport v.1.val.1) v.1.val.2 v.2.2.2.2.2.2 hf
    have horiginal : v.rightReindex.index i ∈ G.columns :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
    rw [v.block.right_residual]
    exact (actual_supportResidual_norm_le _ (G.ideal (v.rightReindex.index i)).property.1 _).trans
      (hN _ horiginal)
  exact actual_divisorPool_norm_le
    (childCartesianColumns v.rightReindex.plain₁ v.rightReindex.plain₂ v.rightReindex.slots)
    (fun i => (v.block.rightResidual (v.rightReindex.index i)).val) Y
    (fun i _ => (v.block.rightResidual (v.rightReindex.index i)).property.1) hcolumns j.2.1

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS ActualLeafNormWindows covered_innerDivisor_norm_le_done"
  log.flush

end ActualGaussStage

namespace FirstGaussPoolData

variable (d : FirstGaussPoolData C P ι)

theorem residualSource_ideal_norm_le (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ)
    (i : d.valuationColumns p n) :
    (Ideal.absNorm ((d.residualSource p n c).ideal i).val : ℝ) ≤
      Ideal.absNorm (d.ideal i.val).val := by
  apply norm_le_of_dvd (d.ideal i.val).property.1
  refine ⟨p.val.asIdeal ^ n, ?_⟩
  exact (d.residualPresentation p n i).reconstructed.trans (mul_comm _ _)

end FirstGaussPoolData

namespace ActualPoolStages

variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)
variable (B : d.SourceCovers c)

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS ActualLeafNormWindows pool_commonLabel_properties_before"
  log.flush

theorem commonLabel_properties (j : s.CoveredLeafKey B) :
    (s.commonLabel B j).1 ≠ 0 ∧ (s.commonLabel B j).2 ≠ 0 ∧
      primeSupport (s.commonLabel B j).1 = primeSupport (s.commonLabel B j).2 := by
  let goal : s.CoveredLeafKey B → Prop := fun key =>
    (s.commonLabel B key).1 ≠ 0 ∧ (s.commonLabel B key).2 ≠ 0 ∧
      primeSupport (s.commonLabel B key).1 = primeSupport (s.commonLabel B key).2
  exact Sum.rec (motive := goal)
    (fun a => actual_common_pair_properties _ _ _ _ a.1.1)
    (fun tail => Sum.rec (motive := fun tail => goal (.inr tail))
      (fun a => actual_common_pair_properties _ _ _ _ a.2.1.1)
      (fun tail => Sum.rec (motive := fun tail => goal (.inr (.inr tail)))
        (fun a => actual_common_pair_properties _ _ _ _ a.2.1.1)
        (fun a => actual_common_pair_properties _ _ _ _ a.2.1.1) tail) tail) j

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS ActualLeafNormWindows pool_commonLabel_properties_done__commonLabel_norm_le_before"
  log.flush

theorem commonLabel_norm_le (Y : ℝ)
    (hN : ∀ i ∈ d.columns, (Ideal.absNorm (d.ideal i).val : ℝ) ≤ Y)
    (j : s.CoveredLeafKey B) :
    (Ideal.absNorm (s.commonLabel B j).1 : ℝ) ≤ Y ∧
      (Ideal.absNorm (s.commonLabel B j).2 : ℝ) ≤ Y := by
  have hres (p : ExteriorPrime A) (n : ℕ) (i : d.valuationColumns p n) :
      (Ideal.absNorm ((d.residualSource p n c).ideal i).val : ℝ) ≤ Y :=
    (d.residualSource_ideal_norm_le p n c i).trans (hN i.val (Finset.mem_filter.mp i.property).1)
  let goal : s.CoveredLeafKey B → Prop := fun key =>
    (Ideal.absNorm (s.commonLabel B key).1 : ℝ) ≤ Y ∧
      (Ideal.absNorm (s.commonLabel B key).2 : ℝ) ≤ Y
  exact Sum.rec (motive := goal)
    (fun a => actual_common_pair_norm _ _ _ _ Y
      (fun i _ => (d.ideal i).property.1) (fun i _ => (d.ideal i).property.1) hN hN a.1.1)
    (fun tail => Sum.rec (motive := fun tail => goal (.inr tail))
      (fun a => actual_common_pair_norm _ _ _ _ Y
        (fun i _ => ((d.residualSource a.1.val 1 c).ideal i).property.1)
        (fun i _ => ((d.residualSource a.1.val 1 c).ideal i).property.1)
        (fun i _ => hres a.1.val 1 i) (fun i _ => hres a.1.val 1 i) a.2.1.1)
      (fun tail => Sum.rec (motive := fun tail => goal (.inr (.inr tail)))
        (fun a => actual_common_pair_norm _ _ _ _ Y
          (fun i _ => ((d.residualSource a.1.val 6 c).ideal i).property.1)
          (fun i _ => ((d.residualSource a.1.val 6 c).ideal i).property.1)
          (fun i _ => hres a.1.val 6 i) (fun i _ => hres a.1.val 6 i) a.2.1.1)
        (fun a => actual_common_pair_norm _ _ _ _ Y
          (fun i _ => ((d.residualSource a.1.val 7 c).ideal i).property.1)
          (fun i _ => ((d.residualSource a.1.val 7 c).ideal i).property.1)
          (fun i _ => hres a.1.val 7 i) (fun i _ => hres a.1.val 7 i) a.2.1.1) tail) tail) j

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS ActualLeafNormWindows pool_commonLabel_norm_le_done__innerDivisor_norm_le_before"
  log.flush

theorem innerDivisor_norm_le (Y : ℝ)
    (hN : ∀ i ∈ d.columns, (Ideal.absNorm (d.ideal i).val : ℝ) ≤ Y)
    (j : s.CoveredLeafKey B) : (Ideal.absNorm (s.innerDivisor B j) : ℝ) ≤ Y := by
  have hres (p : ExteriorPrime A) (n : ℕ) (i : d.valuationColumns p n) :
      (Ideal.absNorm ((d.residualSource p n c).ideal i).val : ℝ) ≤ Y :=
    (d.residualSource_ideal_norm_le p n c i).trans (hN i.val (Finset.mem_filter.mp i.property).1)
  let goal : s.CoveredLeafKey B → Prop := fun key =>
    (Ideal.absNorm (s.innerDivisor B key) : ℝ) ≤ Y
  exact Sum.rec (motive := goal)
    (fun a => s.main.covered_innerDivisor_norm_le B.main B.main Y hN a)
    (fun tail => Sum.rec (motive := fun tail => goal (.inr tail))
      (fun a => (s.one a.1).covered_innerDivisor_norm_le
        (B.residual a.1 1) (B.residual a.1 1) Y (fun i _ => hres a.1.val 1 i) a.2)
      (fun tail => Sum.rec (motive := fun tail => goal (.inr (.inr tail)))
        (fun a => (s.six a.1).covered_innerDivisor_norm_le
          (B.residual a.1 6) (B.residual a.1 6) Y (fun i _ => hres a.1.val 6 i) a.2)
        (fun a => (s.seven a.1).covered_innerDivisor_norm_le
          (B.residual a.1 7) (B.residual a.1 7) Y (fun i _ => hres a.1.val 7 i) a.2) tail) tail) j

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS ActualLeafNormWindows pool_innerDivisor_norm_le_done"
  log.flush

end ActualPoolStages

namespace FirstBlockPoolData

variable {κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable (p : FirstBlockPoolData chart P M X hX)

theorem left_ideal_norm_le (Y : ℝ)
    (hN : ∀ i ∈ left, (Ideal.absNorm (fullI i).val : ℝ) ≤ Y)
    (i : ι) (hi : i ∈ p.leftData.columns) : (Ideal.absNorm (p.leftData.ideal i).val : ℝ) ≤ Y := by
  rw [p.left_columns] at hi
  rw [p.left_ideal, b.left_residual]
  exact (actual_supportResidual_norm_le _ (fullI i).property.1 _).trans
    (hN i (Finset.mem_filter.mp hi).1)

theorem right_ideal_norm_le (Y : ℝ)
    (hN : ∀ i ∈ right, (Ideal.absNorm (fullJ i).val : ℝ) ≤ Y)
    (i : κ) (hi : i ∈ p.rightData.columns) : (Ideal.absNorm (p.rightData.ideal i).val : ℝ) ≤ Y := by
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

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS ActualLeafNormWindows block_commonLabel_properties_before"
  log.flush

theorem commonLabel_properties (j : R.CoveredLeafKey LA RA) :
    (R.commonLabel LA RA j).1 ≠ 0 ∧ (R.commonLabel LA RA j).2 ≠ 0 ∧
      primeSupport (R.commonLabel LA RA j).1 = primeSupport (R.commonLabel LA RA j).2 := by
  exact Sum.rec
    (motive := fun side =>
      (R.commonLabel LA RA ⟨j.1, j.2.1, side⟩).1 ≠ 0 ∧
        (R.commonLabel LA RA ⟨j.1, j.2.1, side⟩).2 ≠ 0 ∧
        primeSupport (R.commonLabel LA RA ⟨j.1, j.2.1, side⟩).1 =
          primeSupport (R.commonLabel LA RA ⟨j.1, j.2.1, side⟩).2)
    (fun a => (R.left j.1 j.2.1).commonLabel_properties _ a)
    (fun a => (R.right j.1 j.2.1).commonLabel_properties _ a) j.2.2

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS ActualLeafNormWindows block_commonLabel_properties_done__commonLabel_norm_le_before"
  log.flush

theorem commonLabel_norm_le (Y : ℝ)
    (hL : ∀ i ∈ left, (Ideal.absNorm (fullI i).val : ℝ) ≤ Y)
    (hR : ∀ i ∈ right, (Ideal.absNorm (fullJ i).val : ℝ) ≤ Y)
    (j : R.CoveredLeafKey LA RA) :
    (Ideal.absNorm (R.commonLabel LA RA j).1 : ℝ) ≤ Y ∧
      (Ideal.absNorm (R.commonLabel LA RA j).2 : ℝ) ≤ Y := by
  exact Sum.rec
    (motive := fun side =>
      (Ideal.absNorm (R.commonLabel LA RA ⟨j.1, j.2.1, side⟩).1 : ℝ) ≤ Y ∧
        (Ideal.absNorm (R.commonLabel LA RA ⟨j.1, j.2.1, side⟩).2 : ℝ) ≤ Y)
    (fun a => (R.left j.1 j.2.1).commonLabel_norm_le _ Y
      (by simpa only [p.divisorPools.left_columns j.1, p.divisorPools.left_ideal j.1] using
        p.left_ideal_norm_le Y hL) a)
    (fun a => (R.right j.1 j.2.1).commonLabel_norm_le _ Y
      (by simpa only [p.divisorPools.right_columns j.1, p.divisorPools.right_ideal j.1] using
        p.right_ideal_norm_le Y hR) a) j.2.2

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS ActualLeafNormWindows block_commonLabel_norm_le_done__innerDivisor_norm_le_before"
  log.flush

theorem innerDivisor_norm_le (Y : ℝ)
    (hL : ∀ i ∈ left, (Ideal.absNorm (fullI i).val : ℝ) ≤ Y)
    (hR : ∀ i ∈ right, (Ideal.absNorm (fullJ i).val : ℝ) ≤ Y)
    (j : R.CoveredLeafKey LA RA) :
    (Ideal.absNorm (R.innerDivisor LA RA j) : ℝ) ≤ Y := by
  exact Sum.rec
    (motive := fun side =>
      (Ideal.absNorm (R.innerDivisor LA RA ⟨j.1, j.2.1, side⟩) : ℝ) ≤ Y)
    (fun a => (R.left j.1 j.2.1).innerDivisor_norm_le _ Y
      (by simpa only [p.divisorPools.left_columns j.1, p.divisorPools.left_ideal j.1] using
        p.left_ideal_norm_le Y hL) a)
    (fun a => (R.right j.1 j.2.1).innerDivisor_norm_le _ Y
      (by simpa only [p.divisorPools.right_columns j.1, p.divisorPools.right_ideal j.1] using
        p.right_ideal_norm_le Y hR) a) j.2.2

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS ActualLeafNormWindows block_innerDivisor_norm_le_done"
  log.flush

end SecondStages
end FirstBlockPoolData

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS ActualLeafNormWindows arithmeticLabels_admissible_before"
  log.flush

/-- The actual retained carrier is admissible from original column
windows and the original old-mask divisibility alone. All transformed
support and norm statements are derived above or from genuine liveness. -/
theorem arithmeticLabels_admissible {cap : ℕ} (hcap : L.slotCount ≤ cap)
    (exceptional : R.supported.gated.CoverHybridPredicates L) (N : s.Normalization)
    (B : ℝ) (oldMask : Ideal (𝓞 K)) (hs : Squarefree oldMask)
    (hmask : ∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val)
    (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B) :
    (R.supported.gated.arithmeticLabels L hcap exceptional N).carrier.Admissible
      (cap + 2) B Z oldMask := by
  refine OriginalArithmeticLabels.carrier_admissible
    (R.supported.gated.arithmeticLabels L hcap exceptional N) B Z oldMask
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    have hp := actual_common_pair_properties _ _ _ _ j.val.1
    have hdiv : oldMask ∣ j.val.1.val.1 ∧ oldMask ∣ j.val.1.val.2 := by
      refine (Finset.mem_image.mp j.val.1.property).elim ?_
      intro ij hijhe
      have hi := (Finset.mem_product.mp hijhe.1).1
      have hj := (Finset.mem_product.mp hijhe.1).2
      have hd := actual_common_label_old_mask oldMask (s.ideal ij.1).val (s.ideal ij.2).val
        hs (s.ideal ij.1).property.1 (s.ideal ij.2).property.1 (hmask ij.1 hi) (hmask ij.2 hj)
      simpa only [hijhe.2] using hd
    exact ⟨hp.1, hp.2.1, hp.2.2, hdiv.1, hdiv.2, Finset.empty_subset _⟩
  · intro j
    exact actual_common_pair_norm _ _ _ _ (Z ^ B)
      (fun i _ => (s.ideal i).property.1) (fun i _ => (s.ideal i).property.1) hN hN j.val.1
  · intro j
    have hS := (R.live_common_old_mask L exceptional N j).1
    exact ⟨hS, hS.ne_zero⟩
  · intro j
    exact (s.pools j.val.1 j.val.2.1).firstDivisor_norm_le (Z ^ B) hN j.val.2.2.1
  · intro j
    have hp := (R.supported.gated j.val.1 j.val.2.1).commonLabel_properties L L j.val.2.2
    have hd := (R.live_common_old_mask L exceptional N j).2
    exact ⟨hp.1, hp.2.1, hp.2.2, hd.1, hd.2, Finset.empty_subset _⟩
  · intro j
    exact (R.supported.gated j.val.1 j.val.2.1).commonLabel_norm_le
      L L (Z ^ B) hN hN j.val.2.2
  · intro j
    rw [R.supported.gated.arithmeticLabels_secondDivisor]
    exact (R.live_inner_divisor_squarefree L exceptional N j).ne_zero
  · intro j
    rw [R.supported.gated.arithmeticLabels_secondDivisor]
    exact (R.supported.gated j.val.1 j.val.2.1).innerDivisor_norm_le
      L L (Z ^ B) hN hN j.val.2.2

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS ActualLeafNormWindows arithmeticLabels_admissible_done"
  log.flush

end ActualFirstSource.SecondStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.covered_innerDivisor_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.arithmeticLabels_admissible

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS ActualLeafNormWindows axioms_done"
  log.flush
