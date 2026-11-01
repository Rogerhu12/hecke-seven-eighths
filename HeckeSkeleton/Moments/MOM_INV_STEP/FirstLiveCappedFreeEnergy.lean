import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCappedFreeEnergy

/-!
# Live first sources at the actual physical row cap

The source is restricted before free row enlargement: an outer index is
retained precisely when its original old-label/frequency row set is
nonempty. Thus empty first frequency balls contribute exactly zero and
cannot create an artificial inverse energy. Every retained outer index
has an actual nonzero ideal row, which proves that its prescribed cap
is at least one. The cap is never replaced by max(1,cap).
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstLiveCappedFreeEnergy

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstColumnAssembly
  FirstParentRows FirstOuterCenters FirstMobiusGeometry FirstPositiveSource
  FirstCenteredPositiveEnergy FirstCenteredMellinEnergy FirstCommonEnvelope
  FirstParentFiber FirstFreeMellinEnergy FirstBranchIntegration InverseRowMajorant CommonKernel
  FirstLocalizedFreeEnergy
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ ι : Type*} [Fintype ι]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (H : OuterIndex K S D T → {r : ℝ // 0 < r})
  (L : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))))
  (w : ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))) → ℝ)
variable (grid : ι → {r : ℝ // 0 < r}) (centers : FirstOuterCenters.Centering K S D T grid)
variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
variable (m : ℕ) (side : Bool)

def alive (o : OuterIndex K S D T) : Prop :=
  (sourceRows K S D Γ L (H o).val).Nonempty

/-- Liveness is the actual old-label nonemptiness and the genuine bare
frequency norm threshold. All original sectors remain present. -/
theorem alive_iff (o : OuterIndex K S D T) :
    alive K S D Γ T H L o ↔ L.Nonempty ∧ 1 ≤ (H o).val := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨hf,hz⟩ := Finset.mem_product.mp hx
    exact ⟨⟨x.1,hf⟩,(height_one_le K Sset x.2.1).trans
      ((FirstDualTruncation.mem_sectorCutoff K S D Γ (H o).val x.2).mp hz)⟩
  · rintro ⟨⟨f,hf⟩,hH⟩
    refine ⟨(f,(FirstInversePoisson.unitIdeal K S,1)), Finset.mem_product.mpr ⟨hf,?_⟩⟩
    apply (FirstDualTruncation.mem_sectorCutoff K S D Γ (H o).val _).mpr
    simpa only [FirstInversePoisson.unitIdeal_val, map_one, Nat.cast_one] using hH

abbrev Index := Σ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o

def liveIndices : Finset (Index K S D T) :=
  Finset.univ.filter (fun i => alive K S D Γ T H L i.1)

theorem mem_liveIndices (i : Index K S D T) :
    i ∈ liveIndices K S D Γ T H L ↔ alive K S D Γ T H L i.1 := by
  simp only [liveIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem alive_cap_one (F : {r : ℝ // 0 < r})
    (R : OuterIndex K S D T → {r : ℝ // 0 < r})
    (hL : ∀ f ∈ L, height K Sset f ≤ F.val)
    (hcap : ∀ o, (rowCap K S (cubeDilation K S (outerAnchor K S D T o).1
      (outerAnchor K S D T o).2 o.1.val o.2.1.val) F (H o)).val ≤ (R o).val)
    (o : OuterIndex K S D T) (ho : alive K S D Γ T H L o) : 1 ≤ (R o).val := by
  obtain ⟨x,hx⟩ := ho
  let E := cubeDilation K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
    o.1.val o.2.1.val
  have hy : FirstRowGeometry.row K S Γ E x ∈
      (sourceRows K S D Γ L (H o).val).image (FirstRowGeometry.row K S Γ E) :=
    Finset.mem_image.mpr ⟨x,hx,rfl⟩
  exact (height_one_le K Sset (FirstRowGeometry.row K S Γ E x).1).trans
    ((sourceRows_row_bound K S D Γ L E F (H o) hL _ hy).trans (hcap o))

theorem alive_exponent_nonneg (F : {r : ℝ // 0 < r})
    (R : OuterIndex K S D T → {r : ℝ // 0 < r})
    (hL : ∀ f ∈ L, height K Sset f ≤ F.val)
    (hcap : ∀ o, (rowCap K S (cubeDilation K S (outerAnchor K S D T o).1
      (outerAnchor K S D T o).2 o.1.val o.2.1.val) F (H o)).val ≤ (R o).val)
    (o : OuterIndex K S D T) (ho : alive K S D Γ T H L o)
    (Z M : ℝ) (hZ : 1 < Z) (hR : (R o).val = Z ^ M) : 0 ≤ M := by
  have h := alive_cap_one K S D Γ T H L F R hL hcap o ho
  rw [hR, ← Real.rpow_zero Z] at h
  exact (Real.rpow_le_rpow_left_iff hZ).mp h

def freeRowIntegral (R : OuterIndex K S D T → {r : ℝ // 0 < r}) (massEps : ℝ)
    (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o)
    (k : ι) (J : Finset σ) : ℝ :=
  let radius := R o
  (radius.val ^ massEps * (rowCovolume K S)⁻¹) *
    ∫ η : LogPlane, frequencyEnvelope m η *
      freeMellinEnergy K S Γ D T.columns Θ ψ G hν hG J (centerScale T.scale (grid k)).val
        (-(1 / 2 : ℝ))
        (firstTriple K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val
          (overlapIdeal K S D T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
            o.1.val o.2.1.val false e))
        (retainedLabel K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
          o.1.val o.2.1.val).val.val (FirstLocalizedEnergy.divisor K S D T o).val W hW
        radius (signedCoordinate side η)

theorem freeRowIntegral_eq_capped
    (R : OuterIndex K S D T → {r : ℝ // 0 < r}) (massEps : ℝ)
    (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o)
    (k : ι) (J : Finset σ) :
    freeRowIntegral K S D Γ T Θ ψ G hν hG grid W hW m side R massEps o e k J =
      FirstCappedFreeEnergy.freeRowIntegral K S D Γ T Θ ψ G hν hG
        grid W hW m side R massEps o e k J := rfl

def freeTotal (R : OuterIndex K S D T → {r : ℝ // 0 < r}) (massEps ε : ℝ) : ℝ :=
  ∑ o : OuterIndex K S D T, if alive K S D Γ T H L o then
    (FirstLocalizedEnergy.maskWeight K S D T o * FirstLocalizedEnergy.radialScale K S D T o ^ ε) *
      ∑ k : ι, ∑ e : FirstOuterCenters.Overlap K S D T o,
        if centers.assignment side o e = k then
          ∑ J ∈ T.columns.slots.powerset,
            branchCoefficient K S D T grid centers W hW side o e k J *
              freeRowIntegral K S D Γ T Θ ψ G hν hG grid W hW m side R massEps o e k J
        else 0
    else 0


theorem freeRowIntegral_nonneg
    (R : OuterIndex K S D T → {r : ℝ // 0 < r}) (massEps : ℝ)
    (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o)
    (k : ι) (J : Finset σ) :
    0 ≤ freeRowIntegral K S D Γ T Θ ψ G hν hG grid W hW m side R massEps o e k J := by
  apply mul_nonneg
  · exact mul_nonneg (Real.rpow_nonneg (R o).property.le _)
      (inv_nonneg.mpr (rowCovolume_pos K S).le)
  · apply integral_nonneg
    intro ξ
    exact mul_nonneg (frequencyEnvelope_nonneg m ξ)
      (freeMellinEnergy_nonneg K S Γ D T.columns Θ ψ G hν hG J
        (centerScale T.scale (grid k)).val (-(1 / 2 : ℝ))
        (firstTriple K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
          o.1.val o.2.1.val
          (overlapIdeal K S D T.scale (outerAnchor K S D T o).1
            (outerAnchor K S D T o).2 o.1.val o.2.1.val false e))
        (retainedLabel K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
          o.1.val o.2.1.val).val.val (FirstLocalizedEnergy.divisor K S D T o).val
        W hW (R o) (signedCoordinate side ξ))

theorem freeTotal_nonneg
    (R : OuterIndex K S D T → {r : ℝ // 0 < r}) (massEps ε : ℝ) :
    0 ≤ freeTotal K S D Γ T Θ ψ G hν hG H L grid centers W hW m side R massEps ε := by
  apply Finset.sum_nonneg
  intro o ho
  split_ifs
  · apply mul_nonneg
    · exact mul_nonneg (FirstLocalizedEnergy.maskWeight_nonneg K S D T o)
        (Real.rpow_nonneg (FirstLocalizedEnergy.radialScale_pos K S D T o).le _)
    · apply Finset.sum_nonneg
      intro k hk
      apply Finset.sum_nonneg
      intro e he
      split_ifs
      · apply Finset.sum_nonneg
        intro J hJ
        exact mul_nonneg
          (branchCoefficient_nonneg K S D T grid centers W hW side o e k J)
          (freeRowIntegral_nonneg K S D Γ T Θ ψ G hν hG grid W hW m side
            R massEps o e k J)
      · exact le_rfl
  · exact le_rfl

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hallowed hΓ in
/-- All the old label and frequency rows in the complete first positive
source are removed at once. The original weight assumptions are the
literal divisor bounds; the source and energy transformations are proved. -/
theorem exists_centeredTotal_free_bound (a p : ℕ) (massEps : ℝ) (hmassEps : 0 < massEps) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {σ₀ ι₀ : Type*} [Fintype ι₀], ∀ (T : FirstParentEnergy.Data K S (σ := σ₀))
        (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
        (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
        (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (L : Finset Ext) (w : Ext → ℝ)
        (grid : ι₀ → {r : ℝ // 0 < r}) (centers : FirstOuterCenters.Centering K S D T grid)
        (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
        (F : {r : ℝ // 0 < r}) (R : OuterIndex K S D T → {r : ℝ // 0 < r})
        (A : ℝ), 0 ≤ A →
        (∀ f ∈ L, height K Sset f ≤ F.val) →
        (∀ o, (rowCap K S (cubeDilation K S (outerAnchor K S D T o).1
          (outerAnchor K S D T o).2 o.1.val o.2.1.val) F (H o)).val ≤ (R o).val) →
        (∀ f ∈ L, w f ≤ A * ((idealDivisors f.val.val).card : ℝ) ^ a) →
        (∀ b ∈ T.cubes, ∀ f ∈ L,
          ‖T.columns.labelWeight b f‖ ≤ ((idealDivisors f.val.val).card : ℝ) ^ p) →
        ∀ (ε : ℝ) (m : ℕ) (side : Bool),
          FirstLocalizedEnergy.centeredTotal K S D Γ T Θ ψ G hν hG H L w
            grid centers W hW ε m side ≤
          (A * B) * freeTotal K S D Γ T Θ ψ G hν hG H L grid centers W hW m side R massEps ε := by
  obtain ⟨B, hB, hb⟩ := exists_uniform_sourceFourierEnergy_bound K S Γ D hallowed hΓ
    (a + 2 * p) massEps hmassEps
  refine ⟨B, hB, ?_⟩
  intro σ₀ ι₀ _ T Θ ψ G hν hG H L w grid centers W hW F R A hA hL hcap hw hβ ε m side
  rw [centeredTotal_eq_rowTotal K S D Γ T Θ ψ G hν hG H L w grid centers W hW m side hΓ]
  unfold rowTotal freeTotal
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o ho
  by_cases halive : alive K S D Γ T H L o
  · simp only [if_pos halive]
    have houter : 0 ≤ FirstLocalizedEnergy.maskWeight K S D T o *
        FirstLocalizedEnergy.radialScale K S D T o ^ ε :=
      mul_nonneg (FirstLocalizedEnergy.maskWeight_nonneg K S D T o)
        (Real.rpow_nonneg (FirstLocalizedEnergy.radialScale_pos K S D T o).le ε)
    have hinner :
        (∑ k : ι₀, ∑ e : FirstOuterCenters.Overlap K S D T o,
          if centers.assignment side o e = k then
            ∑ J ∈ T.columns.slots.powerset,
              branchCoefficient K S D T grid centers W hW side o e k J *
                rowIntegral K S D Γ T Θ ψ G hν hG H L w grid W hW m side o e k J
          else 0) ≤
        (A * B) * ∑ k : ι₀, ∑ e : FirstOuterCenters.Overlap K S D T o,
          if centers.assignment side o e = k then
            ∑ J ∈ T.columns.slots.powerset,
              branchCoefficient K S D T grid centers W hW side o e k J *
                freeRowIntegral K S D Γ T Θ ψ G hν hG grid W hW m side R massEps o e k J
          else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e he
      by_cases ha : centers.assignment side o e = k
      · simp only [ha, if_true, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro J hJ
        let E := cubeDilation K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
          o.1.val o.2.1.val
        have hr := hb T.columns Θ ψ G hν hG J (centerScale T.scale (grid k)).val
          (-(1 / 2 : ℝ))
          (firstTriple K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val
            (overlapIdeal K S D T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
              o.1.val o.2.1.val false e))
          (retainedLabel K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
            o.1.val o.2.1.val).val.val (FirstLocalizedEnergy.divisor K S D T o).val W hW
          E (sourceRows K S D Γ L (H o).val) (pairWeight K S T.columns o.1.val o.2.1.val w)
          A hA (by
            intro x hx
            have hxf := (Finset.mem_product.mp hx).1
            exact pairWeight_bound K S T.columns o.1.val o.2.1.val L w a p A hA hw
              (hβ o.1.val o.1.property) (hβ o.2.1.val o.2.1.property) x.1 hxf)
          (R o) (by
            intro y hy
            exact (sourceRows_row_bound K S D Γ L E F (H o) hL y hy).trans (hcap o))
          m (signedCoordinate side) (signedCoordinate_continuous side)
        have hr' : rowIntegral K S D Γ T Θ ψ G hν hG H L w grid W hW m side o e k J ≤
            (A * B) * freeRowIntegral K S D Γ T Θ ψ G hν hG grid W hW m side R massEps o e k J :=
          hr.trans_eq (by dsimp only [freeRowIntegral, E]; ring)
        exact (mul_le_mul_of_nonneg_left hr'
          (branchCoefficient_nonneg K S D T grid centers W hW side o e k J)).trans_eq (by ring)
      · simp only [ha, if_false, mul_zero, le_refl]
    exact (mul_le_mul_of_nonneg_left hinner houter).trans_eq (by ring)
  · have hempty : sourceRows K S D Γ L (H o).val = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp halive
    simp only [if_neg halive, mul_zero]
    simp [FirstLocalizedFreeEnergy.rowIntegral, FirstParentFiber.sourceMellinEnergy, hempty]

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

include hallowed hΓ in
theorem exists_rawTotal_free_bound
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (a p : ℕ) (ε massEps : ℝ) (hε : 0 < ε) (hmassEps : 0 < massEps) (m : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ {σ ι : Type*} [Fintype ι], ∀ (T : FirstParentEnergy.Data K S (σ := σ)),
      T.localTest = h →
      ∀ (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
        (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
        (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (L : Finset Ext) (w : Ext → ℝ)
        (grid : ι → {r : ℝ // 0 < r}) (centers : FirstOuterCenters.Centering K S D T grid)
        (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
        (F : {r : ℝ // 0 < r}) (R : OuterIndex K S D T → {r : ℝ // 0 < r})
        (Aweight : ℝ), 0 ≤ Aweight →
      (∀ f ∈ L, 0 ≤ w f) →
      (∀ f ∈ L, height K Sset f ≤ F.val) →
      (∀ o, (rowCap K S (cubeDilation K S (outerAnchor K S D T o).1
        (outerAnchor K S D T o).2 o.1.val o.2.1.val) F (H o)).val ≤ (R o).val) →
      (∀ f ∈ L, w f ≤ Aweight * ((idealDivisors f.val.val).card : ℝ) ^ a) →
      (∀ b ∈ T.cubes, ∀ f ∈ L,
        ‖T.columns.labelWeight b f‖ ≤ ((idealDivisors f.val.val).card : ℝ) ^ p) →
      (∀ q : HeightOneSpectrum (𝓞 K), q ∉ Sset → UnramifiedAt K G q) →
      T.columns.base ^ T.columns.length = T.scale.val → 1 < T.columns.base →
      T.columns.cutoff = W →
      (∀ k ∈ T.columns.slots, ∀ q ∈ T.columns.primeLists k, Prime q) →
      ∀ side : Bool,
        FirstLocalizedEnergy.rawTotal K S D Γ μv ν G T H L w side ≤
          (C * s.sup (schwartzSeminormFamily ℝ V ℂ) T.archTest * Aweight) *
            freeTotal K S D Γ T Θ ψ G hν hG H L grid centers W hW m side R massEps ε := by
  obtain ⟨s, A, hA, hsource⟩ := FirstLocalizedEnergy.exists_centeredTotal_bound K S D Γ μv ν hallowed hΓ
    h hlc hcs ε hε m
  obtain ⟨B, hB, hfiber⟩ := exists_centeredTotal_free_bound K S D Γ hΓ hallowed
    a p massEps hmassEps
  refine ⟨s, A * B, mul_nonneg hA (zero_le_one.trans hB), ?_⟩
  intro σ ι _ T hlocal Θ ψ G hν hG H L w grid centers W hW F R Aweight hAweight
    hw0 hF hcap hw hβ hGunramified hscale hbase hcut hprime side
  have h₁ := hsource T hlocal Θ ψ G hν hG H L w hw0 grid centers W hW
    hGunramified hscale hbase hcut hprime side
  have h₂ := hfiber T Θ ψ G hν hG H L w grid centers W hW F R Aweight hAweight
    hF hcap hw hβ ε m side
  exact h₁.trans ((mul_le_mul_of_nonneg_left h₂
    (mul_nonneg hA (apply_nonneg _ _))).trans_eq (by ring))

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstLiveCappedFreeEnergy

end
