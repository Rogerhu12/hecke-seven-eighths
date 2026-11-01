import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportedGaussStages

/-!
# Live leaves retain genuine physical and arithmetic support

Every support assertion below is derived from a literal nonzero leaf.
The original source gates and the original eligible physical rows are
used before any positive Fourier estimate. In particular an error leaf
cannot acquire a prime which divides the old frozen divisor.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory
open HeckeGeneral.Analysis.ConditionalMoments

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.MobiusRegroup

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
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

namespace ActualHybridLeaf

variable {H : Type*} (B : ActualHybridLeaf K H W E)

theorem live_of_scale_live (a : ℝ) (ha : 0 ≤ a) (h : (B.scale a ha).Live) : B.Live := by
  exact ⟨(mul_ne_zero_iff.mp h.1).2, h.2⟩

end ActualHybridLeaf

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)

theorem coveredLeaf_weight_nonzero_inner_squarefree
    (LC RC : SourceCartesianCover G.columns G.ideal)
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (j : s.CoveredLeafKey LC RC)
    (hj : (s.coveredLeaf LC RC exceptional F x j).weight ≠ 0) :
    Squarefree j.2.1.val := by
  by_contra hn
  apply hj
  change ‖(moebius j.2.1.val : ℂ)‖ * _ = 0
  simp only [moebius_of_not_squarefree hn, Int.cast_zero, norm_zero, zero_mul]

/-- These are the original physical rows, not the dual row set of a
profile chart. Their nonemptiness comes from the actual orbital fibre
coefficient in this very leaf. -/
theorem supported_gated_fiberLeaf_live
    (LC RC : SourceCartesianCover G.columns G.ideal)
    (exceptional : s.supported.gated.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W)
    (j : s.supported.gated.CoveredLeafKey LC RC)
    (hj : (s.supported.gated.fiberCoveredLeaf LC RC exceptional F x j).Live) :
    G.rows.Nonempty ∧ j.1.1.val ∈ G.activeCommon ∧ Squarefree j.2.1.val := by
  have hf : s.supported.fiber ≠ 0 := by
    intro hz
    apply hj.1
    change (s.supported.fiber : ℝ) * _ = 0
    rw [hz, Nat.cast_zero, zero_mul]
  have hbare : (s.supported.gated.coveredLeaf LC RC exceptional F x j).Live :=
    (s.supported.gated.coveredLeaf LC RC exceptional F x j).live_of_scale_live
      _ _ hj
  obtain ⟨h, hh, i, hi, hci⟩ := hbare.2.1
  exact ⟨s.supported_fiber_nonzero_rows hf,
    s.supported_gated_leaf_active LC RC exceptional F x j h i hci,
    s.supported.gated.coveredLeaf_weight_nonzero_inner_squarefree
      LC RC exceptional F x j hbare.1⟩

end ActualGaussStage

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}

namespace ActualPoolStages

variable (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)
variable (B : d.SourceCovers c)

/-- Literal arithmetic projections from the actual four-tag carrier. -/
def commonLabel : s.CoveredLeafKey B → Ideal (𝓞 K) × Ideal (𝓞 K)
  | .inl j => j.1.1.val
  | .inr (.inl ⟨_, j⟩) => j.1.1.val
  | .inr (.inr (.inl ⟨_, j⟩)) => j.1.1.val
  | .inr (.inr (.inr ⟨_, j⟩)) => j.1.1.val

def innerDivisor : s.CoveredLeafKey B → Ideal (𝓞 K)
  | .inl j => j.2.1.val
  | .inr (.inl ⟨_, j⟩) => j.2.1.val
  | .inr (.inr (.inl ⟨_, j⟩)) => j.2.1.val
  | .inr (.inr (.inr ⟨_, j⟩)) => j.2.1.val

def physicalRows : s.CoveredLeafKey B → Finset A.R
  | .inl _ => d.mainRows
  | .inr (.inl ⟨p, _⟩) => d.errorRows p.val
  | .inr (.inr (.inl ⟨p, _⟩)) => d.errorRows p.val
  | .inr (.inr (.inr ⟨p, _⟩)) => d.errorRows p.val

def sourceCommonLabels : s.CoveredLeafKey B → Finset (Ideal (𝓞 K) × Ideal (𝓞 K))
  | .inl _ => (d.mainSource c).activeCommon
  | .inr (.inl ⟨p, _⟩) => (d.residualSource p.val 1 c).activeCommon
  | .inr (.inr (.inl ⟨p, _⟩)) => (d.residualSource p.val 6 c).activeCommon
  | .inr (.inr (.inr ⟨p, _⟩)) => (d.residualSource p.val 7 c).activeCommon

def errorPrime : s.CoveredLeafKey B → Option (ExteriorPrime A)
  | .inl _ => none
  | .inr (.inl ⟨p, _⟩) => some p.val
  | .inr (.inr (.inl ⟨p, _⟩)) => some p.val
  | .inr (.inr (.inr ⟨p, _⟩)) => some p.val

theorem supported_gated_live_source
    (exceptional : s.supported.gated.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W)
    (j : s.supported.gated.CoveredLeafKey B)
    (hj : (s.supported.gated.coveredLeaf B exceptional F x j).Live) :
    (s.supported.gated.physicalRows B j).Nonempty ∧
      s.supported.gated.commonLabel B j ∈ s.supported.gated.sourceCommonLabels B j ∧
      Squarefree (s.supported.gated.innerDivisor B j) := by
  rcases j with j | (⟨p, j⟩ | (⟨p, j⟩ | ⟨p, j⟩))
  · exact s.main.supported_gated_fiberLeaf_live B.main B.main exceptional.main F x j
      ((s.main.supported.gated.fiberCoveredLeaf B.main B.main exceptional.main F x j).live_of_scale_live _ _ hj)
  · exact (s.one p).supported_gated_fiberLeaf_live
      (B.residual p 1) (B.residual p 1) (exceptional.one p) F (fun i => x i.val) j
      (((s.one p).supported.gated.fiberCoveredLeaf
        (B.residual p 1) (B.residual p 1) (exceptional.one p) F (fun i => x i.val) j).live_of_scale_live _ _ hj)
  · exact (s.six p).supported_gated_fiberLeaf_live
      (B.residual p 6) (B.residual p 6) (exceptional.six p) F (fun i => x i.val) j
      (((s.six p).supported.gated.fiberCoveredLeaf
        (B.residual p 6) (B.residual p 6) (exceptional.six p) F (fun i => x i.val) j).live_of_scale_live _ _ hj)
  · exact (s.seven p).supported_gated_fiberLeaf_live
      (B.residual p 7) (B.residual p 7) (exceptional.seven p) F (fun i => x i.val) j
      (((s.seven p).supported.gated.fiberCoveredLeaf
        (B.residual p 7) (B.residual p 7) (exceptional.seven p) F (fun i => x i.val) j).live_of_scale_live _ _ hj)

/-- The support of the original whole coefficient, combined with the
actual eligible rows, transports the old squarefree divisor through
the genuine prime-power quotient on every error branch. -/
theorem supported_gated_live_old_mask
    (S : Ideal (𝓞 K)) (hS : Squarefree S) (hfrozen : S ∣ d.frozen)
    (hc : ∀ i ∈ d.columns, c i ≠ 0 → S ∣ (d.ideal i).val)
    (exceptional : s.supported.gated.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W)
    (j : s.supported.gated.CoveredLeafKey B)
    (hj : (s.supported.gated.coveredLeaf B exceptional F x j).Live) :
    S ∣ (s.supported.gated.commonLabel B j).1 ∧
      S ∣ (s.supported.gated.commonLabel B j).2 := by
  have hs := s.supported_gated_live_source B exceptional F x j hj
  rcases j with j | (⟨p, j⟩ | (⟨p, j⟩ | ⟨p, j⟩))
  · exact (d.mainSource c).activeCommon_old_mask S hS hc _ hs.2.1
  · exact (d.residualSource p.val 1 c).activeCommon_old_mask S hS
      (fun i _ hi => d.residualSource_nonzero_dvd p.val 1 c S hfrozen hc hs.1 i hi)
      _ hs.2.1
  · exact (d.residualSource p.val 6 c).activeCommon_old_mask S hS
      (fun i _ hi => d.residualSource_nonzero_dvd p.val 6 c S hfrozen hc hs.1 i hi)
      _ hs.2.1
  · exact (d.residualSource p.val 7 c).activeCommon_old_mask S hS
      (fun i _ hi => d.residualSource_nonzero_dvd p.val 7 c S hfrozen hc hs.1 i hi)
      _ hs.2.1

theorem supported_gated_live_errorPrime
    (exceptional : s.supported.gated.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W)
    (j : s.supported.gated.CoveredLeafKey B)
    (hj : (s.supported.gated.coveredLeaf B exceptional F x j).Live)
    (p : ExteriorPrime A) (hp : s.supported.gated.errorPrime B j = some p) :
    ¬p.val.asIdeal ∣ d.frozen := by
  have hs := s.supported_gated_live_source B exceptional F x j hj
  rcases j with j | (⟨p', j⟩ | (⟨p', j⟩ | ⟨p', j⟩))
  · cases hp
  · have he : p'.val = p := Option.some.inj hp
    subst p
    exact d.errorRows_nonempty_not_dvd_frozen p'.val hs.1
  · have he : p'.val = p := Option.some.inj hp
    subst p
    exact d.errorRows_nonempty_not_dvd_frozen p'.val hs.1
  · have he : p'.val = p := Option.some.inj hp
    subst p
    exact d.errorRows_nonempty_not_dvd_frozen p'.val hs.1

end ActualPoolStages

namespace FirstBlockPoolData

variable {κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable (p : FirstBlockPoolData chart P M X hX)

theorem leftDivisorCoefficient_nonzero_dvd
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (i : ι)
    (hi : p.leftDivisorCoefficient S χ i ≠ 0) :
    S.val ∣ ((p.divisorPools.leftData S).ideal i).val := by
  rw [p.divisorPools.left_ideal S]
  by_contra hn
  exact hi (by simp only [leftDivisorCoefficient, if_neg hn])

theorem rightDivisorCoefficient_nonzero_dvd
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (i : κ)
    (hi : p.rightDivisorCoefficient S χ i ≠ 0) :
    S.val ∣ ((p.divisorPools.rightData S).ideal i).val := by
  rw [p.divisorPools.right_ideal S]
  by_contra hn
  exact hi (by simp only [rightDivisorCoefficient, if_neg hn])

theorem firstDivisor_dvd_left_frozen
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) :
    S.val ∣ (p.divisorPools.leftData S).frozen := by
  rw [p.divisorPools.left_frozen S]
  exact ⟨p.leftData.frozen, mul_comm _ _⟩

theorem firstDivisor_dvd_right_frozen
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) :
    S.val ∣ (p.divisorPools.rightData S).frozen := by
  rw [p.divisorPools.right_frozen S]
  exact ⟨p.rightData.frozen, mul_comm _ _⟩

namespace SecondStages

variable {p}
variable (s : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

def commonLabel (j : s.CoveredLeafKey LA RA) : Ideal (𝓞 K) × Ideal (𝓞 K) :=
  match j.2.2 with
  | .inl a => (s.left j.1 j.2.1).commonLabel (p.leftSourceCovers LA j.1 j.2.1) a
  | .inr a => (s.right j.1 j.2.1).commonLabel (p.rightSourceCovers RA j.1 j.2.1) a

def innerDivisor (j : s.CoveredLeafKey LA RA) : Ideal (𝓞 K) :=
  match j.2.2 with
  | .inl a => (s.left j.1 j.2.1).innerDivisor (p.leftSourceCovers LA j.1 j.2.1) a
  | .inr a => (s.right j.1 j.2.1).innerDivisor (p.rightSourceCovers RA j.1 j.2.1) a

def errorPrime (j : s.CoveredLeafKey LA RA) : Option (ExteriorPrime A) :=
  match j.2.2 with
  | .inl a => (s.left j.1 j.2.1).errorPrime (p.leftSourceCovers LA j.1 j.2.1) a
  | .inr a => (s.right j.1 j.2.1).errorPrime (p.rightSourceCovers RA j.1 j.2.1) a

variable
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)

/-- No Valid condition on all second labels is needed: it follows on
the literal live support after the two original coefficient gates. -/
theorem supported_gated_live_old_mask
    (exceptional : s.supported.gated.CoverHybridPredicates LA RA)
    (j : s.supported.gated.CoveredLeafKey LA RA)
    (hj : (s.supported.gated.coveredLeaf LA RA NL NR hNL hNR exceptional j).Live) :
    Squarefree j.1.val ∧
      j.1.val ∣ (s.supported.gated.commonLabel LA RA j).1 ∧
      j.1.val ∣ (s.supported.gated.commonLabel LA RA j).2 := by
  have hS := s.supported.gated.coveredLeaf_weight_nonzero_squarefree
    LA RA NL NR hNL hNR exceptional j hj.1
  refine ⟨hS, ?_⟩
  rcases j with ⟨S, χ, j | j⟩
  · apply (s.left S χ).supported_gated_live_old_mask (p.leftSourceCovers LA S χ)
      S.val hS (p.firstDivisor_dvd_left_frozen S)
      (fun i _ hi => p.leftDivisorCoefficient_nonzero_dvd S χ i hi)
      (exceptional.left S χ) chart.kernel chart.leftPoint j
    exact ((s.left S χ).supported.gated.coveredLeaf
      (p.leftSourceCovers LA S χ) (exceptional.left S χ) chart.kernel chart.leftPoint j).live_of_scale_live _ _ hj
  · apply (s.right S χ).supported_gated_live_old_mask (p.rightSourceCovers RA S χ)
      S.val hS (p.firstDivisor_dvd_right_frozen S)
      (fun i _ hi => p.rightDivisorCoefficient_nonzero_dvd S χ i hi)
      (exceptional.right S χ) chart.kernel (fun i => -chart.rightPoint i) j
    exact ((s.right S χ).supported.gated.coveredLeaf
      (p.rightSourceCovers RA S χ) (exceptional.right S χ)
      chart.kernel (fun i => -chart.rightPoint i) j).live_of_scale_live _ _ hj

theorem supported_gated_live_errorPrime
    (exceptional : s.supported.gated.CoverHybridPredicates LA RA)
    (j : s.supported.gated.CoveredLeafKey LA RA)
    (hj : (s.supported.gated.coveredLeaf LA RA NL NR hNL hNR exceptional j).Live)
    (r : ExteriorPrime A) (hr : s.supported.gated.errorPrime LA RA j = some r) :
    ¬r.val.asIdeal ∣ j.1.val := by
  rcases j with ⟨S, χ, j | j⟩
  · have hlive := ((s.left S χ).supported.gated.coveredLeaf
      (p.leftSourceCovers LA S χ) (exceptional.left S χ) chart.kernel chart.leftPoint j).live_of_scale_live _ _ hj
    have hp := (s.left S χ).supported_gated_live_errorPrime (p.leftSourceCovers LA S χ)
      (exceptional.left S χ) chart.kernel chart.leftPoint j hlive r hr
    exact fun h => hp (h.trans (p.firstDivisor_dvd_left_frozen S))
  · have hlive := ((s.right S χ).supported.gated.coveredLeaf
      (p.rightSourceCovers RA S χ) (exceptional.right S χ)
      chart.kernel (fun i => -chart.rightPoint i) j).live_of_scale_live _ _ hj
    have hp := (s.right S χ).supported_gated_live_errorPrime (p.rightSourceCovers RA S χ)
      (exceptional.right S χ) chart.kernel (fun i => -chart.rightPoint i) j hlive r hr
    exact fun h => hp (h.trans (p.firstDivisor_dvd_right_frozen S))

theorem supported_gated_live_inner_squarefree
    (exceptional : s.supported.gated.CoverHybridPredicates LA RA)
    (j : s.supported.gated.CoveredLeafKey LA RA)
    (hj : (s.supported.gated.coveredLeaf LA RA NL NR hNL hNR exceptional j).Live) :
    Squarefree (s.supported.gated.innerDivisor LA RA j) := by
  rcases j with ⟨S, χ, j | j⟩
  · have hlive := ((s.left S χ).supported.gated.coveredLeaf
      (p.leftSourceCovers LA S χ) (exceptional.left S χ) chart.kernel chart.leftPoint j).live_of_scale_live _ _ hj
    exact ((s.left S χ).supported_gated_live_source (p.leftSourceCovers LA S χ)
      (exceptional.left S χ) chart.kernel chart.leftPoint j hlive).2.2
  · have hlive := ((s.right S χ).supported.gated.coveredLeaf
      (p.rightSourceCovers RA S χ) (exceptional.right S χ)
      chart.kernel (fun i => -chart.rightPoint i) j).live_of_scale_live _ _ hj
    exact ((s.right S χ).supported_gated_live_source (p.rightSourceCovers RA S χ)
      (exceptional.right S χ) chart.kernel (fun i => -chart.rightPoint i) j hlive).2.2

end SecondStages
end FirstBlockPoolData

variable {omega psi : HeckeCharacter K} {centered : Bool}
variable {dparent : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered dparent a t Y₁ Y₂ X hX}

namespace ActualFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

def commonLabel (j : R.CoveredLeafKey L) : Ideal (𝓞 K) × Ideal (𝓞 K) :=
  (R j.1 j.2.1).commonLabel L L j.2.2

def innerDivisor (j : R.CoveredLeafKey L) : Ideal (𝓞 K) :=
  (R j.1 j.2.1).innerDivisor L L j.2.2

def errorPrime (j : R.CoveredLeafKey L) : Option (ExteriorPrime A) :=
  (R j.1 j.2.1).errorPrime L L j.2.2

theorem live_common_old_mask
    (exceptional : R.supported.gated.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.supported.gated.liveLeaves L exceptional N) :
    Squarefree j.val.2.2.1.val ∧
      j.val.2.2.1.val ∣ (R.supported.gated.commonLabel L j.val).1 ∧
      j.val.2.2.1.val ∣ (R.supported.gated.commonLabel L j.val).2 := by
  have hlive := (R.supported.gated.coveredLeaf L exceptional N j.val).live_of_scale_live _ _ (R.supported.gated.liveLeaves_spec L exceptional N j)
  exact (R j.val.1 j.val.2.1).supported_gated_live_old_mask L L
    (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
    (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
    (exceptional j.val.1 j.val.2.1) j.val.2.2 hlive

theorem live_errorPrime_avoids_old_mask
    (exceptional : R.supported.gated.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.supported.gated.liveLeaves L exceptional N)
    (p : ExteriorPrime A) (hp : R.supported.gated.errorPrime L j.val = some p) :
    ¬p.val.asIdeal ∣ j.val.2.2.1.val := by
  have hlive := (R.supported.gated.coveredLeaf L exceptional N j.val).live_of_scale_live _ _ (R.supported.gated.liveLeaves_spec L exceptional N j)
  exact (R j.val.1 j.val.2.1).supported_gated_live_errorPrime L L
    (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
    (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
    (exceptional j.val.1 j.val.2.1) j.val.2.2 hlive p hp

theorem live_inner_divisor_squarefree
    (exceptional : R.supported.gated.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.supported.gated.liveLeaves L exceptional N) :
    Squarefree (R.supported.gated.innerDivisor L j.val) := by
  have hlive := (R.supported.gated.coveredLeaf L exceptional N j.val).live_of_scale_live _ _ (R.supported.gated.liveLeaves_spec L exceptional N j)
  exact (R j.val.1 j.val.2.1).supported_gated_live_inner_squarefree L L
    (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
    (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
    (exceptional j.val.1 j.val.2.1) j.val.2.2 hlive

end ActualFirstSource.SecondStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.supported_gated_fiberLeaf_live
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.live_common_old_mask
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.live_errorPrime_avoids_old_mask

