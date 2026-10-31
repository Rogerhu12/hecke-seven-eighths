import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSourceFiniteLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonLabelConditions

/-!
# Physical and arithmetic source support before the second estimates

Empty original physical row sets receive their proved zero orbital
fibre bound.  Common blocks outside the exact image of nonzero original
coefficient pairs receive zero chart coefficients.  Both changes are
proved from original finite source data before Möbius expansion and
Cauchy.  They preserve the actual kernels and all physical cutoffs.

This prevents a loose profile bound on an empty source, or cancelled
noncoprime pairs in an inactive common block, from creating spurious
live arithmetic labels in the final mass estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

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

namespace ActualGaussSource

variable {ι : Type*} (G : ActualGaussSource C ι)

def coefficientSupport : Finset ι := G.columns.filter fun i => G.coefficient i ≠ 0

def activeCommon : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)) :=
  commonSupportPool G.coefficientSupport G.coefficientSupport
    (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)

theorem energy_eq_zero_of_rows_eq_empty (h : G.rows = ∅) : G.energy hDiff = 0 := by
  simp only [energy, h, Finset.sum_empty]

/-- The old divisor is inherited on the genuine support of the whole
coefficient; columns on which the coefficient is zero need no condition. -/
theorem activeCommon_old_mask
    (S : Ideal (𝓞 K)) (hS : Squarefree S)
    (hdiv : ∀ i ∈ G.columns, G.coefficient i ≠ 0 → S ∣ (G.ideal i).val)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K)) (hDE : DE ∈ G.activeCommon) :
    S ∣ DE.1 ∧ S ∣ DE.2 := by
  obtain ⟨ij, hij, he⟩ := Finset.mem_image.mp hDE
  have hi := Finset.mem_filter.mp (Finset.mem_product.mp hij).1
  have hj := Finset.mem_filter.mp (Finset.mem_product.mp hij).2
  have hd := actual_common_label_old_mask S (G.ideal ij.1).val (G.ideal ij.2).val
    hS (G.ideal ij.1).property.1 (G.ideal ij.2).property.1
    (hdiv ij.1 hi.1 hi.2) (hdiv ij.2 hj.1 hj.2)
  simpa only [he] using hd

theorem activeCommon_norm_le (Y : ℝ)
    (hN : ∀ i ∈ G.columns, G.coefficient i ≠ 0 → (Ideal.absNorm (G.ideal i).val : ℝ) ≤ Y)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K)) (hDE : DE ∈ G.activeCommon) :
    (Ideal.absNorm DE.1 : ℝ) ≤ Y ∧ (Ideal.absNorm DE.2 : ℝ) ≤ Y := by
  obtain ⟨ij, hij, he⟩ := Finset.mem_image.mp hDE
  have hi := Finset.mem_filter.mp (Finset.mem_product.mp hij).1
  have hj := Finset.mem_filter.mp (Finset.mem_product.mp hij).2
  have hn := actual_common_label_norm_le (G.ideal ij.1).val (G.ideal ij.2).val
    (G.ideal ij.1).property.1 (G.ideal ij.2).property.1
  rw [he] at hn
  exact ⟨hn.1.trans (hN ij.1 hi.1 hi.2), hn.2.trans (hN ij.2 hj.1 hj.2)⟩

end ActualGaussSource

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)

/-- Every nonzero original coprime pair identifies its genuine active
common label before any transform or positive estimate. -/
theorem activeCommon_of_pair
    (_s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (i : ι) (j : ι)
    (hi : i ∈ (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal
      DE.val DE.property).leftColumns G.columns)
    (hj : j ∈ (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal
      DE.val DE.property).rightColumns G.columns)
    (hcop : IsCoprime
      ((canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property).leftResidual i).val
      ((canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property).rightResidual j).val)
    (hci : G.coefficient i ≠ 0) (hcj : G.coefficient j ≠ 0) :
    DE.val ∈ G.activeCommon := by
  let b := canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property
  have hi' := Finset.mem_filter.mp hi
  have hj' := Finset.mem_filter.mp hj
  apply Finset.mem_image.mpr
  refine ⟨(i, j), Finset.mem_product.mpr
    ⟨Finset.mem_filter.mpr ⟨hi'.1, hci⟩, Finset.mem_filter.mpr ⟨hj'.1, hcj⟩⟩, ?_⟩
  apply (commonSupportLabel_eq_iff _ _ _ _
    (commonSupportPool_support_eq G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val) DE.val DE.property)).mpr
  refine ⟨hi'.2, hj'.2, ?_⟩
  simpa only [b.left_residual i, b.right_residual j] using hcop

/-- The source's actual zero physical rows force zero total cost.  The
common-label gates are justified from original coprime coefficient
pairs, so they are inserted before the Möbius and phase expansions. -/
def supported : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest :=
  { s.gated with
    fiber := if G.rows = ∅ then 0 else s.fiber
    calibration :=
      { s.calibration with
        fiber := by
          intro q
          by_cases hrows : G.rows = ∅
          · simp [hrows]
          · simpa only [if_neg hrows] using s.calibration.fiber q }
    charts := fun DE D =>
      { s.gated.charts DE D with
        leftCoefficient := fun i =>
          if DE.val ∈ G.activeCommon then (s.gated.charts DE D).leftCoefficient i else 0
        rightCoefficient := fun j =>
          if DE.val ∈ G.activeCommon then (s.gated.charts DE D).rightCoefficient j else 0
        profile := by
          intro q i hi j hj hcop
          by_cases hactive : DE.val ∈ G.activeCommon
          · simpa only [if_pos hactive] using (s.gated.charts DE D).profile q i hi j hj hcop
          · have hz : G.coefficient i = 0 ∨ G.coefficient j = 0 := by
              by_cases hci : G.coefficient i = 0
              · exact Or.inl hci
              · exact Or.inr (by
                  by_contra hcj
                  exact hactive (s.activeCommon_of_pair DE i j hi hj hcop hci hcj))
            have he := (s.gated.charts DE D).profile q i hi j hj hcop
            rcases hz with hci | hcj
            · simpa only [gated, if_pos hci, if_neg hactive, zero_mul, mul_zero] using he
            · simpa only [gated, if_pos hcj, if_neg hactive, star_zero, mul_zero, zero_mul] using he } }

@[simp] theorem supported_fiber_eq_zero (hrows : G.rows = ∅) : s.supported.fiber = 0 := by
  simp only [supported, if_pos hrows]

theorem supported_fiber_nonzero_rows (hne : s.supported.fiber ≠ 0) : G.rows.Nonempty := by
  by_contra hrows
  exact hne (s.supported_fiber_eq_zero (Finset.not_nonempty_iff_eq_empty.mp hrows))

theorem supported_left_nonzero_active
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) (i : ι)
    (hi : (s.supported.charts DE D).leftCoefficient i ≠ 0) : DE.val ∈ G.activeCommon := by
  by_contra hn
  exact hi (by simp only [supported, if_neg hn])

theorem gated_left_nonzero_original
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) (i : ι)
    (hi : (s.gated.charts DE D).leftCoefficient i ≠ 0) :
    (s.charts DE D).leftCoefficient i ≠ 0 := by
  intro hz
  exact hi (by simp only [gated, hz, ite_self])

theorem supported_gated_leaf_active
    (LC RC : SourceCartesianCover G.columns G.ideal)
    (exceptional : s.supported.gated.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W)
    (j : s.supported.gated.CoveredLeafKey LC RC) (h : Q)
    (i : AllocationColumn K (s.supported.gated.coveredLeaf LC RC exceptional F x j).leftSlots)
    (hi : (s.supported.gated.coveredLeaf LC RC exceptional F x j).leftCoefficient h i ≠ 0) :
    j.1.1.val ∈ G.activeCommon := by
  apply s.supported_left_nonzero_active j.1.1 j.1.2.1 (j.1.leftReindex.index i)
  apply s.supported.gated_left_nonzero_original j.1.1 j.1.2.1 _
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hi).1).1).1

namespace TerminalCalibration

variable {s}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

def supported (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay) :
    s.supported.TerminalCalibration sTail sZero k Z Lmax Nsave decay := { T with }

end TerminalCalibration
end ActualGaussStage

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
variable {dpool : FirstGaussPoolData C P ι} {c : ι → ℂ}

namespace FirstGaussPoolData

theorem errorRows_nonempty_not_dvd_frozen (d : FirstGaussPoolData C P ι)
    (p : ExteriorPrime A) (hne : (d.errorRows p).Nonempty) : ¬p.val.asIdeal ∣ d.frozen := by
  obtain ⟨h, hh⟩ := hne
  exact (Finset.mem_filter.mp hh).2.2

theorem residualCoefficient_nonzero_original (d : FirstGaussPoolData C P ι)
    (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ) (i : d.valuationColumns p n)
    (hi : d.residualCoefficient p n c i ≠ 0) : c i.val ≠ 0 := by
  rw [d.residualCoefficient_eq] at hi
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hi).1).1

theorem residualSource_nonzero_dvd (d : FirstGaussPoolData C P ι)
    (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ) (S : Ideal (𝓞 K))
    (hS : S ∣ d.frozen)
    (hc : ∀ i ∈ d.columns, c i ≠ 0 → S ∣ (d.ideal i).val)
    (hrows : (d.errorRows p).Nonempty)
    (i : d.valuationColumns p n) (hi : (d.residualSource p n c).coefficient i ≠ 0) :
    S ∣ ((d.residualSource p n c).ideal i).val := by
  apply (d.residualPresentation p n i).dvd_residual_of_dvd_original S
  · exact hc i.val (Finset.mem_filter.mp i.property).1
      (d.residualCoefficient_nonzero_original p n c i hi)
  · intro hp
    exact d.errorRows_nonempty_not_dvd_frozen p hrows (hp.trans hS)

end FirstGaussPoolData

namespace ActualPoolStages

def supported (s : ActualPoolStages (E := E) hΓ μv hDiff dpool c finiteTest) :
    ActualPoolStages (E := E) hΓ μv hDiff dpool c finiteTest where
  main := s.main.supported
  one p := (s.one p).supported
  six p := (s.six p).supported
  seven p := (s.seven p).supported

namespace TerminalCalibration

variable {s : ActualPoolStages (E := E) hΓ μv hDiff dpool c finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def supported (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay) :
    s.supported.TerminalCalibration sTail sZero k Lmax Nsave decay where
  main := T.main.supported
  one p := (T.one p).supported
  six p := (T.six p).supported
  seven p := (T.seven p).supported

end TerminalCalibration
end ActualPoolStages

namespace FirstBlockPoolData.SecondStages

variable {κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockPoolData chart P M X hX}

def supported (s : p.SecondStages (E := E) (hDiff := hDiff)) : p.SecondStages (E := E) (hDiff := hDiff) where
  left S χ := (s.left S χ).supported
  right S χ := (s.right S χ).supported

namespace TerminalCalibration

variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def supported (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay) :
    s.supported.TerminalCalibration sTail sZero k Lmax Nsave decay where
  left S χ := (T.left S χ).supported
  right S χ := (T.right S χ).supported

end TerminalCalibration
end FirstBlockPoolData.SecondStages

variable {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}

namespace ActualFirstSource.SecondStages

variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}

def supported (R : s.SecondStages (E := E) (hDiff := hDiff)) :
    s.SecondStages (E := E) (hDiff := hDiff) := fun v D => (R v D).supported

namespace TerminalCalibration

variable {R : s.SecondStages (E := E) (hDiff := hDiff)}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def supported (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay) :
    R.supported.TerminalCalibration sTail sZero k Lmax Nsave decay := fun v D => (T v D).supported

end TerminalCalibration
end ActualFirstSource.SecondStages

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.supported
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.supported_gated_leaf_active
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.residualSource_nonzero_dvd

