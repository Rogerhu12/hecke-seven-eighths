import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedSecondResidual
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolFourierStage

/-!
# Integration of the actual second stages over the first Fourier measure

Only the original fixed stage and its raw terminal calibration are used.
The phase-dependent complete residual kernels are integrable by the
finite-column Fubini theorem. This closes the analytic substitution
needed to pass from the first normalized pool integrals to the actual
second sources.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory

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

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

theorem phase_class_kernel_integrable
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
    (F : SchwartzMap W ℂ) (x : ι → W)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) (D : s.mask.powerset)
    (label : Fin ((s.charts DE D).rowLabelCount + 1)) :
    Integrable (fun ξ =>
      ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts DE D).classKernelCost
        s.mask s.cutoff s.cutoff_one label) (actualFourierMeasure F) := by
  let b := canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property
  let source := s.sources DE
  let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val
  let a := fun i => generatedOriginalColumn (σ := σ) hΓ (b.secondLeftIdeal i)
    (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
    (b.secondLeft_generates C i)
  let a' := fun j => generatedOriginalColumn (σ := σ) hΓ (b.secondRightIdeal j)
    (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
    (b.secondRight_generates C j)
  let chart := s.charts DE D
  have hi := actual_second_residual_first_phase_integrable (σ := σ) PUnit.{1} F chart.kernel
    (source.rows.filter (fun t => chart.rowLabel t = label))
    (fun t => -t.out.val) source.leftColumns source.rightColumns
    b.commonLeftIdeal b.commonRightIdeal b.leftResidual b.rightResidual
    (engineAllowedGenerator C b.commonLeftIdeal) (engineAllowedGenerator C b.commonRightIdeal)
    (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle))
    (fun t => secondOrbitalScalar s.radius D.val * chart.weight t)
    (fun i => chart.leftCoefficient i * (a i).divisorPhase δ)
    (fun j => chart.rightCoefficient j * (a' j).divisorPhase δ)
    x x chart.leftPoint chart.rightPoint
  let cost (rows : Finset (SIntegerOrbits K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)) (leftWeight rightWeight : ι → ℂ) : ℝ :=
    secondResidualKernelCost (σ := σ) PUnit.{1} chart.kernel rows (fun t => -t.out.val)
      source.leftColumns source.rightColumns
      b.commonLeftIdeal b.commonRightIdeal b.leftResidual b.rightResidual
      (engineAllowedGenerator C b.commonLeftIdeal) (engineAllowedGenerator C b.commonRightIdeal)
      (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
      (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle))
      (fun t => secondOrbitalScalar s.radius D.val * chart.weight t)
      leftWeight rightWeight chart.leftPoint chart.rightPoint
  convert hi using 1
  funext ξ
  have hrows : ((s.withMultiplier (fun i => jointPhase ξ (x i))).sources DE).rows =
      source.rows :=
    s.withMultiplier_rows (fun i => Real.fourierChar (inner ℝ ξ (x i))) DE
  have hfilter := congrArg
    (fun rows : Finset (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) =>
      rows.filter (fun t => chart.rowLabel t = label)) hrows
  have hleft : (fun i => (jointPhase ξ (x i) * chart.leftCoefficient i) *
      (a i).divisorPhase δ) =
      (fun i => (chart.leftCoefficient i * (a i).divisorPhase δ) *
        jointPhase ξ (x i)) := by
    funext i
    ring
  have hright : (fun j => (jointPhase ξ (x j) * chart.rightCoefficient j) *
      (a' j).divisorPhase δ) =
      (fun j => (chart.rightCoefficient j * (a' j).divisorPhase δ) *
        jointPhase ξ (x j)) := by
    funext j
    ring
  change cost
      (((s.withMultiplier (fun i => jointPhase ξ (x i))).sources DE).rows.filter
        (fun t => chart.rowLabel t = label))
      (fun i => (jointPhase ξ (x i) * chart.leftCoefficient i) * (a i).divisorPhase δ)
      (fun j => (jointPhase ξ (x j) * chart.rightCoefficient j) * (a' j).divisorPhase δ) =
    cost (source.rows.filter (fun t => chart.rowLabel t = label))
      (fun i => (chart.leftCoefficient i * (a i).divisorPhase δ) * jointPhase ξ (x i))
      (fun j => (chart.rightCoefficient j * (a' j).divisorPhase δ) * jointPhase ξ (x j))
  exact (congrArg (fun rows => cost rows
    (fun i => (jointPhase ξ (x i) * chart.leftCoefficient i) * (a i).divisorPhase δ)
    (fun j => (jointPhase ξ (x j) * chart.rightCoefficient j) * (a' j).divisorPhase δ))
      hfilter).trans
    (congrArg₂ (cost (source.rows.filter (fun t => chart.rowLabel t = label))) hleft hright)

theorem phase_kernel_integrable
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
    (F : SchwartzMap W ℂ) (x : ι → W)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) (D : s.mask.powerset) :
    Integrable (fun ξ =>
      ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts DE D).kernelCost
        s.mask s.cutoff s.cutoff_one) (actualFourierMeasure F) := by
  change Integrable (fun ξ =>
    ∑ label : Fin ((s.charts DE D).rowLabelCount + 1),
      ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts DE D).classKernelCost
        s.mask s.cutoff s.cutoff_one label) (actualFourierMeasure F)
  exact integrable_finsetSum _ (fun label _ =>
    s.phase_class_kernel_integrable F x DE D label)

def phaseKernelCost
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest) (x : ι → W) (ξ : W) : ℝ :=
  ∑ DE, ∑ D : s.mask.powerset,
    ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts DE D).kernelCost
      s.mask s.cutoff s.cutoff_one

set_option maxHeartbeats 800000 in
theorem phaseKernelCost_integrable
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
    (F : SchwartzMap W ℂ) (x : ι → W) :
    Integrable (s.phaseKernelCost x) (actualFourierMeasure F) := by
  let kernel (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
      (D : s.mask.powerset) (ξ : W) : ℝ :=
    ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts DE D).kernelCost
      s.mask s.cutoff s.cutoff_one
  have hk (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) (D : s.mask.powerset) :
      Integrable (kernel DE D) (actualFourierMeasure F) :=
    s.phase_kernel_integrable F x DE D
  exact integrable_finsetSum (Finset.univ : Finset (commonSupportPool G.columns G.columns
    (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))) (fun DE _ =>
      integrable_finsetSum (Finset.univ : Finset s.mask.powerset) (fun D _ => hk DE D))

namespace TerminalCalibration

variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

theorem phase_cost_integrable
    (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    Integrable (fun ξ => (T.fourierPhase x ξ).cost ε Cerror Czero)
      (actualFourierMeasure F) := by
  letI := actualFourierMeasure_finite F
  change Integrable (fun ξ => (s.fiber : ℝ) *
    (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε) + s.phaseKernelCost x ξ +
      Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave))) (actualFourierMeasure F)
  exact (((integrable_const _).add (s.phaseKernelCost_integrable F x)).add
    (integrable_const _)).const_mul (s.fiber : ℝ)

private theorem integral_constant_kernel_formula {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (f : Y → ℝ) (hf : Integrable f μ)
    (weight zeroTerm tailTerm : ℝ) :
    (∫ y, weight * (zeroTerm + f y + tailTerm) ∂μ) =
      weight * (μ.real Set.univ * (zeroTerm + tailTerm) + ∫ y, f y ∂μ) := by
  rw [integral_const_mul,
    integral_add ((integrable_const zeroTerm).add hf) (integrable_const tailTerm),
    integral_add (integrable_const zeroTerm) hf, integral_const, integral_const]
  simp only [smul_eq_mul]
  ring

theorem integral_phase_cost
    (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    (∫ ξ, (T.fourierPhase x ξ).cost ε Cerror Czero ∂actualFourierMeasure F) =
      (s.fiber : ℝ) *
        ((actualFourierMeasure F).real Set.univ *
          (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε) +
            Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave)) +
          ∫ ξ, s.phaseKernelCost x ξ ∂actualFourierMeasure F) := by
  letI := actualFourierMeasure_finite F
  change (∫ ξ, (s.fiber : ℝ) *
    (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε) + s.phaseKernelCost x ξ +
      Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave)) ∂actualFourierMeasure F) = _
  exact integral_constant_kernel_formula (actualFourierMeasure F)
    (s.phaseKernelCost x) (s.phaseKernelCost_integrable F x) (s.fiber : ℝ)
    (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε))
    (Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave))

end TerminalCalibration
end ActualGaussStage

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

theorem ActualPoolStages.TerminalCalibration.phaseCost_integrable
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    Integrable (fun ξ => T.phaseCost x ξ ε Cerror Czero) (actualFourierMeasure F) := by
  unfold ActualPoolStages.TerminalCalibration.phaseCost
  apply Integrable.const_mul
  apply Integrable.add
  · apply Integrable.add
    · apply Integrable.add
      · exact (T.main.phase_cost_integrable F x ε Cerror Czero).const_mul d.multiplicity
      · exact integrable_finsetSum _ (fun p _ =>
          ((T.one p).phase_cost_integrable F (fun i => x i.val) ε Cerror Czero).const_mul _)
    · exact integrable_finsetSum _ (fun p _ =>
        ((T.six p).phase_cost_integrable F (fun i => x i.val) ε Cerror Czero).const_mul _)
  · exact integrable_finsetSum _ (fun p _ =>
      ((T.seven p).phase_cost_integrable F (fun i => x i.val) ε Cerror Czero).const_mul _)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.phase_kernel_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.TerminalCalibration.integral_phase_cost
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.TerminalCalibration.phaseCost_integrable
