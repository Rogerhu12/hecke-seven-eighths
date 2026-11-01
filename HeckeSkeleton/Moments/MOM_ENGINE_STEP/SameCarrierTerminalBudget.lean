import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFirstTerminalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolCoverHybridStage

/-!
# Literal zero and tail parts on the original source labels

These parts are computed from the same terminal calibrations as the
actual parent and covered second sources.  Their fibre factors and
residual multiplicities are retained.  Transport by the first Fourier
phase changes none of them, so their integration uses the mass of the
original first Fourier measure exactly once.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments MeasureTheory

/-- A numerical exponent allowance is applied only after its original
single-profile amplitude has been bounded. -/
theorem terminal_atom_power_bound (Z C A amplitude u v target : ℝ)
    (hZ : 1 ≤ Z) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hamplitude : amplitude ≤ A * Z ^ u) (hexponent : u + v ≤ target) :
    C * amplitude * Z ^ v ≤ C * A * Z ^ target := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  calc
    _ ≤ C * (A * Z ^ u) * Z ^ v :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hamplitude hC)
        (Real.rpow_nonneg hz.le v)
    _ = C * A * Z ^ (u + v) := by rw [Real.rpow_add hz]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hexponent) (mul_nonneg hC hA)

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

namespace ActualGaussStage.TerminalCalibration

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}
variable (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)

def zeroPart (ε Czero : ℝ) : ℝ :=
  (s.fiber : ℝ) * Czero * (T.windows.multiplicity * T.zeroAmplitude) *
    Z ^ (T.productExponent * ε)

def tailPart (Cerror : ℝ) : ℝ :=
  (s.fiber : ℝ) * Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave)

theorem zeroPart_nonneg (ε Czero : ℝ) (hC : 0 ≤ Czero) : 0 ≤ T.zeroPart ε Czero := by
  unfold zeroPart
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC)
      (mul_nonneg (Nat.cast_nonneg _) T.zeroAmplitude_nonneg))
    (Real.rpow_nonneg (zero_le_one.trans T.windows.base_ge_one) _)

theorem tailPart_nonneg (Cerror : ℝ) (hC : 0 ≤ Cerror) : 0 ≤ T.tailPart Cerror := by
  unfold tailPart
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC)
      (mul_nonneg (Nat.cast_nonneg _) T.windows.amplitude_nonneg))
    (Real.rpow_nonneg (zero_le_one.trans T.windows.base_ge_one) _)

/-- Exact decomposition on the original source.  The nonzero covered
cost keeps every original common-support, mask and occurrence label. -/
theorem coverHybridCost_eq_parts (LC RC : SourceCartesianCover G.columns G.ideal)
    (exceptional : s.CoverHybridPredicates LC RC) (ε Cerror Czero : ℝ) :
    T.coverHybridCost LC RC exceptional ε Cerror Czero =
      T.zeroPart ε Czero + (s.fiber : ℝ) * s.coverHybridNonzeroCost LC RC exceptional +
        T.tailPart Cerror := by
  unfold coverHybridCost zeroPart tailPart
  ring

theorem zeroPart_le_power (ε Czero profileConstant profileExponent budget : ℝ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profileConstant)
    (hAmplitude : T.zeroAmplitude ≤ profileConstant * Z ^ profileExponent)
    (hbudget : profileExponent + T.productExponent * ε ≤ budget) :
    T.zeroPart ε Czero ≤
      ((s.fiber : ℝ) * Czero * T.windows.multiplicity * profileConstant) * Z ^ budget := by
  have h := terminal_atom_power_bound Z
    ((s.fiber : ℝ) * Czero * T.windows.multiplicity) profileConstant
    T.zeroAmplitude profileExponent (T.productExponent * ε) budget
    T.windows.base_ge_one (by positivity) hprofile hAmplitude hbudget
  convert h using 1 <;> unfold zeroPart <;> ring

theorem tailPart_le_power (Cerror profileConstant profileExponent budget : ℝ)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profileConstant)
    (hAmplitude : T.tailAmplitude ≤ profileConstant * Z ^ profileExponent)
    (hbudget : profileExponent - Nsave ≤ budget) :
    T.tailPart Cerror ≤
      ((s.fiber : ℝ) * Cerror * T.windows.multiplicity * profileConstant) * Z ^ budget := by
  have h := terminal_atom_power_bound Z
    ((s.fiber : ℝ) * Cerror * T.windows.multiplicity) profileConstant
    T.tailAmplitude profileExponent (-Nsave) budget
    T.windows.base_ge_one (by positivity) hprofile hAmplitude (by linarith)
  convert h using 1 <;> unfold tailPart <;> ring

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem fourierPhase_zeroPart (x : ι → W) (ξ : W) (ε Czero : ℝ) :
    (T.fourierPhase x ξ).zeroPart ε Czero = T.zeroPart ε Czero := rfl

theorem fourierPhase_tailPart (x : ι → W) (ξ : W) (Cerror : ℝ) :
    (T.fourierPhase x ξ).tailPart Cerror = T.tailPart Cerror := rfl

variable [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]

theorem integral_fourierPhase_zeroPart (F : 𝓢(W, ℂ)) (x : ι → W) (ε Czero : ℝ) :
    (∫ ξ, (T.fourierPhase x ξ).zeroPart ε Czero ∂actualFourierMeasure F) =
      (actualFourierMeasure F).real Set.univ * T.zeroPart ε Czero := by
  simp only [fourierPhase_zeroPart, integral_const, smul_eq_mul]

theorem integral_fourierPhase_tailPart (F : 𝓢(W, ℂ)) (x : ι → W) (Cerror : ℝ) :
    (∫ ξ, (T.fourierPhase x ξ).tailPart Cerror ∂actualFourierMeasure F) =
      (actualFourierMeasure F).real Set.univ * T.tailPart Cerror := by
  simp only [fourierPhase_tailPart, integral_const, smul_eq_mul]

end ActualGaussStage.TerminalCalibration

namespace ActualFirstSource.TerminalCalibration

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {ω ψ : HeckeCharacter K} {centered : Bool} {d : MomentData K ω ψ}
variable {a : RealParameters} {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := E) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}
variable (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)

def zeroPart (ε Czero : ℝ) : ℝ := Czero * T.zeroAmplitude * Z ^ (T.productExponent * ε)
def tailPart (Cerror : ℝ) : ℝ := Cerror * T.tailAmplitude * Z ^ (-Nsave)

theorem cost_eq_parts (ε Cerror Czero : ℝ) :
    T.cost ε Cerror Czero = T.zeroPart ε Czero + T.tailPart Cerror := rfl

theorem zeroPart_nonneg (ε Czero : ℝ) (hC : 0 ≤ Czero) : 0 ≤ T.zeroPart ε Czero :=
  mul_nonneg (mul_nonneg hC T.zeroAmplitude_nonneg)
    (Real.rpow_nonneg (zero_le_one.trans T.windows.base_ge_one) _)

theorem tailPart_nonneg (Cerror : ℝ) (hC : 0 ≤ Cerror) : 0 ≤ T.tailPart Cerror :=
  mul_nonneg (mul_nonneg hC T.windows.amplitude_nonneg)
    (Real.rpow_nonneg (zero_le_one.trans T.windows.base_ge_one) _)

theorem zeroPart_le_power (ε Czero profileConstant profileExponent budget : ℝ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profileConstant)
    (hAmplitude : T.zeroAmplitude ≤ profileConstant * Z ^ profileExponent)
    (hbudget : profileExponent + T.productExponent * ε ≤ budget) :
    T.zeroPart ε Czero ≤ Czero * profileConstant * Z ^ budget :=
  terminal_atom_power_bound Z Czero profileConstant T.zeroAmplitude
    profileExponent (T.productExponent * ε) budget T.windows.base_ge_one hC hprofile hAmplitude hbudget

theorem tailPart_le_power (Cerror profileConstant profileExponent budget : ℝ)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profileConstant)
    (hAmplitude : T.tailAmplitude ≤ profileConstant * Z ^ profileExponent)
    (hbudget : profileExponent - Nsave ≤ budget) :
    T.tailPart Cerror ≤ Cerror * profileConstant * Z ^ budget :=
  terminal_atom_power_bound Z Cerror profileConstant T.tailAmplitude
    profileExponent (-Nsave) budget T.windows.base_ge_one hC hprofile hAmplitude (by linarith)

end ActualFirstSource.TerminalCalibration

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.TerminalCalibration.coverHybridCost_eq_parts
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.TerminalCalibration.integral_fourierPhase_zeroPart
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.TerminalCalibration.cost_eq_parts
