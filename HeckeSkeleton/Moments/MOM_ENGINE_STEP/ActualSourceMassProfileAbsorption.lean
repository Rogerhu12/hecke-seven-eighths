import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalSourceMassInputs

set_option linter.unusedSectionVars false

/-!
# Paying the original Mellin profile powers in the same actual mass

The analytic profile bound may contain a fixed constant and a small
power of the base. These are numerical upper-bound parameters only.
The actual normalized family, its chosen children, active rectangles,
Fourier kernels, outer weights and measures are kept literally fixed.

The mass theorem is applied with half the final exponent budget and
the enlarged control `Cprofile * profile * Z ^ rate`. The fixed degree
determines `rate` before the source is chosen. Expanding its power
returns the original profile control and the final exponent, while
retaining `Cprofile ^ degree` in the fixed total constant.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep.ActualSourceMassProfileAbsorption

/-- The extra `1` covers a zero profile degree without a separate case. -/
def rate (ε : ℝ) (degree : ℕ) : ℝ := ε / (2 * ((degree : ℝ) + 1))

theorem rate_pos (ε : ℝ) (degree : ℕ) (hε : 0 < ε) : 0 < rate ε degree := by
  sorry

theorem rate_degree_le (ε : ℝ) (degree : ℕ) (hε : 0 ≤ ε) :
    rate ε degree * degree ≤ ε / 2 := by
  sorry

def scaledProfile (Cprofile profile Z ε : ℝ) (degree : ℕ) : ℝ :=
  Cprofile * profile * Z ^ rate ε degree

theorem le_scaledProfile (Cprofile profile Z ε : ℝ) (degree : ℕ)
    (hC : 1 ≤ Cprofile) (hprofile : 1 ≤ profile) (hZ : 1 ≤ Z) (hε : 0 < ε) :
    profile ≤ scaledProfile Cprofile profile Z ε degree := by
  sorry

theorem scaledProfile_one (Cprofile profile Z ε : ℝ) (degree : ℕ)
    (hC : 1 ≤ Cprofile) (hprofile : 1 ≤ profile) (hZ : 1 ≤ Z) (hε : 0 < ε) :
    1 ≤ scaledProfile Cprofile profile Z ε degree := by
  sorry

/-- The original log-atom amplitude has degree one. A larger fixed
degree is also allowed, and no scale power is placed inside a seminorm. -/
theorem original_amplitude_le_scaled_power
    (Cprofile profile Z ε η amplitude : ℝ) (degree d : ℕ)
    (hC : 1 ≤ Cprofile) (hprofile : 1 ≤ profile) (hZ : 1 ≤ Z) (hε : 0 < ε)
    (hd : 1 ≤ d) (hη : η ≤ rate ε degree)
    (hamp : amplitude ≤ Cprofile * profile ^ d * Z ^ η) :
    amplitude ≤ scaledProfile Cprofile profile Z ε degree ^ d := by
  sorry

/-- This is only the expansion of a numerical majorant. It has no
source-to-child or total-kernel inequality as an input. -/
theorem scaledProfile_mass_le (Cmass Cprofile profile Z ε : ℝ) (degree : ℕ)
    (hCmass : 0 ≤ Cmass) (hC : 1 ≤ Cprofile) (hprofile : 1 ≤ profile)
    (hZ : 1 ≤ Z) (hε : 0 < ε) :
    Cmass * scaledProfile Cprofile profile Z ε degree ^ degree * Z ^ (ε / 2) ≤
      (Cmass * Cprofile ^ degree) * profile ^ degree * Z ^ ε := by
  sorry

/-- An actual nonnegative rectangle can use the enlarged numerical
profile. The original arithmetic index and its weight are unchanged. -/
theorem pointwise_weight_enlarge
    {actual indexWeight Cweight profile enlarged Z exponent : ℝ} (dWeight : ℕ)
    (hactual : 0 ≤ actual) (hCweight : 0 < Cweight)
    (hprofile : 0 < profile) (hZ : 0 < Z) (hcontrol : profile ≤ enlarged)
    (hweight : actual ≤ (Cweight * profile ^ dWeight * Z ^ exponent) * indexWeight) :
    actual ≤ (Cweight * enlarged ^ dWeight * Z ^ exponent) * indexWeight := by
  sorry

end HeckeSkeleton.Moments.EngineStep.ActualSourceMassProfileAbsorption

namespace HeckeSkeleton.Moments.EngineStep.InternalMassAssembly

open NumberField IsDedekindDomain DedekindZetaZeroFree CommonSupportMass
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments ActualNormalizedPairFamily
open ActualSourceMassProfileAbsorption

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
  [MeasurableSpace (WithLp 2 (W × E))] [BorelSpace (WithLp 2 (W × E))]
variable {Θ : Type*} [Fintype Θ]
variable {ω ψ : HeckeCharacter K}

/-- The same direct actual family pays the original profile scale power
inside the final exponent budget. Its physical mask and children are unchanged. -/
theorem actual_direct_source_image_kernel_mass_original_profiles
    (cap dimension width J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight : ℕ)
    (B ε Cweight : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hCweight : 0 < Cweight) :
    ∃ seminorms₁ seminorms₂ : Finset (ℕ × ℕ), ∃ Cmass : ℝ, 0 < Cmass ∧
    ∀ Cprofile : ℝ, 1 ≤ Cprofile →
    ∀ (Z : ℝ), 1 < Z → ∀ profile : ℝ, 1 ≤ profile →
    ∀ (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
      (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
      (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X)
      (s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
      (R : s.SecondStages (E := E) (hDiff := hDiff))
      (L : SourceCartesianAtlas s.columns s.ideal) (hcap : L.slotCount ≤ cap)
      (exceptional : R.prepared.CoverHybridPredicates L) (N : s.Normalization),
    ∀ (families : (R.prepared.liveLeaves L exceptional N) →
        ActualNormalizedPairFamily A σ (WithLp 2 (W × E)) (Bool × Bool) ω ψ Z)
      (F₁ : (R.prepared.liveLeaves L exceptional N) × (Bool × Bool) → 𝓢(W, ℂ))
      (F₂ : (R.prepared.liveLeaves L exceptional N) × (Bool × Bool) → 𝓢(E, ℂ))
      (outer B₁ B₂ : (R.prepared.liveLeaves L exceptional N) × (Bool × Bool) → ℝ)
      (parentWidth : ℝ),
    ProfileWindows (combine families) Finset.univ F₁ F₂ outer B₁ B₂
      (scaledProfile Cprofile profile Z ε (totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight 0))
      cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ seminorms₁ seminorms₂ →
    ∀ (rows : R.prepared.OriginalFibreRows Θ dimension width B Z)
      (physicalMask : Ideal (𝓞 K)), physicalMask ≠ 0 →
      OriginalMaskPrimeData s.mask physicalMask →
      (Ideal.absNorm physicalMask : ℝ) ≤ Z ^ B →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B) →
      (∀ b : (combine families).active Finset.univ,
        outer b.val * (combine families).weight Finset.univ parentWidth b ≤
          (Cweight * profile ^ dWeight * Z ^ (ε / 8)) *
            (R.prepared.arithmeticLabels L hcap exceptional N).carrier.indexWeight
              ((R.prepared.arithmeticLabels L hcap exceptional N).rectangleIndex families b)) →
      (∀ b : (combine families).active Finset.univ,
        IsFiniteMeasure ((combine families).kernel Finset.univ
          (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b)) ∧
      (∑ b : (combine families).active Finset.univ,
        ((combine families).kernel Finset.univ
          (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b).real Set.univ) ≤
        (Cmass * Cprofile ^ totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight 0) *
          profile ^ totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight 0 * Z ^ ε := by
  sorry

/-- The same actual one-pool family pays profile growth after its
physical fibres and two harmonic divisor masses have been proved. -/
theorem actual_amplified_source_image_kernel_mass_original_profiles
    (cap dimension width J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight : ℕ)
    (B ε Cweight ell eps Mmax Bmax : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) (hCweight : 0 < Cweight)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell) (hepsε : eps ≤ ε / 8)
    (hMmax : 0 ≤ Mmax) (hBmax : 0 ≤ Bmax) :
    ∃ seminorms₁ seminorms₂ : Finset (ℕ × ℕ), ∃ Cmass Z₀ : ℝ, 0 < Cmass ∧ 1 < Z₀ ∧
    ∀ Cprofile : ℝ, 1 ≤ Cprofile →
    ∀ (Z : ℝ), Z₀ ≤ Z → ∀ profile : ℝ, 1 ≤ profile →
    ∀ (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (pool : PowerScaleExteriorPool A bad Z ell eps)
      (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
      (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
      (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X)
      (s : ActualFirstSource (E := W) hΓ μv C pool finiteTest centered d a t Y₁ Y₂ X hX)
      (R : s.SecondStages (E := E) (hDiff := hDiff))
      (L : SourceCartesianAtlas s.columns s.ideal) (hcap : L.slotCount ≤ cap)
      (exceptional : R.supported.gated.CoverHybridPredicates L) (N : s.Normalization),
    ∀ (families : (R.supported.gated.liveLeaves L exceptional N) →
        ActualNormalizedPairFamily A σ (WithLp 2 (W × E)) (Bool × Bool) ω ψ Z)
      (F₁ : (R.supported.gated.liveLeaves L exceptional N) × (Bool × Bool) → 𝓢(W, ℂ))
      (F₂ : (R.supported.gated.liveLeaves L exceptional N) × (Bool × Bool) → 𝓢(E, ℂ))
      (outer B₁ B₂ : (R.supported.gated.liveLeaves L exceptional N) × (Bool × Bool) → ℝ)
      (parentWidth : ℝ),
    ProfileWindows (combine families) Finset.univ F₁ F₂ outer B₁ B₂
      (scaledProfile Cprofile profile Z ε (totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight 0))
      cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ seminorms₁ seminorms₂ →
    ∀ (B₀ : ℝ), B₀ + 7 * ell ≤ B →
    ∀ (rows : R.supported.gated.OriginalFibreRows Θ dimension width B Z)
      (physicalMask : Ideal (𝓞 K)), physicalMask ≠ 0 →
      OriginalMaskPrimeData s.mask physicalMask →
      (Ideal.absNorm physicalMask : ℝ) ≤ Z ^ B →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B₀) →
      (∀ b : (combine families).active Finset.univ,
        outer b.val * (combine families).weight Finset.univ parentWidth b ≤
          (Cweight * profile ^ dWeight * Z ^ (ε / 8)) *
            amplifiedIndexWeight pool Mmax Bmax
              ((R.supported.gated.arithmeticLabels L hcap exceptional N).mainCarrier
                (R.supported.gated.arithmeticTag L exceptional N))
              ((R.supported.gated.arithmeticLabels L hcap exceptional N).errorCarrier
                (R.supported.gated.arithmeticTag L exceptional N))
              ((R.supported.gated.arithmeticLabels L hcap exceptional N).rectangleAmplifiedIndex
                families pool (R.supported.gated.arithmeticTag L exceptional N)
                (R.supported.gated.arithmeticTag_mem L exceptional N) b)) →
      (∀ b : (combine families).active Finset.univ,
        IsFiniteMeasure ((combine families).kernel Finset.univ
          (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b)) ∧
      (∑ b : (combine families).active Finset.univ,
        ((combine families).kernel Finset.univ
          (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b).real Set.univ) ≤
        (Cmass * Cprofile ^ totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight 0) *
          profile ^ totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight 0 * Z ^ ε := by
  sorry

end HeckeSkeleton.Moments.EngineStep.InternalMassAssembly

#print axioms HeckeSkeleton.Moments.EngineStep.ActualSourceMassProfileAbsorption.rate_degree_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSourceMassProfileAbsorption.original_amplitude_le_scaled_power
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSourceMassProfileAbsorption.scaledProfile_mass_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSourceMassProfileAbsorption.pointwise_weight_enlarge
#print axioms HeckeSkeleton.Moments.EngineStep.InternalMassAssembly.actual_direct_source_image_kernel_mass_original_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.InternalMassAssembly.actual_amplified_source_image_kernel_mass_original_profiles
