import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualSourceMassProfileAbsorption

/-!
# One original profile envelope pays every part of the actual kernel mass

The actual log atoms and the actual Fourier kernels may both contain
small original scale powers. Their common numerical envelope is
`Cprofile * profile * Z ^ rate`. It controls the original atom weights
as well as the two profile windows of the same normalized family.

The complete fixed profile degree already includes the pointwise
weight degree. Applying the mass theorem at half the exponent budget
and then expanding this one envelope pays all those powers exactly
once. Every actual source, chosen child, Fourier kernel, outer weight,
physical mask and measure remains fixed throughout the argument.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

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

/-- The same direct actual family uses one envelope for its original
atom weights and its profile windows. The final fixed degree includes both. -/
theorem actual_direct_source_image_kernel_mass_profile_envelope
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
          (Cweight *
            scaledProfile Cprofile profile Z ε
              (totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight 0) ^ dWeight * Z ^ (ε / 8)) *
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
  obtain ⟨s₁, s₂, Cmass, hCmass, hm⟩ :=
    actual_direct_source_image_kernel_mass_physical_mask
      (A := A) (σ := σ) (C := C) (Γ := Γ) (hΓ := hΓ) (μv := μv) (hDiff := hDiff)
      (W := W) (E := E) (Θ := Θ) (ω := ω) (ψ := ψ)
      cap dimension width J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight
      B (ε / 2) Cweight hB (by positivity) hCweight
  refine ⟨s₁, s₂, Cmass, hCmass, ?_⟩
  intro Cprofile hCprofile Z hZ profile hprofile finiteTest centered d a t Y₁ Y₂ X hX
    s R L hcap exceptional N families F₁ F₂ outer B₁ B₂ parentWidth windows
    rows physicalMask hmask0 mask hmaskN hN hweight
  let degree := totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight 0
  let envelope := scaledProfile Cprofile profile Z ε degree
  have henvelope : 1 ≤ envelope :=
    scaledProfile_one Cprofile profile Z ε degree hCprofile hprofile hZ.le hε
  have hweights : ∀ b : (combine families).active Finset.univ,
      outer b.val * (combine families).weight Finset.univ parentWidth b ≤
        (Cweight * envelope ^ dWeight * Z ^ ((ε / 2) / 4)) *
          (R.prepared.arithmeticLabels L hcap exceptional N).carrier.indexWeight
            ((R.prepared.arithmeticLabels L hcap exceptional N).rectangleIndex families b) := by
    simpa only [show (ε / 2) / 4 = ε / 8 by ring] using hweight
  have hmass := hm Z hZ envelope henvelope finiteTest centered d a t Y₁ Y₂ X hX
    s R L hcap exceptional N families F₁ F₂ outer B₁ B₂ parentWidth windows
    rows physicalMask hmask0 mask hmaskN hN hweights
  refine ⟨hmass.1, hmass.2.trans ?_⟩
  exact scaledProfile_mass_le Cmass Cprofile profile Z ε degree
    hCmass.le hCprofile hprofile hZ.le hε

/-- The same original pool and its actual prime/valuation branches
use that identical envelope, including the degree of their pointwise weights. -/
theorem actual_amplified_source_image_kernel_mass_profile_envelope
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
          (Cweight *
            scaledProfile Cprofile profile Z ε
              (totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight 0) ^ dWeight * Z ^ (ε / 8)) *
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
  have hepshalf : eps ≤ (ε / 2) / 4 := by linarith
  obtain ⟨s₁, s₂, Cmass, Z₀, hCmass, hZ₀, hm⟩ :=
    actual_amplified_source_image_kernel_mass_physical_mask
      (A := A) (σ := σ) (C := C) (Γ := Γ) (hΓ := hΓ) (μv := μv) (hDiff := hDiff)
      (W := W) (E := E) (Θ := Θ) (ω := ω) (ψ := ψ)
      cap dimension width J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight
      B (ε / 2) Cweight ell eps Mmax Bmax hB (by positivity) hCweight
      hell heps hepsell hepshalf hMmax hBmax
  refine ⟨s₁, s₂, Cmass, Z₀, hCmass, hZ₀, ?_⟩
  intro Cprofile hCprofile Z hZ profile hprofile bad pool finiteTest centered d a t Y₁ Y₂ X hX
    s R L hcap exceptional N families F₁ F₂ outer B₁ B₂ parentWidth windows
    B₀ hbox rows physicalMask hmask0 mask hmaskN hN hweight
  let degree := totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight 0
  let envelope := scaledProfile Cprofile profile Z ε degree
  have hZ1 : 1 < Z := hZ₀.trans_le hZ
  have henvelope : 1 ≤ envelope :=
    scaledProfile_one Cprofile profile Z ε degree hCprofile hprofile hZ1.le hε
  have hweights : ∀ b : (combine families).active Finset.univ,
      outer b.val * (combine families).weight Finset.univ parentWidth b ≤
        (Cweight * envelope ^ dWeight * Z ^ ((ε / 2) / 4)) *
          amplifiedIndexWeight pool Mmax Bmax
            ((R.supported.gated.arithmeticLabels L hcap exceptional N).mainCarrier
              (R.supported.gated.arithmeticTag L exceptional N))
            ((R.supported.gated.arithmeticLabels L hcap exceptional N).errorCarrier
              (R.supported.gated.arithmeticTag L exceptional N))
            ((R.supported.gated.arithmeticLabels L hcap exceptional N).rectangleAmplifiedIndex
              families pool (R.supported.gated.arithmeticTag L exceptional N)
              (R.supported.gated.arithmeticTag_mem L exceptional N) b) := by
    simpa only [show (ε / 2) / 4 = ε / 8 by ring] using hweight
  have hmass := hm Z hZ envelope henvelope bad pool finiteTest centered d a t Y₁ Y₂ X hX
    s R L hcap exceptional N families F₁ F₂ outer B₁ B₂ parentWidth windows
    B₀ hbox rows physicalMask hmask0 mask hmaskN hN hweights
  refine ⟨hmass.1, hmass.2.trans ?_⟩
  exact scaledProfile_mass_le Cmass Cprofile profile Z ε degree
    hCmass.le hCprofile hprofile hZ1.le hε

end HeckeSkeleton.Moments.EngineStep.InternalMassAssembly

#print axioms HeckeSkeleton.Moments.EngineStep.InternalMassAssembly.actual_direct_source_image_kernel_mass_profile_envelope
#print axioms HeckeSkeleton.Moments.EngineStep.InternalMassAssembly.actual_amplified_source_image_kernel_mass_profile_envelope
