import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNormalizedImageFibres
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualArithmeticIndex
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectLeafNormWindows

/-!
# Actual physical source images give the normalized kernel mass

These internal assembly theorems use the genuine prepared source and
its literal live leaves. Original column norm and old-mask windows
produce arithmetic admissibility. Physical row classifiers produce the
finite-fibre estimate. Neither fact is a conclusion supplied by the caller.

Only the per-rectangle arithmetic scalar inequality remains to be
inserted from the original allowance and atom windows. Its index is the
one computed from the same actual leaf, with both divisors and all
allocations. The children, their active set, and their kernels stay
unchanged throughout. Constants and Fourier seminorms are chosen before
the scale, source, atlas, profiles, or chosen normalized family.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep.InternalMassAssembly

open NumberField IsDedekindDomain DedekindZetaZeroFree CommonSupportMass
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments ActualNormalizedPairFamily

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

/-- The direct source has no artificial pool and allows zero selected
slots. Its original physical classifier and column window fill both
the arithmetic support and fibre arguments internally. -/
theorem actual_direct_source_image_kernel_mass
    (cap dimension width J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight : ℕ)
    (B ε Cweight : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hCweight : 0 < Cweight) :
    ∃ seminorms₁ seminorms₂ : Finset (ℕ × ℕ), ∃ Cmass : ℝ, 0 < Cmass ∧
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
    ProfileWindows (combine families) Finset.univ F₁ F₂ outer B₁ B₂ profile
      cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ seminorms₁ seminorms₂ →
    ∀ (rows : R.prepared.OriginalFibreRows Θ dimension width B Z)
      (oldMask : Ideal (𝓞 K)), Squarefree oldMask → oldMask ≠ 0 →
      OriginalMaskPrimeData s.mask oldMask →
      (Ideal.absNorm oldMask : ℝ) ≤ Z ^ B →
      (∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val) →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B) →
      (∀ b : (combine families).active Finset.univ,
        outer b.val * (combine families).weight Finset.univ parentWidth b ≤
          (Cweight * profile ^ dWeight * Z ^ (ε / 4)) *
            (R.prepared.arithmeticLabels L hcap exceptional N).carrier.indexWeight
              ((R.prepared.arithmeticLabels L hcap exceptional N).rectangleIndex families b)) →
      (∀ b : (combine families).active Finset.univ,
        IsFiniteMeasure ((combine families).kernel Finset.univ
          (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b)) ∧
      (∑ b : (combine families).active Finset.univ,
        ((combine families).kernel Finset.univ
          (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b).real Set.univ) ≤
        Cmass * profile ^ totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight 0 * Z ^ ε := by
  let Cf := kernelSourceFibreConstant K cap (Fintype.card Θ) dimension width B ε hB hε
  have hCf : 0 < Cf :=
    kernelSourceFibreConstant_pos K cap (Fintype.card Θ) dimension width B ε hB hε
  obtain ⟨s₁, s₂, Cmass, hCmass, hm⟩ :=
    direct_kernel_mass_of_pointwise_index (A := A) (σ := σ) (ω := ω) (ψ := ψ)
      (U := W) (E := E) cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight 0
      (cap + 2) B ε Cweight (4 * Cf) hB hε hCweight (by positivity)
  refine ⟨s₁, s₂, Cmass, hCmass, ?_⟩
  intro Z hZ profile hprofile finiteTest centered d a t Y₁ Y₂ X hX s R L hcap
    exceptional N families F₁ F₂ outer B₁ B₂ parentWidth windows
    rows oldMask hs hs0 mask hmaskN hmask hN hweight
  have hadmissible := R.arithmeticLabels_admissible L hcap exceptional N
    B oldMask hs hmask hN
  apply hm Z hZ profile hprofile (combine families) Finset.univ
    F₁ F₂ outer B₁ B₂ parentWidth windows oldMask hs hs0
    (R.prepared.arithmeticLabels L hcap exceptional N).carrier hadmissible
    ((R.prepared.arithmeticLabels L hcap exceptional N).rectangleIndex families) hweight
  intro j
  have hf := R.prepared.normalized_image_kernel_fibre L hcap ε hB hε hZ.le
    rows oldMask hs0 mask hmaskN hN exceptional N families j
  simpa only [Cf, pow_zero, mul_one] using hf

/-- The amplified source uses the fixed original pool and global
deletion windows. Its actual prime and valuation remain in the image;
the one pool loss and both independent divisor masses are paid by the
proved finite-index theorem. -/
theorem actual_amplified_source_image_kernel_mass
    (cap dimension width J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight : ℕ)
    (B ε Cweight ell eps Mmax Bmax : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) (hCweight : 0 < Cweight)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell) (hepsε : eps ≤ ε / 4)
    (hMmax : 0 ≤ Mmax) (hBmax : 0 ≤ Bmax) :
    ∃ seminorms₁ seminorms₂ : Finset (ℕ × ℕ), ∃ Cmass Z₀ : ℝ, 0 < Cmass ∧ 1 < Z₀ ∧
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
    ProfileWindows (combine families) Finset.univ F₁ F₂ outer B₁ B₂ profile
      cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ seminorms₁ seminorms₂ →
    ∀ (B₀ : ℝ), B₀ + 7 * ell ≤ B →
    ∀ (rows : R.supported.gated.OriginalFibreRows Θ dimension width B Z)
      (oldMask : Ideal (𝓞 K)), Squarefree oldMask → oldMask ≠ 0 →
      OriginalMaskPrimeData s.mask oldMask →
      (Ideal.absNorm oldMask : ℝ) ≤ Z ^ B →
      (∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val) →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B₀) →
      (∀ b : (combine families).active Finset.univ,
        outer b.val * (combine families).weight Finset.univ parentWidth b ≤
          (Cweight * profile ^ dWeight * Z ^ (ε / 4)) *
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
        Cmass * profile ^ totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight 0 * Z ^ ε := by
  let Cf := kernelSourceFibreConstant K cap (Fintype.card Θ) dimension width B ε hB hε
  have hCf : 0 < Cf :=
    kernelSourceFibreConstant_pos K cap (Fintype.card Θ) dimension width B ε hB hε
  obtain ⟨s₁, s₂, Cmass, Z₀, hCmass, hZ₀, hm⟩ :=
    amplified_kernel_mass_of_pointwise_index (A := A) (σ := σ) (ω := ω) (ψ := ψ)
      (U := W) (E := E) cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight 0
      (cap + 2) B ε Cweight (4 * Cf) ell eps Mmax Bmax hB hε hCweight
      (by positivity) hell heps hepsell hepsε hMmax hBmax
  refine ⟨s₁, s₂, Cmass, Z₀, hCmass, hZ₀, ?_⟩
  intro Z hZ profile hprofile bad pool finiteTest centered d a t Y₁ Y₂ X hX s R L hcap
    exceptional N families F₁ F₂ outer B₁ B₂ parentWidth windows
    B₀ hbox rows oldMask hs hs0 mask hmaskN hmask hN hweight
  have hZ1 : 1 < Z := hZ₀.trans_le hZ
  have hB₀ : B₀ ≤ B := by linarith
  have hN' : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B := by
    intro i hi
    exact (hN i hi).trans (Real.rpow_le_rpow_of_exponent_le hZ1.le hB₀)
  have hadmissible := R.arithmeticCarriers_admissible L hcap N exceptional
    B oldMask hs hmask hN'
  apply hm Z hZ profile hprofile (combine families) Finset.univ
    F₁ F₂ outer B₁ B₂ parentWidth windows bad pool Mmax Bmax hMmax le_rfl le_rfl
    oldMask hs hs0
    ((R.supported.gated.arithmeticLabels L hcap exceptional N).mainCarrier
      (R.supported.gated.arithmeticTag L exceptional N)) hadmissible.1
    ((R.supported.gated.arithmeticLabels L hcap exceptional N).errorCarrier
      (R.supported.gated.arithmeticTag L exceptional N))
    (fun n _ p _ => hadmissible.2 n p)
    ((R.supported.gated.arithmeticLabels L hcap exceptional N).rectangleAmplifiedIndex
      families pool (R.supported.gated.arithmeticTag L exceptional N)
      (R.supported.gated.arithmeticTag_mem L exceptional N)) hweight
  intro j
  have hf := R.supported.gated.normalized_image_kernel_fibre L hcap ε B₀ hB hε
    hbox rows oldMask hs0 mask hmaskN hN exceptional N families j
  simpa only [Cf, pow_zero, mul_one] using hf

end HeckeSkeleton.Moments.EngineStep.InternalMassAssembly

#print axioms HeckeSkeleton.Moments.EngineStep.InternalMassAssembly.actual_direct_source_image_kernel_mass
#print axioms HeckeSkeleton.Moments.EngineStep.InternalMassAssembly.actual_amplified_source_image_kernel_mass
