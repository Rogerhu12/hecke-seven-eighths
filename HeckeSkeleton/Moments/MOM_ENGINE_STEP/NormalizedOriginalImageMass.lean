import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalAmplifiedCarrier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedRectangleFibres
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedIndexedKernelMass

/-!
# The original arithmetic image controls the same normalized kernels

The index below is the existing original image map composed with the
actual active-family projection. Both independent divisors and both
complete occurrence allocations are retained, together with the
original amplifier prime and valuation in the amplified case.

These are internal assembly lemmas. The source-fibre estimate is the
physical covered-source theorem, and the pointwise scalar estimate is
the original-window arithmetic theorem. Neither a new arithmetic carrier
nor a total normalized-kernel mass is an input. The four centered
rectangles cost exactly the universal factor four in the fibre bound.
All Fourier seminorms and constants are chosen before the moving source
type, profiles, scale, family or arithmetic projections.
-/

noncomputable section
open DedekindZetaZeroFree.LocalFiniteSums (ExteriorPrime)
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open CommonSupportMass
open ActualNormalizedPairFamily

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}

namespace OriginalArithmeticLabels

variable {I V : Type*} [Fintype I] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {cap : ℕ} {Z : ℝ}
variable (L : OriginalArithmeticLabels K I cap)
variable (families : I → ActualNormalizedPairFamily A σ V (Bool × Bool) ω ψ Z)

/-- This is the literal original direct index of the retained leaf.
The rectangle only selects one of its already chosen child pairs. -/
def rectangleIndex (b : (combine families).active Finset.univ) : L.carrier.Index :=
  L.index (activeCombineEquiv families b).1

@[simp] theorem rectangleIndex_allocation (b : (combine families).active Finset.univ) :
    L.indexAllocation (L.rectangleIndex families b) =
      L.allocation (activeCombineEquiv families b).1 := rfl

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable (pool : PowerScaleExteriorPool A bad Z ell eps)
variable (tag : I → Option (ℕ × ExteriorPrime A))
variable (tag_mem : ∀ i n p, tag i = some (n, p) →
  n ∈ ({1, 6, 7} : Finset ℕ) ∧ p ∈ pool.primes)

/-- The same map in the amplified case keeps its original tag, prime,
valuation, divisors and allocation functions. -/
def rectangleAmplifiedIndex (b : (combine families).active Finset.univ) :
    AmplifiedCommonIndex pool (L.mainCarrier tag) (L.errorCarrier tag) :=
  L.amplifiedIndex tag pool tag_mem (activeCombineEquiv families b).1

@[simp] theorem rectangleAmplifiedIndex_tag
    (b : (combine families).active Finset.univ) :
    L.amplifiedTag tag pool (L.rectangleAmplifiedIndex families pool tag tag_mem b) =
      tag (activeCombineEquiv families b).1 :=
  L.amplifiedIndex_tag tag pool tag_mem _

@[simp] theorem rectangleAmplifiedIndex_allocation
    (b : (combine families).active Finset.univ) :
    L.amplifiedAllocation tag pool
        (L.rectangleAmplifiedIndex families pool tag tag_mem b) =
      L.allocation (activeCombineEquiv families b).1 :=
  L.amplifiedIndex_allocation tag pool tag_mem _

end OriginalArithmeticLabels

namespace InternalMassAssembly

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]

/-- The direct image is built from the original projections. Its
admissibility is proved here from individual original support and norm
windows. The supplied physical-source fibre is lifted to the actual
active rectangles inside the proof. -/
theorem original_direct_image_kernel_mass
    (cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight dFiber : ℕ)
    (normBox ε Cweight Cfiber : ℝ)
    (hbox : 0 ≤ normBox) (hε : 0 < ε)
    (hCweight : 0 < Cweight) (hCfiber : 0 < Cfiber) :
    ∃ seminorms₁ seminorms₂ : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ {I : Type*} [Fintype I] (Z : ℝ), 1 < Z → ∀ profile : ℝ, 1 ≤ profile →
    ∀ (L : OriginalArithmeticLabels K I cap)
      (families : I → ActualNormalizedPairFamily A σ (WithLp 2 (U × E))
        (Bool × Bool) ω ψ Z)
      (F₁ : I × (Bool × Bool) → 𝓢(U, ℂ))
      (F₂ : I × (Bool × Bool) → 𝓢(E, ℂ))
      (outer B₁ B₂ : I × (Bool × Bool) → ℝ) (parentWidth : ℝ),
    ProfileWindows (combine families) Finset.univ F₁ F₂ outer B₁ B₂ profile
      cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ seminorms₁ seminorms₂ →
    ∀ oldMask : Ideal (𝓞 K), Squarefree oldMask → oldMask ≠ 0 →
      (∀ i, Valid oldMask (L.first i)) →
      (∀ i, (Ideal.absNorm (L.first i).1.1 : ℝ) ≤ Z ^ normBox ∧
        (Ideal.absNorm (L.first i).1.2 : ℝ) ≤ Z ^ normBox) →
      (∀ i, Squarefree (L.firstDivisor i) ∧ L.firstDivisor i ≠ 0) →
      (∀ i, (Ideal.absNorm (L.firstDivisor i) : ℝ) ≤ Z ^ normBox) →
      (∀ i, Valid (L.firstDivisor i) (L.second i)) →
      (∀ i, (Ideal.absNorm (L.second i).1.1 : ℝ) ≤ Z ^ normBox ∧
        (Ideal.absNorm (L.second i).1.2 : ℝ) ≤ Z ^ normBox) →
      (∀ i, (L.allocation i).1 ≠ 0) →
      (∀ i, (Ideal.absNorm (L.allocation i).1 : ℝ) ≤ Z ^ normBox) →
      (∀ b : (combine families).active Finset.univ,
        outer b.val * (combine families).weight Finset.univ parentWidth b ≤
          (Cweight * profile ^ dWeight * Z ^ (ε / 4)) *
            L.carrier.indexWeight (L.rectangleIndex families b)) →
      (∀ j, ((Finset.univ.filter (fun i => L.index i = j)).card : ℝ) ≤
        Cfiber * profile ^ dFiber * Z ^ (ε / 4)) →
      (∀ b : (combine families).active Finset.univ,
        IsFiniteMeasure ((combine families).kernel Finset.univ
          (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b)) ∧
      (∑ b : (combine families).active Finset.univ,
        ((combine families).kernel Finset.univ
          (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b).real Set.univ) ≤
          C * profile ^ totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight dFiber * Z ^ ε := by
  obtain ⟨seminorms₁, seminorms₂, C, hC, hm⟩ :=
    direct_kernel_mass_of_pointwise_index (A := A) (σ := σ) (ω := ω) (ψ := ψ)
      (U := U) (E := E) cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight dFiber
      (cap + 2) normBox ε Cweight (4 * Cfiber) hbox hε hCweight (by positivity)
  refine ⟨seminorms₁, seminorms₂, C, hC, ?_⟩
  intro I inst Z hZ profile hprofile L families F₁ F₂ outer B₁ B₂ parentWidth windows
    oldMask hs hs0 hf hfN hS hSN hw hwN hD hDN hweight hfibre
  have hadmissible := L.carrier_admissible normBox Z oldMask
    hf hfN hS hSN hw hwN hD hDN
  apply hm Z hZ profile hprofile (combine families) Finset.univ
    F₁ F₂ outer B₁ B₂ parentWidth windows oldMask hs hs0
    L.carrier hadmissible (L.rectangleIndex families) hweight
  intro j
  have hfour := activeCombine_rectangle_fibre_le families L.index j
    (Cfiber * profile ^ dFiber * Z ^ (ε / 4)) (hfibre j)
  simpa only [OriginalArithmeticLabels.rectangleIndex, mul_assoc] using hfour

/-- The amplified image uses the original prime and valuation tag. Its
moving norm is already inside amplifiedIndexWeight, so the pointwise
small exponent is only the remaining original-window error. -/
theorem original_amplified_image_kernel_mass
    (cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight dFiber : ℕ)
    (normBox ε Cweight Cfiber ell eps Mmax Bmax : ℝ)
    (hbox : 0 ≤ normBox) (hε : 0 < ε)
    (hCweight : 0 < Cweight) (hCfiber : 0 < Cfiber)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell) (hepsε : eps ≤ ε / 4)
    (hMmax : 0 ≤ Mmax) (hBmax : 0 ≤ Bmax) :
    ∃ seminorms₁ seminorms₂ : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 0 < C ∧ 1 < Z₀ ∧
    ∀ {I : Type*} [Fintype I] (Z : ℝ), Z₀ ≤ Z → ∀ profile : ℝ, 1 ≤ profile →
    ∀ (L : OriginalArithmeticLabels K I cap)
      (families : I → ActualNormalizedPairFamily A σ (WithLp 2 (U × E))
        (Bool × Bool) ω ψ Z)
      (F₁ : I × (Bool × Bool) → 𝓢(U, ℂ))
      (F₂ : I × (Bool × Bool) → 𝓢(E, ℂ))
      (outer B₁ B₂ : I × (Bool × Bool) → ℝ) (parentWidth : ℝ),
    ProfileWindows (combine families) Finset.univ F₁ F₂ outer B₁ B₂ profile
      cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ seminorms₁ seminorms₂ →
    ∀ bad : Finset (HeightOneSpectrum (𝓞 K)),
    ∀ pool : PowerScaleExteriorPool A bad Z ell eps,
    ∀ (tag : I → Option (ℕ × ExteriorPrime A))
      (tag_mem : ∀ i n p, tag i = some (n, p) →
        n ∈ ({1, 6, 7} : Finset ℕ) ∧ p ∈ pool.primes),
    ∀ M B : ℝ, 0 ≤ M → M ≤ Mmax → B ≤ Bmax →
    ∀ oldMask : Ideal (𝓞 K), Squarefree oldMask → oldMask ≠ 0 →
      (∀ i, Valid oldMask (L.first i)) →
      (∀ i, (Ideal.absNorm (L.first i).1.1 : ℝ) ≤ Z ^ normBox ∧
        (Ideal.absNorm (L.first i).1.2 : ℝ) ≤ Z ^ normBox) →
      (∀ i, Squarefree (L.firstDivisor i) ∧ L.firstDivisor i ≠ 0) →
      (∀ i, (Ideal.absNorm (L.firstDivisor i) : ℝ) ≤ Z ^ normBox) →
      (∀ i, Valid (L.firstDivisor i) (L.second i)) →
      (∀ i, (Ideal.absNorm (L.second i).1.1 : ℝ) ≤ Z ^ normBox ∧
        (Ideal.absNorm (L.second i).1.2 : ℝ) ≤ Z ^ normBox) →
      (∀ i, (L.allocation i).1 ≠ 0) →
      (∀ i, (Ideal.absNorm (L.allocation i).1 : ℝ) ≤ Z ^ normBox) →
      (∀ b : (combine families).active Finset.univ,
        outer b.val * (combine families).weight Finset.univ parentWidth b ≤
          (Cweight * profile ^ dWeight * Z ^ (ε / 4)) *
            amplifiedIndexWeight pool M B (L.mainCarrier tag) (L.errorCarrier tag)
              (L.rectangleAmplifiedIndex families pool tag tag_mem b)) →
      (∀ j, ((Finset.univ.filter (fun i => L.amplifiedIndex tag pool tag_mem i = j)).card : ℝ) ≤
        Cfiber * profile ^ dFiber * Z ^ (ε / 4)) →
      (∀ b : (combine families).active Finset.univ,
        IsFiniteMeasure ((combine families).kernel Finset.univ
          (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b)) ∧
      (∑ b : (combine families).active Finset.univ,
        ((combine families).kernel Finset.univ
          (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b).real Set.univ) ≤
          C * profile ^ totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight dFiber * Z ^ ε := by
  obtain ⟨seminorms₁, seminorms₂, C, Z₀, hC, hZ₀, hm⟩ :=
    amplified_kernel_mass_of_pointwise_index (A := A) (σ := σ) (ω := ω) (ψ := ψ)
      (U := U) (E := E) cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight dFiber
      (cap + 2) normBox ε Cweight (4 * Cfiber) ell eps Mmax Bmax hbox hε hCweight
      (by positivity) hell heps hepsell hepsε hMmax hBmax
  refine ⟨seminorms₁, seminorms₂, C, Z₀, hC, hZ₀, ?_⟩
  intro I inst Z hZ profile hprofile L families F₁ F₂ outer B₁ B₂ parentWidth windows
    bad pool tag tag_mem M B hM hMM hBB oldMask hs hs0
    hf hfN hS hSN hw hwN hD hDN hweight hfibre
  have hadmissible := L.amplified_carriers_admissible tag normBox Z oldMask
    hf hfN hS hSN hw hwN hD hDN
  apply hm Z hZ profile hprofile (combine families) Finset.univ
    F₁ F₂ outer B₁ B₂ parentWidth windows bad pool M B hM hMM hBB oldMask hs hs0
    (L.mainCarrier tag) hadmissible.1 (L.errorCarrier tag)
    (fun n _ p _ => hadmissible.2 n p)
    (L.rectangleAmplifiedIndex families pool tag tag_mem) hweight
  intro j
  have hfour := activeCombine_rectangle_fibre_le families
    (L.amplifiedIndex tag pool tag_mem) j
    (Cfiber * profile ^ dFiber * Z ^ (ε / 4)) (hfibre j)
  simpa only [OriginalArithmeticLabels.rectangleAmplifiedIndex, mul_assoc] using hfour

end InternalMassAssembly
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.rectangleAmplifiedIndex_allocation
#print axioms HeckeSkeleton.Moments.EngineStep.InternalMassAssembly.original_direct_image_kernel_mass
#print axioms HeckeSkeleton.Moments.EngineStep.InternalMassAssembly.original_amplified_image_kernel_mass
