import HeckeSkeleton.HighBinSupport.ActualBoundaryIntegrability
import HeckeSkeleton.HighBinSupport.ActualKernelEnvelope
import HeckeSkeleton.HighBinSupport.BoundaryTailAssembly
/-!
Transport of the original `rowContourBox`, with its original normalization.

This module applies the rectangle theorem to the literal compensated kernel.
Its analytic premises concern only the marked correction product. The
deleted L denominator is treated with the actual upper-zero detector, and
all finite-box integrability is derived from the actual factors. The last
theorem converts a pointwise marked-Euler estimate into arbitrary-order
external-height decay; it does not assume a contour estimate.
-/

set_option autoImplicit false
noncomputable section

namespace HighBinBoundary.ActualContour

open NumberField IsDedekindDomain MeasureTheory Set Complex
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : (S : Set (HeightOneSpectrum (𝓞 K)))) → Measure (p.val.adicCompletion K))
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), (μ p).IsAddHaarMeasure]

/-- Merely group the two unchanged height coordinates of the actual kernel. -/
def rowKernel (P : ProbeData K S₀) (ψ : HeckeCharacter K)
    (E : RowEulerData K S₀ P) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S₀)
    (Z ν : ℝ) (s : ℂ) (q : ℝ × ℝ) : ℂ :=
  compensatedRowMellinKernel K S₀ μ P ψ E g T u Z s
    ((ν : ℂ) + q.1 * I) ((17 / 50 : ℂ) + q.2 * I)

theorem twoHeightMeasure_ae_mem (H : ℝ) :
    ∀ᵐ q ∂twoHeightMeasure H,
      q ∈ Icc (-H) H ×ˢ Icc (-H) H := by
  simpa only [twoHeightMeasure, Measure.prod_restrict] using
    (ae_restrict_mem (μ := (volume : Measure (ℝ × ℝ)))
      (measurableSet_Icc.prod measurableSet_Icc))

/-- Exact Fubini identification, including the (2π)^(-3) normalization. -/
theorem rowContourBox_eq_parameterBox
    (P : ProbeData K S₀) (ψ : HeckeCharacter K) (E : RowEulerData K S₀ P)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S₀) (Z H σ ν : ℝ) (hH : 0 ≤ H)
    (hi : Integrable (fun p : ℝ × (ℝ × ℝ) =>
      rowKernel K S μ P ψ E g T u Z ν ((σ : ℂ) + p.1 * I) p.2)
      ((volume.restrict (Icc (-H) H)).prod (twoHeightMeasure H))) :
    rowContourBox K S₀ μ P ψ E g T u Z H σ ν (17 / 50) =
      (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) *
        parameterBox (twoHeightMeasure H) (rowKernel K S μ P ψ E g T u Z ν) σ H := by
  rw [parameterBox_eq_nested_Icc _ σ H hH hi]
  simp only [rowContourBox, rowKernel, Complex.ofReal_div, Complex.ofReal_ofNat]

/-- The actual row box is integrable on either vertical face as soon as
the actual correction product is continuous there. -/
theorem rowKernel_integrable_heightBox
    (P : ProbeData K S₀) (ψ : HeckeCharacter K) (E : RowEulerData K S₀ P)
    (g : PrimeWindowGeometry) (T Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ)
    (u : FrequencyRow K S₀)
    (hχ : ∀ t : ℝ, E.rows.character u ≠ heckeNormTwist K t)
    (hβ : ∀ t : ℝ, ψ * conjugate (E.rows.character u) ≠ heckeNormTwist K t)
    (Z H U α σ ν : ℝ) (hZ : 0 < Z) (hHU : H ≤ U)
    (hα : 1 / 2 ≤ α) (hσ : α < σ)
    (hbelow : rowZeroBelow K S₀ ψ Θ P E u U α)
    (hcorr : ∀ Q : Finset (ExteriorPrime K S₀),
      ContinuousOn (fun q => rowCorrection K S₀ P ψ E Q u
        (ActualIntegrability.sLine σ q) (ActualIntegrability.wLine ν q)
        (ActualIntegrability.zLine q)) (ActualIntegrability.heightBox H)) :
    Integrable (fun p : ℝ × (ℝ × ℝ) =>
      rowKernel K S μ P ψ E g T u Z ν ((σ : ℂ) + p.1 * I) p.2)
      ((volume.restrict (Icc (-H) H)).prod (twoHeightMeasure H)) := by
  simpa only [rowKernel, ActualIntegrability.sLine, ActualIntegrability.wLine,
    ActualIntegrability.zLine] using
    ActualIntegrability.compensatedRowMellinKernel_integrable_heightBox
      K S μ P ψ E g T Θ hΘ u hχ hβ H U α σ ν Z hHU hα hσ hZ hbelow hcorr

/-- All L-denominator nonvanishing on the rectangle follows from the
actual detector. The only remaining s-holomorphy premise is for rowCorrection. -/
theorem rowKernel_differentiableOn_rectangle
    (P : ProbeData K S₀) (ψ : HeckeCharacter K) (E : RowEulerData K S₀ P)
    (g : PrimeWindowGeometry) (T Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ)
    (u : FrequencyRow K S₀)
    (hβ : ∀ t : ℝ, ψ * conjugate (E.rows.character u) ≠ heckeNormTwist K t)
    (Z H U α l r ν : ℝ) (hZ : 0 < Z) (hH : 0 ≤ H) (hHU : H ≤ U)
    (hα : 1 / 2 ≤ α) (hl : α < l) (hlr : l ≤ r)
    (hbelow : rowZeroBelow K S₀ ψ Θ P E u U α)
    (q : ℝ × ℝ)
    (hcorr : ∀ s ∈ Icc l r ×ℂ Icc (-H) H,
      ∀ Q : Finset (ExteriorPrime K S₀),
        DifferentiableAt ℂ (fun s => rowCorrection K S₀ P ψ E Q u s
          ((ν : ℂ) + q.1 * I) ((17 / 50 : ℂ) + q.2 * I)) s) :
    DifferentiableOn ℂ (fun s => rowKernel K S μ P ψ E g T u Z ν s q)
      (uIcc l r ×ℂ uIcc (-H) H) := by
  rw [uIcc_of_le hlr, uIcc_of_le (show -H ≤ H by linarith)]
  intro s hs
  have hsα : α < s.re := hl.trans_le hs.1.1
  have hsi : |s.im| ≤ U := (abs_le.mpr hs.2).trans hHU
  exact (ActualHolomorphy.compensatedRowMellinKernel_differentiableAt_s
    K S₀ μ P ψ E g T Θ hΘ u hβ U α hα hbelow Z hZ s
    ((ν : ℂ) + q.1 * I) ((17 / 50 : ℂ) + q.2 * I) hsα hsi
    (hcorr s hs)).differentiableWithinAt

/-- The original-minus-final row contour equals the two horizontal faces.
The frequency row and every finite prime subset remain fixed throughout. -/
theorem rowContourBox_rectangle_identity
    (P : ProbeData K S₀) (ψ : HeckeCharacter K) (E : RowEulerData K S₀ P)
    (g : PrimeWindowGeometry) (T Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ)
    (u : FrequencyRow K S₀)
    (hχ : ∀ t : ℝ, E.rows.character u ≠ heckeNormTwist K t)
    (hβ : ∀ t : ℝ, ψ * conjugate (E.rows.character u) ≠ heckeNormTwist K t)
    (Z H U α l r ν : ℝ) (hZ : 0 < Z) (hH : 0 ≤ H) (hHU : H ≤ U)
    (hα : 1 / 2 ≤ α) (hl : α < l) (hlr : l ≤ r)
    (hbelow : rowZeroBelow K S₀ ψ Θ P E u U α)
    (hcorrC : ∀ σ ∈ ({l, r} : Finset ℝ), ∀ Q : Finset (ExteriorPrime K S₀),
      ContinuousOn (fun q => rowCorrection K S₀ P ψ E Q u
        (ActualIntegrability.sLine σ q) (ActualIntegrability.wLine ν q)
        (ActualIntegrability.zLine q)) (ActualIntegrability.heightBox H))
    (hcorrD : ∀ q ∈ Icc (-H) H ×ˢ Icc (-H) H,
      ∀ s ∈ Icc l r ×ℂ Icc (-H) H, ∀ Q : Finset (ExteriorPrime K S₀),
        DifferentiableAt ℂ (fun s => rowCorrection K S₀ P ψ E Q u s
          ((ν : ℂ) + q.1 * I) ((17 / 50 : ℂ) + q.2 * I)) s) :
    rowContourBox K S₀ μ P ψ E g T u Z H r ν (17 / 50) -
      rowContourBox K S₀ μ P ψ E g T u Z H l ν (17 / 50) =
        (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) *
          ∫ q : ℝ × ℝ, I *
            ((∫ x : ℝ in l..r, rowKernel K S μ P ψ E g T u Z ν
                ((x : ℂ) + (-H) * I) q) -
              (∫ x : ℝ in l..r, rowKernel K S μ P ψ E g T u Z ν
                ((x : ℂ) + H * I) q)) ∂twoHeightMeasure H := by
  have hli := rowKernel_integrable_heightBox K S μ P ψ E g T Θ hΘ u hχ hβ
    Z H U α l ν hZ hHU hα hl hbelow (hcorrC l (by simp))
  have hri := rowKernel_integrable_heightBox K S μ P ψ E g T Θ hΘ u hχ hβ
    Z H U α r ν hZ hHU hα (hl.trans_le hlr) hbelow (hcorrC r (by simp))
  have hF : ∀ᵐ q ∂twoHeightMeasure H,
      DifferentiableOn ℂ (fun s => rowKernel K S μ P ψ E g T u Z ν s q)
        (uIcc l r ×ℂ uIcc (-H) H) := by
    filter_upwards [twoHeightMeasure_ae_mem H] with q hq
    exact rowKernel_differentiableOn_rectangle K S μ P ψ E g T Θ hΘ u hβ
      Z H U α l r ν hZ hH hHU hα hl hlr hbelow q (hcorrD q hq)
  rw [rowContourBox_eq_parameterBox K S μ P ψ E g T u Z H r ν hH hri,
    rowContourBox_eq_parameterBox K S μ P ψ E g T u Z H l ν hH hli, ← mul_sub]
  congr 1
  apply parameter_rectangle_identity _ _ l r H hH _ _ hF
  · simpa only [restrict_Ioc_eq_restrict_Icc] using hli
  · simpa only [restrict_Ioc_eq_restrict_Icc] using hri

#print axioms rowContourBox_eq_parameterBox
#print axioms rowKernel_integrable_heightBox
#print axioms rowKernel_differentiableOn_rectangle
#print axioms rowContourBox_rectangle_identity

/-- A pointwise bound for the actual marked Euler continuations on the
horizontal faces gives a tail of every order for the literal row contour.
The scale exponent is the fixed number 5, independent of the tail order.
The later arithmetic row and retained-block summation must still supply
one polynomial bound for their corresponding M values. -/
theorem exists_rowContourBox_external_tail
    (P : ProbeData K S₀) (g : PrimeWindowGeometry) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ψ : HeckeCharacter K) (E : RowEulerData K S₀ P)
        (T Θ : Finset (HeckeCharacter K)), 1 ∈ Θ →
      ∀ u : FrequencyRow K S₀,
      (∀ t : ℝ, E.rows.character u ≠ heckeNormTwist K t) →
      (∀ t : ℝ, ψ * conjugate (E.rows.character u) ≠ heckeNormTwist K t) →
      ∀ Z H U α l r ν Text : ℝ,
      1 ≤ Z → 1 ≤ Text → Text ≤ H → H ≤ U → 1 / 2 ≤ α → α < l → l ≤ r →
      1 / 2 ≤ l → r ≤ 2 → -1 ≤ ν → ν ≤ 1 →
      rowZeroBelow K S₀ ψ Θ P E u U α →
      (∀ σ ∈ ({l, r} : Finset ℝ), ∀ Q : Finset (ExteriorPrime K S₀),
        ContinuousOn (fun q => rowCorrection K S₀ P ψ E Q u
          (ActualIntegrability.sLine σ q) (ActualIntegrability.wLine ν q)
          (ActualIntegrability.zLine q)) (ActualIntegrability.heightBox H)) →
      (∀ q ∈ Icc (-H) H ×ˢ Icc (-H) H,
        ∀ s ∈ Icc l r ×ℂ Icc (-H) H, ∀ Q : Finset (ExteriorPrime K S₀),
          DifferentiableAt ℂ (fun s => rowCorrection K S₀ P ψ E Q u s
            ((ν : ℂ) + q.1 * I) ((17 / 50 : ℂ) + q.2 * I)) s) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ σ ∈ Icc l r, ∀ q ∈ Icc (-H) H ×ˢ Icc (-H) H,
        ∀ x : ℝ, |x| = H →
        ∀ p ∈ Fintype.piFinset (fun i => primeWindow K S₀ g T Z i),
          ∀ Q : Finset (ExteriorPrime K S₀), Q ⊆ Finset.univ.image p →
            ‖rowEulerContinuation K S₀ P ψ E Q u ((σ : ℂ) + x * I)
              ((ν : ℂ) + q.1 * I) ((17 / 50 : ℂ) + q.2 * I)‖ ≤ M) →
      ‖rowContourBox K S₀ μ P ψ E g T u Z H r ν (17 / 50) -
        rowContourBox K S₀ μ P ψ E g T u Z H l ν (17 / 50)‖ ≤
          C * Z ^ 5 * M * |r - l| * Text ^ (-(N : ℝ)) := by
  letI : IsTotallyComplex K :=
    ⟨HeckeSkeleton.HeckeFiniteBackgroundControl.all_complex_of_primitive12
      K P.arithmetic.primitive12⟩
  obtain ⟨C₀, hC₀, henv⟩ := ActualKernel.exists_compensated_kernel_envelope K S₀ μ P g
  obtain ⟨D, hD, hprof⟩ := ActualAdditiveBorel.exists_additiveMellin_rapid_bound_actualBorel
    K S (fun p => inferInstance) (fun p => inferInstance) μ (fun p => inferInstance)
    P.additive (17 / 50) (by norm_num) (by norm_num) (N + 2)
  let A : ℝ := ‖(2 * (Real.pi : ℂ)) ^ (-(3 : ℤ))‖ + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hG : 0 < gaussianMoment (N + 2) := gaussianMoment_pos _
  refine ⟨8 * A * C₀ * gaussianMoment (N + 2) * D,
    by positivity, ?_⟩
  intro ψ E T Θ hΘ u hχ hβ Z H U α l r ν Text hZ hT hTH hHU hα hl hlr
    hl0 hr2 hν0 hν1 hbelow hcorrC hcorrD M hM hrow
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hH : 0 ≤ H := by linarith
  have hli := rowKernel_integrable_heightBox K S μ P ψ E g T Θ hΘ u hχ hβ
    Z H U α l ν hZpos hHU hα hl hbelow (hcorrC l (by simp))
  have hri := rowKernel_integrable_heightBox K S μ P ψ E g T Θ hΘ u hχ hβ
    Z H U α r ν hZpos hHU hα (hl.trans_le hlr) hbelow (hcorrC r (by simp))
  have hF : ∀ᵐ q ∂twoHeightMeasure H,
      DifferentiableOn ℂ (fun s => rowKernel K S μ P ψ E g T u Z ν s q)
        (uIcc l r ×ℂ uIcc (-H) H) := by
    filter_upwards [twoHeightMeasure_ae_mem H] with q hq
    exact rowKernel_differentiableOn_rectangle K S μ P ψ E g T Θ hΘ u hβ
      Z H U α l r ν hZpos hH hHU hα hl hlr hbelow q (hcorrD q hq)
  have hkernel : ∀ᵐ q ∂twoHeightMeasure H, ∀ σ ∈ uIcc l r,
      ∀ x : ℝ, |x| = H →
      ‖rowKernel K S μ P ψ E g T u Z ν ((σ : ℂ) + x * I) q‖ ≤
        (C₀ * Z ^ 5 * M) *
          (Real.exp (-((x + q.2) ^ 2)) *
            ‖additiveMellin K S₀ μ P.additive ((17 / 50 : ℂ) + q.2 * I)‖) := by
    filter_upwards [twoHeightMeasure_ae_mem H] with q hq
    intro σ hσ x hx
    rw [uIcc_of_le hlr] at hσ
    have h := henv ψ E T u Z hZ ((σ : ℂ) + x * I)
      ((ν : ℂ) + q.1 * I) ((17 / 50 : ℂ) + q.2 * I)
      (by simpa using hl0.trans hσ.1) (by simpa using hσ.2.trans hr2)
      (by simpa using hν0) (by simpa using hν1) (by simp) M hM
      (hrow σ hσ q hq x hx)
    simpa [rowKernel, Complex.add_im, Complex.mul_im, Complex.div_im] using h
  have hbound := coupled_box_external_tail
    (rowKernel K S μ P ψ E g T u Z ν)
    (fun t => additiveMellin K S₀ μ P.additive ((17 / 50 : ℂ) + t * I))
    N l r H Text (C₀ * Z ^ 5 * M) D hT hTH (by positivity)
    (by simpa only [restrict_Ioc_eq_restrict_Icc] using hli)
    (by simpa only [restrict_Ioc_eq_restrict_Icc] using hri) hF hprof hkernel
  rw [rowContourBox_eq_parameterBox K S μ P ψ E g T u Z H r ν hH hri,
    rowContourBox_eq_parameterBox K S μ P ψ E g T u Z H l ν hH hli,
    ← mul_sub, norm_mul]
  calc
    _ ≤ A * (8 * (C₀ * Z ^ 5 * M) * gaussianMoment (N + 2) * D *
        |r - l| * Text ^ (-(N : ℝ))) :=
      mul_le_mul (by dsimp [A]; linarith) hbound (norm_nonneg _) hA.le
    _ = _ := by ring

#print axioms exists_rowContourBox_external_tail

end HighBinBoundary.ActualContour
