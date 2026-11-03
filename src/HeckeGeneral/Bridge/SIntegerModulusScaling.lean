import HeckeGeneral.Bridge.SIntegerScaledPoisson
import HeckeGeneral.Arithmetic.SIntegerOrbitNorm

/-! Dividing an actual principal frequency by a nonzero S-integer is the
same as multiplying its original S-local base point by the inverse local
diagonal. This statement concerns the archimedean and original S coordinates;
it does not identify the assembled ideles outside S. -/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
  NumberField.AdelicFourier NumberField.StandardAddChar
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "G" => sLocalMultiplicativeGroup K (S : Set (HeightOneSpectrum (𝓞 K)))

variable (c : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) (hc : c ≠ 0)

include c hc

/-- The equality holds even when the numerator is zero. -/
theorem sLocalScaledPrincipal_div_modulus_arch (p : G) (a : K) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K
        (sLocalScaledPrincipal K S p (a / (c : K))).1 =
      InfiniteAdeleRing.ringEquiv_mixedSpace K
        (sLocalScaledPrincipal K S
          (p * (sLocalNonzeroIntegerDiagonal K (S : Set (HeightOneSpectrum (𝓞 K)))
            ⟨c, hc⟩)⁻¹) a).1 := by
  rw [sLocalScaledPrincipal_arch, sLocalScaledPrincipal_arch]
  change p.1.val * mixedEmbedding K (a / (c : K)) =
    (p.1.val * mixedEmbedding K ((c : K)⁻¹)) * mixedEmbedding K a
  rw [div_eq_mul_inv, map_mul]
  ac_rfl

theorem sLocalScaledPrincipal_div_modulus_finite (p : G) (a : K)
    (v : (S : Set (HeightOneSpectrum (𝓞 K)))) :
    (sLocalScaledPrincipal K S p (a / (c : K))).2 v.val =
      (sLocalScaledPrincipal K S
        (p * (sLocalNonzeroIntegerDiagonal K (S : Set (HeightOneSpectrum (𝓞 K)))
          ⟨c, hc⟩)⁻¹) a).2 v.val := by
  rw [sLocalScaledPrincipal_finite_mem, sLocalScaledPrincipal_finite_mem]
  change (p.2 v).val * algebraMap K (v.val.adicCompletion K) (a / (c : K)) =
    ((p.2 v).val * algebraMap K (v.val.adicCompletion K) ((c : K)⁻¹)) *
      algebraMap K (v.val.adicCompletion K) a
  rw [div_eq_mul_inv, map_mul]
  ac_rfl

theorem sLocalProductNorm_div_modulus (p : G) :
    sLocalProductNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (p * (sLocalNonzeroIntegerDiagonal K (S : Set (HeightOneSpectrum (𝓞 K)))
          ⟨c, hc⟩)⁻¹) =
      sLocalProductNorm K (S : Set (HeightOneSpectrum (𝓞 K))) p /
        (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val := by
  have hinv := congrArg (fun z : ℝˣ => (z : ℝ))
    (map_inv (sLocalProductNormHom K (S : Set (HeightOneSpectrum (𝓞 K))))
      (sLocalNonzeroIntegerDiagonal K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩))
  rw [sLocalProductNorm_mul]
  change sLocalProductNorm K _ p *
    sLocalProductNorm K _ (sLocalNonzeroIntegerDiagonal K _ ⟨c, hc⟩)⁻¹ = _
  rw [show sLocalProductNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sLocalNonzeroIntegerDiagonal K _ ⟨c, hc⟩)⁻¹ =
      (sLocalProductNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sLocalNonzeroIntegerDiagonal K _ ⟨c, hc⟩))⁻¹ from hinv]
  rfl

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))

/-- Only the Fourier tensor's actual local coordinates are changed. -/
theorem sIntegerScaledDualTensorTerm_div_modulus
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) (p : G) (a : K) :
    sIntegerScaledDualTensorTerm K S μv φ h p (a / (c : K)) =
      sIntegerScaledDualTensorTerm K S μv φ h
        (p * (sLocalNonzeroIntegerDiagonal K (S : Set (HeightOneSpectrum (𝓞 K)))
          ⟨c, hc⟩)⁻¹) a := by
  have harch := congrArg
    (fourierIntegral (standardMixedAddCharacter K) volume φ)
    (sLocalScaledPrincipal_div_modulus_arch K S c hc p a)
  have hfinite :
      sIntegerLocalFourierProduct K μv S h
          (sLocalScaledPrincipal K S p (a / (c : K))).2 =
        sIntegerLocalFourierProduct K μv S h
          (sLocalScaledPrincipal K S
            (p * (sLocalNonzeroIntegerDiagonal K
              (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩)⁻¹) a).2 := by
    unfold sIntegerLocalFourierProduct
    apply Finset.prod_congr rfl
    intro v hv
    exact congrArg (fun z : v.adicCompletion K =>
      ((μv v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ)⁻¹ *
        fourierIntegral (psiLocal K v) (μv v) (h v) z)
      (sLocalScaledPrincipal_div_modulus_finite K S c hc p a ⟨v, hv⟩)
  exact congrArg₂ (fun x y : ℂ => x * y) harch hfinite

end HeckeGeneral.Bridge
