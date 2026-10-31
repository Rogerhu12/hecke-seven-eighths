import ActualThetaGeneratorDivision
import ActualProbeGaussOriginalFourier
import SIntegerSexticPIDFullFactorization
import SIntegerSexticFullCorrelationSupport

/-!
UNCOMPILED / native 0. Natural exterior ideal factorizations I=C*N1 and
J=C*N2 supply literal quotient generators n1=gen(I)/gen(C), n2=gen(J)/gen(C).
Their actual general units are retained. Coprimality of the residual ideals
implies literal element coprimality and supplies Bezout data; no PID or
chosen-generator multiplicativity is assumed. The full original correlation
vanishes off C and factors at gen(C)*k for every k, including zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain
open scoped Classical

theorem sIntegerSexticFiniteCorrelation_ideal_congr (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (ζ : K) (hζ : IsPrimitiveRoot ζ 6)
    (σ : K →+* ℂ) {I I' : Ideal (𝓞 K)} (h : I = I') (hI : I ≠ 0) (hI' : I' ≠ 0)
    (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S)
    (hS' : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I' → p ∉ S)
    (h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → (6 : 𝓞 K) ∉ p.asIdeal)
    (h6' : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I' → (6 : 𝓞 K) ∉ p.asIdeal)
    (x y k : S.integer K) :
    sIntegerSexticFiniteCorrelation K S ζ hζ σ I hI hS h6
        (Ideal.Quotient.mk _ x) (Ideal.Quotient.mk _ y) (Ideal.Quotient.mk _ k) =
      sIntegerSexticFiniteCorrelation K S ζ hζ σ I' hI' hS' h6'
        (Ideal.Quotient.mk _ x) (Ideal.Quotient.mk _ y) (Ideal.Quotient.mk _ k) := by
  subst h
  rfl

end HeckeGeneral.Characters

namespace HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualProbeGaussFourierDraft
open scoped Classical ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local notation "OS" => S.integer K
local notation "NZ" => NonzeroRingElements OS
local notation "χ" => sIntegerSexticSymbol K S D.root6 D.primitive6 D.embedding
  (probeArithmetic_six_support K S D)

/-- Residual ideal coprimality implies coprimality of the actual literal
quotient generators, including their independent general unit factors. -/
theorem thetaGeneratorDivision_isCoprime
    (C N₁ N₂ I J : ExteriorIdeal K S)
    (hI : I = exteriorMul K S C N₁) (hJ : J = exteriorMul K S C N₂)
    (hcop : IsCoprime N₁.val.val N₂.val.val) :
    IsCoprime (thetaGeneratorDivision K S D C N₁ I hI).val
      (thetaGeneratorDivision K S D C N₂ J hJ).val := by
  apply (Ideal.sup_eq_top_iff_isCoprime _ _).mp
  rw [thetaGeneratorDivision_span, thetaGeneratorDivision_span,
    ← Ideal.map_sup, hcop.sup_eq, Ideal.map_top]

/-- Actual Bezout data in the precise orientation used by the existing
full-correlation factorization theorem. -/
theorem exists_thetaGeneratorDivision_bezout
    (C N₁ N₂ I J : ExteriorIdeal K S)
    (hI : I = exteriorMul K S C N₁) (hJ : J = exteriorMul K S C N₂)
    (hcop : IsCoprime N₁.val.val N₂.val.val) :
    ∃ a b : OS,
      a * (thetaGeneratorDivision K S D C N₂ J hJ).val -
        b * (thetaGeneratorDivision K S D C N₁ I hI).val = 1 := by
  obtain ⟨r, s, hrs⟩ := thetaGeneratorDivision_isCoprime K S D C N₁ N₂ I J hI hJ hcop
  refine ⟨s, -r, ?_⟩
  calc
    _ = r * (thetaGeneratorDivision K S D C N₁ I hI).val +
        s * (thetaGeneratorDivision K S D C N₂ J hJ).val := by ring
    _ = 1 := hrs

/-- Any common exterior ideal forces divisibility of every frequency in
the support of the actual full original correlation. No residual
coprimality is needed for this support statement. -/
theorem thetaOriginalFullCorrelation_eq_zero_of_not_dvd
    (C N₁ N₂ I J : ExteriorIdeal K S)
    (hI : I = exteriorMul K S C N₁) (hJ : J = exteriorMul K S C N₂)
    (j : OS) (hj : ¬ D.generator C ∣ j) :
    sIntegerSexticOriginalFullCorrelation K S D.root6 D.primitive6 D.embedding
      (probeArithmetic_six_support K S D)
      (probeGenerator K S D I) (probeGenerator K S D J) j = 0 := by
  exact sIntegerSexticOriginalFullCorrelation_common_factor_support
    K S D.root6 D.primitive6 D.embedding (probeArithmetic_six_support K S D)
    (probeGenerator K S D I) (probeGenerator K S D J) (probeGenerator K S D C)
    (thetaGeneratorDivision K S D C N₁ I hI) (thetaGeneratorDivision K S D C N₂ J hJ)
    j (thetaGeneratorDivision_factor K S D C N₁ I hI)
    (thetaGeneratorDivision_factor K S D C N₂ J hJ) hj

/-- The same support statement expressed in the actual extension C.map,
without replacing C by a formal common-factor label. -/
theorem thetaOriginalFullCorrelation_eq_zero_of_not_mem
    (C N₁ N₂ I J : ExteriorIdeal K S)
    (hI : I = exteriorMul K S C N₁) (hJ : J = exteriorMul K S C N₂)
    (j : OS) (hj : j ∉ C.val.val.map (algebraMap (𝓞 K) OS)) :
    sIntegerSexticOriginalFullCorrelation K S D.root6 D.primitive6 D.embedding
      (probeArithmetic_six_support K S D)
      (probeGenerator K S D I) (probeGenerator K S D J) j = 0 := by
  apply thetaOriginalFullCorrelation_eq_zero_of_not_dvd K S D C N₁ N₂ I J hI hJ j
  intro hdvd
  apply hj
  rw [← D.generator_span C]
  exact Ideal.mem_span_singleton.mpr hdvd

/-- Exact raw sextic times actual RCorrection times genuine finite
correlation at C. Both quotient generators retain their actual units.
All k, including zero and nonprimitive frequencies, remain in the formula. -/
theorem thetaOriginalFullCorrelation_factorization
    (C N₁ N₂ I J : ExteriorIdeal K S)
    (hI : I = exteriorMul K S C N₁) (hJ : J = exteriorMul K S C N₂)
    (hcop : IsCoprime N₁.val.val N₂.val.val) (k : OS) :
    let n₁ : NZ := thetaGeneratorDivision K S D C N₁ I hI
    let n₂ : NZ := thetaGeneratorDivision K S D C N₂ J hJ
    sIntegerSexticOriginalFullCorrelation K S D.root6 D.primitive6 D.embedding
      (probeArithmetic_six_support K S D)
      (probeGenerator K S D I) (probeGenerator K S D J) (D.generator C * k) =
      (χ k n₁ * conj (χ (-k) n₂)) *
        sIntegerSexticRCorrection K S D.root6 D.primitive6 D.embedding n₁ n₂ *
        sIntegerSexticFiniteCorrelation K S D.root6 D.primitive6 D.embedding
          C.val.val (nonZeroDivisors.coe_ne_zero C.val) C.property
          (fun p hp => D.away_six p (C.property p hp))
          (Ideal.Quotient.mk _ n₁.val) (Ideal.Quotient.mk _ n₂.val)
          (Ideal.Quotient.mk _ k) := by
  obtain ⟨a, b, hab⟩ := exists_thetaGeneratorDivision_bezout K S D C N₁ N₂ I J hI hJ hcop
  have hf := sIntegerSexticOriginalFullCorrelation_factorization
    K S D.root6 D.primitive6 D.embedding (probeArithmetic_six_support K S D)
    (probeGenerator K S D I) (probeGenerator K S D J) (probeGenerator K S D C)
    (thetaGeneratorDivision K S D C N₁ I hI) (thetaGeneratorDivision K S D C N₂ J hJ)
    a b k (thetaGeneratorDivision_factor K S D C N₁ I hI)
    (thetaGeneratorDivision_factor K S D C N₂ J hJ) hab
  convert hf using 2
  all_goals first | rfl | exact (probeGenerator_contraction K S D C).symm | skip
  exact HeckeGeneral.Characters.sIntegerSexticFiniteCorrelation_ideal_congr K S _ _ _
    (probeGenerator_contraction K S D C).symm _ _ _ _ _ _ _ _ _

end HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
