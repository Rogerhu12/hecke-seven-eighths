module

public import ThetaGlobal.GlobalProjectOrbitEvaluation
public import ThetaGlobal.FiniteSourceConstantTerm

@[expose] public section

/-!
# The actual normalized seed identity on rational frequency classes

This theorem joins the proved high K-type Fourier reflection, exact
exterior extraction, absolute S-unit orbit unfolding, and the actual
normalized local Mellin pair.  Every analytic hypothesis is discharged
from the constructed source.  The remaining explicit inputs are the
permitted local archimedean and exterior digit tables.

The two frequency series are absolutely summable.  Their common actual
Fourier normalization is nonzero and is cancelled only after both orbit
evaluations have been proved with precisely that same scalar.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section

namespace ThetaGlobal.GlobalProjectFrequencySeed

open NumberField MeasureTheory DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.OrbitExpansion
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open DedekindZetaZeroFree.ThetaSheetExactUnfolding
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.GlobalProjectOrbitEvaluation
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

local instance : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
local instance : Countable R.A.Gamma1 :=
  Countable.of_equiv (ThetaReflectionData.rationalGamma R.A) (gammaEquiv R).toEquiv

def frequencyOrbitEquiv : (ThetaReflectionData.Frequency R.A × R.A.Gamma1) ≃ Fˣ :=
  (Equiv.prodCongr (Equiv.refl _) (gammaEquiv R).symm.toEquiv).trans
    (orbitFrequencyEquiv R)

theorem frequencyOrbitEquiv_apply (ξ : ThetaReflectionData.Frequency R.A)
    (γ : R.A.Gamma1) :
    frequencyOrbitEquiv R (ξ, γ) = gammaFrequency R (Quotient.out ξ) γ := by
  change (Quotient.out ξ : Fˣ) * ((gammaEquiv R).symm γ).val =
    ((gammaEquiv R).symm γ).val * Quotient.out ξ
  exact mul_comm _ _

theorem frequencyOrbitEquiv_apply_pair (i : ThetaReflectionData.Frequency R.A × R.A.Gamma1) :
    frequencyOrbitEquiv R i = gammaFrequency R (Quotient.out i.1) i.2 := by
  rcases i with ⟨ξ, γ⟩
  exact frequencyOrbitEquiv_apply R ξ γ

theorem absolute_grouping (f : Fˣ → ℂ) (hf : Summable (fun a => ‖f a‖)) :
    Summable (fun ξ : ThetaReflectionData.Frequency R.A =>
      ‖∑' γ : R.A.Gamma1, f (gammaFrequency R (Quotient.out ξ) γ)‖) ∧
    (∑' a : Fˣ, f a) =
      ∑' ξ : ThetaReflectionData.Frequency R.A, ∑' γ : R.A.Gamma1,
        f (gammaFrequency R (Quotient.out ξ) γ) := by
  have hn := hf.comp_injective (frequencyOrbitEquiv R).injective
  simp_rw [frequencyOrbitEquiv_apply_pair] at hn
  refine ⟨?_, ?_⟩
  · exact hn.prod.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ =>
      norm_tsum_le_tsum_norm (hn.prod_factor ξ))
  · calc
      _ = ∑' i : ThetaReflectionData.Frequency R.A × R.A.Gamma1,
          f (frequencyOrbitEquiv R i) := ((frequencyOrbitEquiv R).tsum_eq f).symm
      _ = _ := by
        simp_rw [frequencyOrbitEquiv_apply_pair]
        exact hn.of_norm.tsum_prod

theorem norm_summable_of_common_scalar {I : Type*} (W : ℂ) (hW : W ≠ 0)
    (f g : I → ℂ) (hg : Summable (fun i => ‖g i‖)) (he : ∀ i, g i = W * f i) :
    Summable (fun i => ‖f i‖) := by
  apply (hg.mul_left ‖W‖⁻¹).congr
  intro i
  rw [he, norm_mul, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hW), one_mul]

variable (θ : HeckeCharacter F) (C : FiniteFixedSource.Source R θ)
  (L : FiniteLocalHighK.Input R θ C)

local notation "D" => C.projected.base.factorization
local notation "Sf" => (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))

local instance : C.transport.groupHaar.IsHaarMeasure := C.transport.groupHaar_isHaar

/-- The constructed source proves the normalized global seed identity.
There is no global seed, reflection, summability, or profile factorization
hypothesis in this statement. -/
theorem actual_frequency_seed
    (hR : RootAligned R)
    (Adata : ThetaArithmeticData F Sf)
    (H : GlobalProjectLocalDigitTables.Input R D Adata)
    (hS : conductorPlaces F θ ⊆ R.A.Sf)
    (u : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (j : GlobalProjectWeightedDigits.Places R m → Fin 6)
    (marked : GlobalProjectWeightedDigits.Places R m → Bool)
    (w : InfinitePlace F) (hk : heckeComplexWeight F w (R.A.complex_place w) θ ≠ 0)
    (l : PositiveAxis) :
    let c := GlobalProjectLiteralDigitWeights.tensorWeight R Adata m j marked
    Summable (fun ξ : ThetaReflectionData.Frequency R.A =>
      ‖directTerm R θ C L u m c w l (Quotient.out ξ)‖) ∧
    Summable (fun ξ : ThetaReflectionData.Frequency R.A =>
      ‖GlobalProjectOrbitEvaluation.reflectedTerm R θ C L u m c w l (Quotient.out ξ)‖) ∧
    (∑' ξ : ThetaReflectionData.Frequency R.A,
      directTerm R θ C L u m c w l (Quotient.out ξ)) =
      ∑' ξ : ThetaReflectionData.Frequency R.A,
        GlobalProjectOrbitEvaluation.reflectedTerm R θ C L u m c w l (Quotient.out ξ) := by
  let c := GlobalProjectLiteralDigitWeights.tensorWeight R Adata m j marked
  have hc : GlobalProjectWeightedDigits.ReindexInvariant R m c :=
    GlobalProjectLiteralDigitWeights.tensorWeight_reindexInvariant R Adata m j marked
  have hfwd (a : Fˣ) (γ : ThetaReflectionData.rationalGamma R.A) :
      GlobalProjectForwardCoefficients.scalar R D m c (γ.val * a) =
        GlobalProjectForwardCoefficients.scalar R D m c a :=
    GlobalProjectForwardCoefficients.scalar_gamma R D Adata C.projected.base.exterior H
      m j marked a γ
  obtain ⟨Ω, hΩm, hΩc, _, hΩ⟩ := exists_sheetFundamentalDomain R.A w C.transport.groupHaar l
  have hi := GlobalProjectWeightedSheet.target_sheet_fourier_identity R m c hc
    (FiniteFixedSource.Source.constantTerm R θ C)
    (GlobalProjectHighKReflection.vector R D u L.vector)
    (GlobalProjectHighKReflection.vector_exterior R D u L.vector)
    θ hS u w hk C.transport.groupHaar l Ω hΩ hΩc
  change (∑' a : Fˣ, integralTerm R θ C L u m c w l Ω true a) =
    ∑' a : Fˣ, integralTerm R θ C L u m c w l Ω false a at hi
  have hd := absolute_grouping R _
    (integralTerm_norm_summable R θ C L u m c w l Ω hΩm.nullMeasurableSet hΩc true)
  have hr := absolute_grouping R _
    (integralTerm_norm_summable R θ C L u m c w l Ω hΩm.nullMeasurableSet hΩc false)
  have hde (ξ : ThetaReflectionData.Frequency R.A) :
      (∑' γ : R.A.Gamma1, integralTerm R θ C L u m c w l Ω true
        (gammaFrequency R (Quotient.out ξ) γ)) =
      GlobalProjectSheetProfiles.commonScalar R θ C L u *
        directTerm R θ C L u m c w l (Quotient.out ξ) :=
    (forward_orbit R θ C L u m c hR hfwd hS w l Ω hΩ hΩc (Quotient.out ξ)).2
  have hre (ξ : ThetaReflectionData.Frequency R.A) :
      (∑' γ : R.A.Gamma1, integralTerm R θ C L u m c w l Ω false
        (gammaFrequency R (Quotient.out ξ) γ)) =
      GlobalProjectSheetProfiles.commonScalar R θ C L u *
        GlobalProjectOrbitEvaluation.reflectedTerm R θ C L u m c w l (Quotient.out ξ) :=
    (reverse_orbit R θ C L u m c hR hc hS w l Ω hΩ hΩc (Quotient.out ξ)).2
  have hW := GlobalProjectSheetProfiles.commonScalar_ne_zero R θ C L u
  refine ⟨norm_summable_of_common_scalar _ hW _ _ hd.1 hde,
    norm_summable_of_common_scalar _ hW _ _ hr.1 hre, ?_⟩
  apply mul_left_cancel₀ hW
  rw [hd.2, hr.2] at hi
  simp_rw [hde, hre] at hi
  simpa only [tsum_mul_left] using hi

end ThetaGlobal.GlobalProjectFrequencySeed

#print axioms ThetaGlobal.GlobalProjectFrequencySeed.actual_frequency_seed
