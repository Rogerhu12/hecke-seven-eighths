import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolStageTerminalBudget

/-!
# Raw terminal calibration for the literal amplifier residual source

The original whole-factor encoding is injective.  Its residual encoding
is constructed here, and both its product and its bounded fibres are
proved before supplying the per-profile, norm and radius windows.
Thus the actual 1/6/7 source can inhabit the same terminal interface as
the main source without a false residual-injectivity requirement.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
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
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

namespace FirstGaussPoolData

/-- This produces the actual raw window record consumed by
`ActualGaussStage.TerminalCalibration`.  It takes no residual factor
identity, fibre/cardinality estimate, tail estimate or zero estimate. -/
def residualTailWindows {ι : Type*} (d : FirstGaussPoolData C P ι)
    (p : ExteriorPrime A) (n k : ℕ) (c : ι → ℂ)
    (s : ActualGaussStage (E := E) hΓ μv hDiff (d.residualSource p n c) finiteTest)
    (sTail : Finset (ℕ × ℕ)) (prodExp profileExp maskExp radiusExp Amp : ℝ)
    (hZ : 1 ≤ Z) (hB : 0 ≤ prodExp) (hAmp : 0 ≤ Amp)
    (originalFactors : ι × ι → Fin k → A.Exterior)
    (hinj : Set.InjOn (fun ij t => (originalFactors ij t).val)
      (d.columns ×ˢ d.columns : Set (ι × ι)))
    (hproduct : ∀ ij ∈ d.columns ×ˢ d.columns,
      PowerfulDiagonal.tupleIdeal (fun t => (originalFactors ij t).val) =
        (d.ideal ij.1).val * (d.ideal ij.2).val)
    (hnorm : ∀ ij ∈ (d.residualSource p n c).columns ×ˢ (d.residualSource p n c).columns,
      (Ideal.absNorm (((d.residualSource p n c).ideal ij.1).val *
        ((d.residualSource p n c).ideal ij.2).val) : ℝ) ≤ Z ^ prodExp)
    (hprofile : ∀ v ∈ firstZeroPairs
      (d.residualSource p n c).columns (d.residualSource p n c).columns
      (d.residualSource p n c).ideal (d.residualSource p n c).ideal,
      sTail.sup (schwartzSeminormFamily ℂ V ℂ)
        (((d.residualSource p n c).coefficient v.2.1 *
          star ((d.residualSource p n c).coefficient v.2.2)) • s.profile) ≤
        Amp * Z ^ profileExp)
    (hmask :
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) s.mask)).val ≤ Z ^ maskExp)
    (hradius : s.radius.val⁻¹ ≤ Z ^ radiusExp) :
    SecondTailWindows C
      (d.residualSource p n c).columns (d.residualSource p n c).columns
      (d.residualSource p n c).ideal (d.residualSource p n c).ideal
      (fun DE => canonicalFirstCommonBlock C
        (d.residualSource p n c).columns (d.residualSource p n c).columns
        (d.residualSource p n c).ideal (d.residualSource p n c).ideal DE.val DE.property)
      sTail (fun i j => ((d.residualSource p n c).coefficient i *
        star ((d.residualSource p n c).coefficient j)) • s.profile)
      s.radius s.mask k Z prodExp profileExp maskExp radiusExp Amp where
  base_ge_one := hZ
  productExponent_nonneg := hB
  amplitude_nonneg := hAmp
  factors ij := actualResidualFactorTuple C p (originalFactors (ij.1.val, ij.2.val))
  multiplicity := (n + n + 1) ^ k
  factors_fiber_card := (d.residual_source_pair_factors p n k c originalFactors hinj hproduct).2
  factor_product := (d.residual_source_pair_factors p n k c originalFactors hinj hproduct).1
  product_norm := hnorm
  profile_seminorm := hprofile
  mask_norm := hmask
  inverse_radius := hradius

/-- The same fixed factor count pays all three actual error valuations. -/
theorem residual_terminal_multiplicity_le (n k : ℕ) (hn : n ≤ 7) :
    (n + n + 1) ^ k ≤ 15 ^ k :=
  Nat.pow_le_pow_left (by omega) k

end FirstGaussPoolData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.residualTailWindows
