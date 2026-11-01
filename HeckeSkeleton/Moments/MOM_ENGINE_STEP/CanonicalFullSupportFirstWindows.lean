import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFirstPhysicalWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFullSupportParameters

/-!
# The original full-support first terminal calibration

A fixed original length bound determines the physical tail degree before
any moving source or profiles. The actual raw column windows then supply
the complete principal-mask and first-modulus windows. The sharp zero
radius is the full-support radius from the original joint row budget.

This factory retains the actual centered coefficients, Cartesian columns,
common blocks, padded original factor tuple and independent sharp zero
product bound. It takes no physical mask/modulus estimate, whole source
bound, terminal ledger or final terminal bound.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]

/-- A fixed degree for all actual first tail windows with this slot
cap and original column/parent length bound. -/
def originalFirstPhysicalDegree (cap : ℕ) (bound : ℝ) : ℝ :=
  2 * bound * ((2 * (cap + 2) : ℕ) : ℝ) + 3 * bound

theorem firstTailExponent_le_originalPhysicalDegree
    (cap : ℕ) (bound columnDegree originalDegree : ℝ)
    (hcolumn : columnDegree ≤ bound) (horiginal : 0 ≤ originalDegree) :
    firstTailExponent (2 * (cap + 2)) (2 * columnDegree)
      (2 * (-originalDegree / 2)) bound (2 * bound) ≤
        originalFirstPhysicalDegree cap bound := by
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcolumn (by norm_num : (0 : ℝ) ≤ 2))
    (Nat.cast_nonneg (2 * (cap + 2)) : (0 : ℝ) ≤ ((2 * (cap + 2) : ℕ) : ℝ))
  dsimp only [firstTailExponent, originalFirstPhysicalDegree]
  linarith

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K} {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]

/-- All physical first windows and the full-support inverse radius
are filled from the original arithmetic recipe and individual profiles.
The remaining scalar premises are only original lengths and the fixed
annulus threshold. -/
def canonicalFullSupportFirstWindows
    (W : NormProfileRecipe data) (ξ : X) (a : RealParameters) (Z t Y₁ Y₂ : ℝ)
    (C : A.GeneralArithmeticContext σ η hS)
    (cap : ℕ) (orders : Finset (ℕ × ℕ))
    (B annulus loss leftExponent rightExponent bound Nsave decay : ℝ)
    (hB : 1 ≤ B) (hannulus : 1 ≤ annulus) (hloss : 0 ≤ loss) (hbound : 0 ≤ bound)
    (hcap : (data ξ).geometry.slotCount ≤ cap)
    (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss)
    (centered : Bool) {floor padding : ℝ}
    (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
    (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hleftExponent : a.n₁ ≤ leftExponent) (hrightExponent : a.n₂ ≤ rightExponent)
    (hY₁le : Y₁ ≤ Z ^ leftExponent) (hY₂le : Y₂ ≤ Z ^ rightExponent)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window
      (OriginalProfileAtomBounds.profileOrders orders) (data ξ) B)
    (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (hcolumn : leftExponent + rightExponent + (data ξ).geometry.totalLength + loss ≤ bound)
    (hwidth : a.m + a.q ≤ bound)
    (sTail sZero : Finset (ℕ × ℕ)) :
    let atoms := (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t;
    let raw := atoms.raw Y₁ Y₂;
    FirstDualOriginalWindows
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) C
      raw.exteriorColumns raw.columnExterior (raw.originalFirstBlocks C)
      (fun i j => ((atoms.values Y₁ Y₂).coefficient centered i *
        star ((atoms.values Y₁ Y₂).coefficient centered j)) • CanonicalRowBall.archTest K A.Sf 1)
      (Q.fullSupportRadius Z (a.m + a.q) (zero_lt_one.trans domain.scale)) ∅
      sTail sZero (2 * (cap + 2)) Z
      (Z ^ firstTailCutoffExponent (originalFirstPhysicalDegree cap bound) Nsave decay)
      bound (originalFirstPhysicalDegree cap bound) Nsave decay := by
  let atoms := (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t
  let raw := atoms.raw Y₁ Y₂
  have hz : 0 < Z := zero_lt_one.trans domain.scale
  have hraw (i : raw.Column) (hi : i ∈ raw.exteriorColumns) :
      (Ideal.absNorm (raw.columnExterior i).val : ℝ) ≤ Z ^ bound := by
    apply (raw.original_union_column_norm_le_power profiles cap annulus loss
      leftExponent rightExponent hannulus hcap hannulusZ hz hY₁ hY₂
      (Real.rpow_le_rpow_of_exponent_le domain.scale.le hleftExponent)
      (Real.rpow_le_rpow_of_exponent_le domain.scale.le hrightExponent)
      hY₁le hY₂le hrows ht hwindow i hi).trans
    exact Real.rpow_le_rpow_of_exponent_le domain.scale.le hcolumn
  have hphysical := first_original_physical_windows
    (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) C
    raw.exteriorColumns raw.exteriorColumns raw.columnExterior raw.columnExterior
    (raw.originalFirstBlocks C) (fun _ _ => CanonicalRowBall.archTest K A.Sf 1)
    Z bound hz hraw hraw
  have hinverse : (Q.fullSupportRadius Z (a.m + a.q) hz).val⁻¹ ≤ Z ^ (2 * bound) := by
    rw [Q.fullSupportRadius_inverse_eq_parameters_m a Z domain.scale]
    apply Real.rpow_le_rpow_of_exponent_le domain.scale.le
    rw [Q.fullSupportParameters_m]
    have hs := Q.fullSupportLength_nonneg Z domain.scale
    linarith
  have hlength : 0 ≤ (data ξ).geometry.totalLength :=
    Finset.sum_nonneg (fun i _ => ((data ξ).geometry.slots i).length_pos.le)
  have hdegree := firstTailExponent_le_originalPhysicalDegree cap bound
    (leftExponent + rightExponent + (data ξ).geometry.totalLength + loss)
    (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) hcolumn
    (add_nonneg (add_nonneg domain.plain_left_nonneg domain.plain_right_nonneg) hlength)
  exact Q.canonicalOriginalFirstWindows W ξ a Z t Y₁ Y₂ C cap orders
    B annulus loss leftExponent rightExponent hB hannulus hloss hcap hannulusZ
    centered domain hY₁ hY₂ hleftExponent hrightExponent hY₁le hY₂le
    profiles hrows ht hwindow (Q.fullSupportRadius Z (a.m + a.q) hz) ∅ sTail sZero
    (Z ^ firstTailCutoffExponent (originalFirstPhysicalDegree cap bound) Nsave decay)
    bound (originalFirstPhysicalDegree cap bound) Nsave decay bound (2 * bound)
    (Q.fullSupportParameters a Z).m hcolumn
    (fun v hv => (hphysical v hv).1) (fun v hv => (hphysical v hv).2)
    hinverse (Q.fullSupportRadius_inverse_eq_parameters_m a Z domain.scale).le
    hdegree rfl (1 : Ideal (𝓞 K)) one_ne_zero
    (by simpa only [map_one, Nat.cast_one] using Real.one_le_rpow domain.scale.le hbound)
    emptyOriginalSIntegerMask

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.firstTailExponent_le_originalPhysicalDegree
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalFullSupportFirstWindows
