import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalGaussScaleProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralTwoStages
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAtlasAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDeletion
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPlainBalance

/-!
# The actual literal Gauss scale from the original prime window

The original prime representatives are supported in `(1, 2)`. Each
removed occurrence therefore has ideal norm at least its original
prime scale. The original residual-scale theorem applies with
reciprocal annulus constant exactly one, including empty slot sets.

The first transform inserts that residual scale once. The second
extraction preserves the complete Gauss product, by moving each
removed Gauss occurrence into the first plain factor. Atlas transport,
deletion masks, scalar extraction and plain balance also preserve it.
The resulting product is the normalization scale of the same actual
frame; no lower bound on a completed frame is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

namespace RawProfileWindow

variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {B : ℝ}

/-- Only the original open prime window is used, rather than a lower
endpoint for the two plain profiles. -/
theorem primeScale_le_norm_of_open_prime_window
    (profiles : RawProfileWindow rowDomain heightDomain window seminorms d B)
    (Z t : ℝ) (hZ : 0 < Z)
    (hprime : ∀ i, Function.support (profiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
    (i : Fin d.geometry.slotCount) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length)) :
    Z ^ (d.geometry.slots i).length ≤ (Ideal.absNorm p.asIdeal : ℝ) := by
  have hprofile := ((d.geometry.slots i).support_spec t
    (Z ^ (d.geometry.slots i).length) p).mp hp
  have hrep : profiles.primeRep i t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) ≠ 0 := by
    simpa only [profiles.prime_eq] using hprofile
  have hratio := (hprime i hrep).1
  have h := (lt_div_iff₀ (Real.rpow_pos_of_pos hZ (d.geometry.slots i).length)).mp hratio
  simpa only [one_mul] using h.le

end RawProfileWindow

namespace SupportCartesianBranch

variable {k : ℕ} {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {support : Finset (Ideal (𝓞 K))}

/-- The fixed reciprocal-annulus cost is one for the original prime
window. Every removed occurrence still appears in the frozen ideal. -/
theorem residualGaussScale_lower_one
    (b : SupportCartesianBranch S₁ S₂ S support)
    (Z : ℝ) (hZ : 1 < Z) (length : Fin k → ℝ) (X₁ X₂ total : ℝ)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hproduct : X₁ * X₂ = Z ^ total)
    (hprime : ∀ i ∈ Finset.univ \ b.keep,
      Z ^ length i ≤ (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ)) :
    Z ^ (total + (∑ i, length i) -
      idealLogLength Z (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2)) ≤
        b.residualGaussScale Z length X₁ X₂ := by
  simpa only [one_pow, one_mul] using
    b.residualGaussScale_lower Z hZ length X₁ X₂ total 1 k hX₁ hX₂ le_rfl le_rfl
      hproduct (by simpa only [one_mul] using hprime)

end SupportCartesianBranch

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

def gaussScale : ℝ := extraGaussScale d.gauss₁ d.gauss₂ d.gaussSlot

theorem gaussScale_pos : 0 < d.gaussScale :=
  extraGaussScale_pos _ _ _ d.gauss₁_pos d.gauss₂_pos d.gaussSlot_pos

@[simp] theorem gaussScale_scale (c : ℂ) : (d.scale c).gaussScale = d.gaussScale := rfl

@[simp] theorem gaussScale_balancePlain (c : Bool → ℝ) :
    (d.balancePlain c).gaussScale = d.gaussScale := rfl

@[simp] theorem gaussScale_deleteMask (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.deleteMask M).gaussScale = d.gaussScale := rfl

@[simp] theorem gaussScale_onAtlas {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (atlas : SourceCartesianAtlas columns ideal) (count : k = atlas.slotCount) :
    (d.onAtlas atlas count).gaussScale = d.gaussScale := by
  cases count
  rfl

@[simp] theorem gaussScale_extract {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    (d.extract b).gaussScale = d.gaussScale := d.extract_gaussScale b

section FirstTransform

variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)

theorem gaussScale_secondInput :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).gaussScale =
        d.gaussScale * b.residualGaussScale d.base d.length (d.scale₁ false) (d.scale₂ false) :=
  d.secondInput_gaussScale (σ := σ) b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂

theorem secondInput_gaussScale_lower_one
    (total : ℝ) (hproduct : d.scale₁ false * d.scale₂ false = d.base ^ total)
    (hprime : ∀ i ∈ Finset.univ \ b.keep,
      d.base ^ d.length i ≤ (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ)) :
    d.gaussScale * d.base ^ (total + (∑ i, d.length i) -
      idealLogLength d.base
        (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2)) ≤
      (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).gaussScale := by
  rw [d.gaussScale_secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂]
  exact mul_le_mul_of_nonneg_left
    (b.residualGaussScale_lower_one d.base d.base_gt_one d.length
      (d.scale₁ false) (d.scale₂ false) total
      (d.scale₁_pos false).le (d.scale₂_pos false).le hproduct hprime) d.gaussScale_pos.le

end FirstTransform

/-- The frame uses this complete product on both sides, regardless of
the sign of its actual right Fourier phases. -/
theorem factors_normalizationScale
    {A : SArithmeticData K} {σ : K →+* ℂ}
    {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
    {C : A.GeneralArithmeticContext σ η hS}
    {H J : Type*} [Fintype J] [DecidableEq J]
    (R : ActualSecondCorrelationRows A σ H J)
    (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
    (ideal : AllocationColumn K k → A.Exterior)
    (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
      (ideal i).val = allocationColumnIdeal i)
    (firstSign : ℝ) (rectangle : Bool) (L : Ideal (𝓞 K))
    (selection : primeSupport L → Finset (Fin (k + 2)))
    (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
      id id HeightOneSpectrum.asIdeal).Nonempty) :
    ((d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne)
      .normalizationScale = d.gaussScale := rfl

end CanonicalLiteralRectangles.Atoms

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)

local notation "seed" => Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂

@[simp] theorem literalOriginalAtoms_gaussScale : (seed).gaussScale = 1 := by
  simp only [literalOriginalAtoms, CanonicalLiteralRectangles.Atoms.gaussScale,
    extraGaussScale, Finset.prod_const_one, mul_one]

/-- The actual original support provides every prime lower bound. The
result concerns the actual first-extracted table before the second
common extraction, and charges the entire frozen original ideal. -/
theorem literalOriginalAtoms_secondInput_gaussScale_lower
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch (seed).plain₁ (seed).plain₂ (seed).slots support)
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {B : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window seminorms (data ξ) B)
    (hprime : ∀ i, Function.support (profiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2) :
    Z ^ (a.n₁ + a.n₂ + (data ξ).geometry.totalLength -
      idealLogLength Z
        (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2)) ≤
      ((seed).secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).gaussScale := by
  have hp (i) (_hi : i ∈ Finset.univ \ b.keep) :
      (seed).base ^ (seed).length i ≤ (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ) := by
    have hslot := (Finset.mem_filter.mp (b.witness_slots i)).1
    change b.witness.2 i ∈
      (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorSlots i at hslot
    exact profiles.primeScale_le_norm_of_open_prime_window Z t (zero_lt_one.trans hZ)
      hprime i (b.witness.2 i) (Finset.mem_filter.mp hslot).1
  have hproduct : (seed).scale₁ false * (seed).scale₂ false = (seed).base ^ (a.n₁ + a.n₂) :=
    (Real.rpow_add (zero_lt_one.trans hZ) a.n₁ a.n₂).symm
  have h := (seed).secondInput_gaussScale_lower_one (σ := σ) b P R
    power firstFixed poolFixed unitFixed firstElement poolElement unitElement
    hfirst hpool hunit δ₁ δ₂ (a.n₁ + a.n₂) hproduct hp
  simpa only [Q.literalOriginalAtoms_gaussScale ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂,
    one_mul, SlotGeometry.totalLength] using h

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.RawProfileWindow.primeScale_le_norm_of_open_prime_window
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.residualGaussScale_lower_one
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.factors_normalizationScale
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_secondInput_gaussScale_lower
