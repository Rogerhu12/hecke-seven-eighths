import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralAtlas
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalGaussScaleProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNominalGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SixthDeletionCapacity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralPhases

set_option linter.unusedSectionVars false

/-!
# The two original constant scalars outside the profile family

The first common extraction and the pool reciprocity scalar are
independent of every remaining column. Their precise product is
separated from the actual two-stage atom table here. This equality is
proved from the individual profile operations, including all ramified
zeros and the complete centered subtraction.

Both scalars may vanish. No division is used in their normal form.
Only a genuinely nonzero original coefficient permits the inverse
rescaling used by the live normalization family. Atlas transport,
second common extraction and full deletion preserve the same scalar.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralRectangles.Atoms

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)

theorem scale_scale (c e : ℂ) : (d.scale c).scale e = d.scale (c * e) := by
  sorry

theorem scale_one : d.scale 1 = d := by
  sorry

theorem scale_inv_cancel (c : ℂ) (hc : c ≠ 0) :
    (d.scale c).scale c⁻¹ = d := by
  sorry

theorem scale_addGauss (c : ℂ) (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ i, 0 < G i) :
    (d.scale c).addGauss G₁ G₂ G h₁ h₂ hG =
      (d.addGauss G₁ G₂ G h₁ h₂ hG).scale c := by
  sorry

theorem scale_normPower (c : ℂ) (δ : ℝ) :
    (d.scale c).normPower δ = (d.normPower δ).scale c := by
  sorry

theorem scale_twoStageNorms (c : ℂ) (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ i, 0 < G i) (δ₁ δ₂ : ℝ) :
    (d.scale c).twoStageNorms G₁ G₂ G h₁ h₂ hG δ₁ δ₂ =
      (d.twoStageNorms G₁ G₂ G h₁ h₂ hG δ₁ δ₂).scale c := by
  sorry

theorem scale_extract (c : ℂ) {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    (d.scale c).extract b = (d.extract b).scale c := rfl

theorem scale_commonScalar (c : ℂ) {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    (d.scale c).commonScalar b = d.commonScalar b := rfl

theorem scale_onAtlas (c : ℂ) {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount) :
    (d.scale c).onAtlas T count = (d.onAtlas T count).scale c := by
  sorry

theorem scale_deleteMask (c : ℂ) (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.scale c).deleteMask M = (d.deleteMask M).scale c := rfl

theorem scale_balancePlain (c : ℂ) (balance : Bool → ℝ) :
    (d.scale c).balancePlain balance = (d.balancePlain balance).scale c := by
  sorry

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

theorem scale_movingSingleton (c : ℂ) (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) :
    (d.scale c).movingSingleton P R I a ha =
      (d.movingSingleton P R I a ha).scale c := rfl

variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

/-- This table retains both Mellin factors, the actual Gauss scales
and all three original arithmetic phases. Only the two column-constant
profile multipliers are outside it. -/
def secondInputCore (firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement)
    (δ₁ δ₂ : ℝ) : CanonicalLiteralRectangles.Atoms (K := K) b.keep.card :=
  let e := d.extract b
  let n := e.twoStageNorms (e.scale₁ false) (e.scale₂ false)
    (fun i => e.base ^ e.length i) (e.scale₁_pos false) (e.scale₂_pos false)
    (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans e.base_gt_one) _) δ₁ δ₂
  ((n.movingSingleton P R firstFixed firstElement hfirst).movingSingleton
    P R poolFixed poolElement hpool).movingSingleton P R unitFixed unitElement hunit

/-- The exact first common scalar times the original pool scalar.
The latter is also present on the main and direct paths with power one. -/
def secondInputScalar (power : A.Exterior) (firstElement : A.R) (δ₁ : ℝ) : ℂ :=
  d.commonScalar b * (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
    actualIdealResidue (A := A) (σ := σ) power.val firstElement)

/-- An identity of the actual atom tables, proved before any sum or
norm. It therefore preserves every zero coefficient and works when
the extracted constant itself is zero. -/
theorem secondInput_eq_scale_core
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ) :
    d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ =
      (d.secondInputCore P R b firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale
          (d.secondInputScalar (σ := σ) b power firstElement δ₁) := by
  sorry

theorem secondInput_whole_eq_scalar_core
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)
    (i : AllocationColumn K b.keep.card) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).whole i =
      d.secondInputScalar (σ := σ) b power firstElement δ₁ *
        (d.secondInputCore P R b firstFixed poolFixed unitFixed
          firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).whole i := by
  sorry

theorem secondInputScalar_ne_zero_of_whole_ne_zero
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)
    (i : AllocationColumn K b.keep.card)
    (hne : (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).whole i ≠ 0) :
    d.secondInputScalar (σ := σ) b power firstElement δ₁ ≠ 0 := by
  sorry

/-- Inverse rescaling is used only after a true live coefficient has
proved that the original constant is nonzero. -/
theorem secondInput_scale_inverse
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)
    (hc : d.secondInputScalar (σ := σ) b power firstElement δ₁ ≠ 0) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale
        (d.secondInputScalar (σ := σ) b power firstElement δ₁)⁻¹ =
      d.secondInputCore P R b firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ := by
  sorry

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# The original scale product after actual occurrence extraction

An upper window on each original prime profile gives the upper scale
product needed by the actual capacity ledger. Every removed occurrence
appears in the frozen ideal. Its fixed annulus cost is paid explicitly;
neither a final raw-degree bound nor a child bound is assumed.

The same product is preserved by both Mellin factors, reciprocal plain
balancing, constant extraction, the exact Gauss normalization and the
original atlas transport. Thus the calculation applies to both actual
centered rectangles and to zero slots without a separate argument.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace RawProfileWindow

variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window seminorms d amplitude)

include profiles in
theorem primeNorm_le_annulus_mul_scale (B Z t : ℝ) (hZ : 0 < Z)
    (ht : t ∈ heightDomain) (hwindow : ∀ x ∈ window, x ≤ B)
    (i : Fin d.geometry.slotCount) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length)) :
    (Ideal.absNorm p.asIdeal : ℝ) ≤ B * Z ^ (d.geometry.slots i).length := by
  sorry

end RawProfileWindow

namespace SupportCartesianBranch

variable {k : ℕ} {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {P : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch S₁ S₂ S P)

/-- Every original frozen prime occurs in this product. The bound is
the upper-annulus counterpart of the already proved Gauss lower bound. -/
theorem residualGaussScale_mul_frozenNorm_le
    (Z : ℝ) (length : Fin k → ℝ) (X₁ X₂ B : ℝ) (cap : ℕ)
    (hZ : 0 < Z) (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    (hB : 1 ≤ B) (hcap : k ≤ cap)
    (hprime : ∀ i ∈ Finset.univ \ b.keep,
      (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ) ≤ B * Z ^ length i) :
    b.residualGaussScale Z length X₁ X₂ *
        (Ideal.absNorm (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂
          b.keep b.witness.2) : ℝ) ≤
      B ^ cap * (X₁ * X₂ * ∏ i, Z ^ length i) := by
  sorry

end SupportCartesianBranch

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

def scaleProduct (r : Bool) : ℝ :=
  d.scale₁ r * d.scale₂ r * ∏ i, d.base ^ d.length i

theorem scaleProduct_pos (r : Bool) : 0 < d.scaleProduct r := by
  sorry

theorem scaleProduct_eq_sum (r : Bool) :
    d.scaleProduct r = d.scale₁ r * d.scale₂ r * d.base ^ (∑ i, d.length i) := by
  sorry

/-- A window on the original individual prime occurrences, not on a
transformed polynomial or an output scale. -/
def PrimeNormWindow (B : ℝ) : Prop :=
  ∀ i, ∀ p ∈ d.slots i, (Ideal.absNorm p.asIdeal : ℝ) ≤ B * d.base ^ d.length i

variable {d} {B : ℝ}

theorem PrimeNormWindow.extract (h : d.PrimeNormWindow B)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    (d.extract b).PrimeNormWindow B := by
  sorry

theorem PrimeNormWindow.onAtlas (h : d.PrimeNormWindow B)
    {A : SArithmeticData K} {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount)
    (hslots : ∀ i, T.reindex.slots (Fin.cast count i) = d.slots i) :
    (d.onAtlas T count).PrimeNormWindow B := by
  sorry

theorem PrimeNormWindow.onAtlas_dictionary (h : d.PrimeNormWindow B)
    {A : SArithmeticData K} {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (index : AllocationColumn K k → ι)
    (e : T.literalDictionary = ⟨k, (d.plain₁, d.plain₂), d.slots, index⟩) :
    (d.onAtlas T (congrArg Sigma.fst e).symm).PrimeNormWindow B := by
  sorry

theorem PrimeNormWindow.scale (h : d.PrimeNormWindow B) (c : ℂ) :
    (d.scale c).PrimeNormWindow B := by
  sorry

theorem PrimeNormWindow.balancePlain (h : d.PrimeNormWindow B) (c : Bool → ℝ) :
    (d.balancePlain c).PrimeNormWindow B := by
  sorry

theorem PrimeNormWindow.deleteMask (h : d.PrimeNormWindow B)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.deleteMask M).PrimeNormWindow B := by
  sorry

variable (d)

theorem extract_scaleProduct_mul_frozenNorm_le (hprime : d.PrimeNormWindow B)
    (hB : 1 ≤ B) (cap : ℕ) (hcap : k ≤ cap)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) (r : Bool) :
    (d.extract b).scaleProduct r *
        (Ideal.absNorm (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂
          b.keep b.witness.2) : ℝ) ≤ B ^ cap * d.scaleProduct r := by
  sorry

theorem scale_scaleProduct (c : ℂ) (r : Bool) : (d.scale c).scaleProduct r = d.scaleProduct r := rfl
theorem normPower_scaleProduct (δ : ℝ) (r : Bool) : (d.normPower δ).scaleProduct r = d.scaleProduct r := rfl
theorem balancePlain_scaleProduct (c : Bool → ℝ) (r : Bool) :
    (d.balancePlain c).scaleProduct r = d.scaleProduct r := rfl
theorem deleteMask_scaleProduct (M : HeckeGeneral.Analysis.NonzeroIdeal K) (r : Bool) :
    (d.deleteMask M).scaleProduct r = d.scaleProduct r := rfl

theorem onAtlas_scaleProduct {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount) (r : Bool) :
    (d.onAtlas T count).scaleProduct r = d.scaleProduct r := by
  sorry

section TwoStages

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)

theorem secondInput_scaleProduct (r : Bool) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scaleProduct r =
        (d.extract b).scaleProduct r := rfl

theorem secondInputCore_scaleProduct (r : Bool) :
    (d.secondInputCore P R b firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scaleProduct r =
        (d.extract b).scaleProduct r := rfl

theorem secondInput_primeNormWindow (h : d.PrimeNormWindow B) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).PrimeNormWindow B := by
  sorry

theorem secondInputCore_primeNormWindow (h : d.PrimeNormWindow B) :
    (d.secondInputCore P R b firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).PrimeNormWindow B := by
  sorry

end TwoStages

/-- This consumes the original occurrence window and an earlier
proved original scale product. The full frozen ideal is subtracted
exactly, while its fixed annulus power remains visible. -/
theorem extract_scaleProduct_le_power (hprime : d.PrimeNormWindow B)
    (hB : 1 ≤ B) (cap : ℕ) (hcap : k ≤ cap)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) (r : Bool)
    (degree error : ℝ) (hproduct : d.scaleProduct r ≤ d.base ^ degree)
    (herror : B ^ cap ≤ d.base ^ error) :
    (d.extract b).scaleProduct r ≤
      d.base ^ (degree - idealLogLength d.base
        (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2) + error) := by
  sorry

end CanonicalLiteralRectangles.Atoms

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)

theorem literalOriginalAtoms_scaleProduct (r : Bool)
    (hcomparison : Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂)) :
    (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).scaleProduct r =
      Z ^ (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) := by
  sorry

theorem literalOriginalAtoms_primeNormWindow
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {amplitude : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window seminorms (data ξ) amplitude)
    (B : ℝ) (ht : t ∈ heightDomain) (hwindow : ∀ x ∈ window, x ≤ B) :
    (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).PrimeNormWindow B := by
  sorry

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStepV2

end

/-!+# The actual upper endpoints in the capacity length dictionary

The second source uses the upper endpoint of the proved physical row
window and the already paid original support majorant. Their two
parameters are computed here from the same original geometry and its
actual frequency radicals. There is no lower bound on an individual
row or an assumption that the support majorant is the support norm.

The cutoff is an explicit row error; the full sixth root is an explicit
support increment. The scale product derived from the two original
occurrence extractions is rewritten into the same raw-degree ledger.
The atom table, allocation and future capacity choice stay unchanged.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

namespace OriginalNominalTag

/-- The literal removed ideal: one for direct/main, and the actual
prime to its original 1/6/7 valuation for an amplifier error. -/
def extractionIdeal (tag : OriginalNominalTag K) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  match tag with
  | .direct | .main => 1
  | .error e p => ⟨p.asIdeal ^ e.multiplicity,
      mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ p.ne_bot)⟩

theorem extractionIdeal_length (tag : OriginalNominalTag K) (Z : ℝ) :
    idealLogLength Z tag.extractionIdeal.val = tag.removedLength Z := by
  sorry

end OriginalNominalTag


/-- The original annulus charge is absorbed at one fixed threshold,
before either original atlas, scale, allocation or Fourier variable. -/
theorem literal_scale_product_threshold (cap : ℕ) (annulus error : ℝ)
    (herror : 0 < error) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → annulus ^ (2 * cap) ≤ Z ^ error := by
  sorry

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

/-- The same original first ideal times the actual removed pool power.
For main and direct branches the latter is the unit ideal. -/
def literalFirstExtraction : HeckeGeneral.Analysis.NonzeroIdeal K :=
  G.ideals.first * G.tag.extractionIdeal

theorem literalFirstExtraction_length :
    idealLogLength Z G.literalFirstExtraction.val = G.skeleton.c + G.skeleton.w := by
  sorry

theorem literalRawDegree :
    G.skeleton.rawDegree = a.n₁ + a.n₂ + a.z -
      idealLogLength Z G.literalFirstExtraction.val -
        idealLogLength Z G.ideals.second.val := by
  sorry

/-- The raw row parameter of the chosen physical upper endpoint. -/
def literalRowParameter (cutoff : ℝ) : ℝ :=
  G.frequencyCenter + cutoff - (G.skeleton.g₂ + G.skeleton.V)

/-- The fixed support majorant includes the entire second sixth root. -/
def literalSupportParameter (rootLength : ℝ) : ℝ :=
  G.supportCenter + (G.skeleton.t₂ + G.skeleton.V) + rootLength

/-- All four endpoint inequalities and the exact norm extractions are
proved internally. Only the original cutoff size enters the error. -/
def literalEndpointWindows (hZ : 1 < Z) (cutoff rootLength : ℝ)
    (hcutoff : 0 ≤ cutoff) (hsmall : 2 * cutoff ≤ step) :
    G.ScaleWindows (G.literalRowParameter cutoff)
      (G.literalSupportParameter rootLength - rootLength) where
  rowScale := Z ^ (G.frequencyCenter + cutoff)
  supportScale := Z ^ G.supportCenter
  rowScale_pos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  supportScale_pos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  rowError := cutoff
  supportError := 0
  rowError_nonneg := hcutoff
  supportError_nonneg := le_rfl
  error_small := by simpa only [add_zero] using hsmall
  row_lower := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  row_upper := le_rfl
  support_lower := by simp only [sub_zero, le_refl]
  support_upper := by simp only [add_zero, le_refl]
  row_parameter := by
    have hf : Z ^ (G.skeleton.g₂ + G.skeleton.V) =
        (Ideal.absNorm (gcd G.ideals.second.val G.ideals.secondOpposite.val) : ℝ) *
          (Ideal.absNorm G.ideals.nonunitPart.val : ℝ) := by
      change Z ^ (idealLogLength Z _ + idealLogLength Z _) = _
      rw [Real.rpow_add (zero_lt_one.trans hZ), rpow_idealLogLength Z hZ _
        (gcd_ne_zero_of_left (nonZeroDivisors.coe_ne_zero G.ideals.second)),
        rpow_idealLogLength Z hZ _ (nonZeroDivisors.coe_ne_zero G.ideals.nonunitPart)]
    rw [literalRowParameter, Real.rpow_sub (zero_lt_one.trans hZ), hf]
  support_parameter := by
    have hf : Z ^ (G.skeleton.t₂ + G.skeleton.V) =
        (Ideal.absNorm G.ideals.unitPart.val : ℝ) *
          (Ideal.absNorm G.ideals.nonunitPart.val : ℝ) := by
      change Z ^ (idealLogLength Z _ + idealLogLength Z _) = _
      rw [Real.rpow_add (zero_lt_one.trans hZ),
        rpow_idealLogLength Z hZ _ (nonZeroDivisors.coe_ne_zero G.ideals.unitPart),
        rpow_idealLogLength Z hZ _ (nonZeroDivisors.coe_ne_zero G.ideals.nonunitPart)]
    simp only [literalSupportParameter, add_sub_cancel_right]
    rw [Real.rpow_add (zero_lt_one.trans hZ), hf]

@[simp] theorem literalEndpointWindows_error (hZ : 1 < Z) (cutoff rootLength : ℝ)
    (hcutoff : 0 ≤ cutoff) (hsmall : 2 * cutoff ≤ step) :
    (G.literalEndpointWindows hZ cutoff rootLength hcutoff hsmall).error = cutoff := by
  sorry

/-- The actual joint budget is the nominal width plus the two explicit
costs used by the physical-cutoff and full-deletion constructions. -/
theorem literalParameters_width (cutoff rootLength : ℝ) :
    G.literalRowParameter cutoff + G.literalSupportParameter rootLength =
      G.skeleton.nominalWidth + rootLength + cutoff := by
  sorry

end OriginalNominalGeometry

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {a : RealParameters} {step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a d.base step)

/-- The two actual norm factors calculated by the original-table and
covered-leaf theorems are precisely the raw-degree factors. -/
theorem scaleProduct_le_originalRawDegree
    (B : ℝ) (cap : ℕ) (error : ℝ) (rectangle : Bool)
    (hbound : d.scaleProduct rectangle *
      ((Ideal.absNorm G.literalFirstExtraction.val : ℝ) *
        (Ideal.absNorm G.ideals.second.val : ℝ)) ≤
      B ^ (2 * cap) * d.base ^ (a.n₁ + a.n₂ + a.z))
    (herror : B ^ (2 * cap) ≤ d.base ^ error) :
    d.scaleProduct rectangle ≤ d.base ^ (G.skeleton.rawDegree + error) := by
  sorry

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStepV2

end

set_option quotPrecheck false

/-!
# Original length products construct the actual frame's capacity binding

The actual frame keeps its original allocation and slot dictionary.
The original two extraction calculations supply the two norm factors
in its scale product; the fixed annulus threshold converts their
already computed product bound into the raw degree. The calibration's
parameter identity is literal for the constructed Fourier data.

The chosen row endpoint pays the two appearances of the original
active-column loss and the physical cutoff. It is never asserted to
be a lower window for every individual frequency. All endpoints and
the complete sixth-root support increment are constructed internally.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

/-- The original active column upper window enters the dual frequency
twice. Its cost is an explicit row error of this same geometry. -/
theorem literalParameters_secondWidth (columnLoss cutoff rootLength : ℝ) :
    G.literalRowParameter (2 * columnLoss + cutoff) + G.literalSupportParameter rootLength =
      secondCommonChildWidth Z
        (G.skeleton.A - G.skeleton.c - G.skeleton.w + columnLoss)
        (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo
        G.skeleton.Krow G.skeleton.g G.ideals.second.val G.ideals.secondOpposite.val
        G.ideals.unitPart.val G.ideals.nonunitPart.val + rootLength + cutoff := by
  sorry

namespace ScaleWindows

variable {G}

/-- Parameter identities transport only the two defining equations.
The actual endpoint values and their explicit errors stay literal. -/
def reparameterize {m q m' q' : ℝ} (W : G.ScaleWindows m q)
    (hm : m' = m) (hq : q' = q) : G.ScaleWindows m' q' where
  rowScale := W.rowScale
  supportScale := W.supportScale
  rowScale_pos := W.rowScale_pos
  supportScale_pos := W.supportScale_pos
  rowError := W.rowError
  supportError := W.supportError
  rowError_nonneg := W.rowError_nonneg
  supportError_nonneg := W.supportError_nonneg
  error_small := W.error_small
  row_lower := W.row_lower
  row_upper := W.row_upper
  support_lower := W.support_lower
  support_upper := W.support_upper
  row_parameter := by rw [hm]; exact W.row_parameter
  support_parameter := by rw [hq]; exact W.support_parameter

@[simp] theorem reparameterize_error {m q m' q' : ℝ} (W : G.ScaleWindows m q)
    (hm : m' = m) (hq : q' = q) : (W.reparameterize hm hq).error = W.error := rfl

end ScaleWindows

end OriginalNominalGeometry

namespace CanonicalLiteralRectangles.Atoms

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {H J : Type*} [Fintype J] [DecidableEq J]
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable (R : ActualSecondCorrelationRows A σ H J)
variable (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (rectangle : Bool) (L : Ideal (𝓞 K))
variable (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "f" =>
  (d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne

/-- Neither the negative right phase nor the actual allocation changes
the original pre-allocation occurrence dictionary. -/
def factorsOriginalSlots (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length) :
    OriginalSlotDictionary parent (f).source.length := by
  cases side <;> exact slots

/-- The full-kappa prime input uses the same original mesh bound on
the retained source slots, before any capacity deletion. -/
theorem factors_childLength_le (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length) (mesh : ℝ)
    (hfit : parent.geometry.fitsMesh mesh) (i : Fin (f).source.allocation.keep.card) :
    (f).source.childLength i ≤ mesh := by
  sorry

variable (D : ((d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne).source.Calibration
  (σ := σ) ω ψ)
variable (parent : MomentData K ω ψ) (a : RealParameters) (step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a
  ((d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base step)

/-- This is the length input of the already constructed actual frame.
`hbound` is the exact two-extraction norm-product result, before taking
logarithms; it is produced by the original direct/main/pool scale
theorems and `literalLeftAtoms_secondScale`/its right counterpart.
No raw-degree, width, final-child or capacity bound is assumed. -/
def factorsOriginalSixthLengths
    {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain centered parent a (f).source.base Y₁ Y₂ floor padding)
    (slots : OriginalSlotDictionary parent d.length)
    (direct : G.tag = .direct → parent.geometry.slotCount = 0)
    (cutoff rootLength : ℝ) (hcutoff : 0 ≤ cutoff) (hsmall : 2 * cutoff ≤ step)
    (hparameters : D.parameters = CanonicalLiteralAllocatedData.parameters d (f).allocation
      rectangle (G.literalRowParameter cutoff) (G.literalSupportParameter rootLength) a.κ)
    (annulus : ℝ) (cap : ℕ) (error : ℝ) (herr : 0 ≤ error)
    (hbound : d.scaleProduct rectangle *
      ((Ideal.absNorm G.literalFirstExtraction.val : ℝ) *
        (Ideal.absNorm G.ideals.second.val : ℝ)) ≤
      annulus ^ (2 * cap) * (f).source.base ^ (a.n₁ + a.n₂ + a.z))
    (hthreshold : annulus ^ (2 * cap) ≤ (f).source.base ^ error) :
    D.OriginalSixthLengthBinding parent a step G rootLength := by
  have hproduct : (f).source.scale₁ * (f).source.scale₂ * (f).source.base ^ (f).source.beforeLength ≤
      (f).source.base ^ (G.skeleton.rawDegree + error) := by
    have he := d.factors_source_scaleProduct (C := C) R side χ ideal hideal firstSign rectangle
      L selection hne
    cases side <;>
      exact he.trans_le (d.scaleProduct_le_originalRawDegree G annulus cap error rectangle
        hbound hthreshold)
  have hκ : D.parameters.κ = a.κ := by
    rw [hparameters]
    rfl
  have hm : D.parameters.m = G.literalRowParameter cutoff := by
    rw [hparameters]
    rfl
  have hq : D.parameters.q = G.literalSupportParameter rootLength := by
    rw [hparameters]
    rfl
  refine
    { slots := d.factorsOriginalSlots (C := C) R side χ ideal hideal firstSign rectangle L selection hne
        parent slots
      parent_z := domain.total_length
      parent_region := ⟨domain.kappa_lower, domain.kappa_upper, domain.capacity⟩
      kappa := hκ
      direct_slots := ?_
      scales := (G.literalEndpointWindows (f).source.base_gt_one cutoff rootLength hcutoff hsmall).reparameterize hm (congrArg (fun y : ℝ => y - rootLength) hq)
      rawScaleError := error
      rawScaleError_nonneg := herr
      original_scale_product := hproduct }
  · intro hd
    have hc : k ≤ parent.geometry.slotCount := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective slots.index slots.index.injective
    rw [direct hd] at hc
    exact Nat.eq_zero_of_le_zero hc

@[simp] theorem factorsOriginalSixthLengths_error
    {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain centered parent a (f).source.base Y₁ Y₂ floor padding)
    (slots : OriginalSlotDictionary parent d.length)
    (direct : G.tag = .direct → parent.geometry.slotCount = 0)
    (cutoff rootLength : ℝ) (hcutoff : 0 ≤ cutoff) (hsmall : 2 * cutoff ≤ step)
    (hparameters : D.parameters = CanonicalLiteralAllocatedData.parameters d (f).allocation
      rectangle (G.literalRowParameter cutoff) (G.literalSupportParameter rootLength) a.κ)
    (annulus : ℝ) (cap : ℕ) (error : ℝ) (herr : 0 ≤ error)
    (hbound : d.scaleProduct rectangle *
      ((Ideal.absNorm G.literalFirstExtraction.val : ℝ) *
        (Ideal.absNorm G.ideals.second.val : ℝ)) ≤
      annulus ^ (2 * cap) * (f).source.base ^ (a.n₁ + a.n₂ + a.z))
    (hthreshold : annulus ^ (2 * cap) ≤ (f).source.base ^ error) :
    (d.factorsOriginalSixthLengths (C := C) R side χ ideal hideal firstSign rectangle L selection hne
      D parent a step G domain slots direct cutoff rootLength hcutoff hsmall hparameters
      annulus cap error herr hbound hthreshold).scales.error = cutoff := by
  sorry

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStepV2

end

set_option quotPrecheck false

/-!
# A capacity scale error computed for every original rectangle

All rectangles receive their actual side normalization before source
activity is tested. An absent ordinary comparison can have arbitrary
positive comparison scales. Its raw degree is still bounded by the
explicit logarithm of its actual scale product; this possibly large
error is retained in its unused capacity cost.

On a rectangle satisfying the original two-extraction norm window,
the computed error equals the original small error exactly. Thus the
same selected normalization and child use the established small-error
mass formula. No inactive source, radius, calibration or slot is
replaced.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- This is a value computed from the actual original scales, not an
assumed raw-degree or capacity estimate. -/
def computedRawError (degree error : ℝ) (r : Bool) : ℝ :=
  max error (Real.logb d.base (d.scaleProduct r) - degree)

theorem computedRawError_nonneg (degree error : ℝ) (r : Bool) (herr : 0 ≤ error) :
    0 ≤ d.computedRawError degree error r := by
  sorry

theorem scaleProduct_le_computedRawError (degree error : ℝ) (r : Bool) :
    d.scaleProduct r ≤ d.base ^ (degree + d.computedRawError degree error r) := by
  sorry

theorem computedRawError_eq_of_scaleProduct_le (degree error : ℝ) (r : Bool)
    (hproduct : d.scaleProduct r ≤ d.base ^ (degree + error)) :
    d.computedRawError degree error r = error := by
  sorry

theorem computedRawError_eq_of_two_norms {a : RealParameters} {step : ℝ}
    (G : OriginalNominalGeometry (K := K) a d.base step)
    (annulus : ℝ) (cap : ℕ) (error : ℝ) (r : Bool)
    (hbound : d.scaleProduct r *
      ((Ideal.absNorm G.literalFirstExtraction.val : ℝ) *
        (Ideal.absNorm G.ideals.second.val : ℝ)) ≤
      annulus ^ (2 * cap) * d.base ^ (a.n₁ + a.n₂ + a.z))
    (hthreshold : annulus ^ (2 * cap) ≤ d.base ^ error) :
    d.computedRawError G.skeleton.rawDegree error r = error := by
  sorry

section Frame

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {H J : Type*} [Fintype J] [DecidableEq J]
variable {ω ψ : HeckeCharacter K}
variable (R : ActualSecondCorrelationRows A σ H J)
variable (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (rectangle : Bool) (L : Ideal (𝓞 K))
variable (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "f" =>
  (d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne

variable (D : ((d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne).source.Calibration
  (σ := σ) ω ψ)
variable (parent : MomentData K ω ψ) (a : RealParameters) (step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a
  ((d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base step)
variable {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered parent a
  ((d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
  Y₁ Y₂ floor padding)
variable (slots : OriginalSlotDictionary parent d.length)
variable (direct : G.tag = .direct → parent.geometry.slotCount = 0)
variable (cutoff rootLength : ℝ) (hcutoff : 0 ≤ cutoff) (hsmall : 2 * cutoff ≤ step)
variable (hparameters : D.parameters = CanonicalLiteralAllocatedData.parameters d
  ((d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne).allocation
  rectangle (G.literalRowParameter cutoff) (G.literalSupportParameter rootLength) a.κ)
variable (error : ℝ) (herr : 0 ≤ error)

/-- The actual original slot and endpoint data construct this binding
on every rectangle, including one whose source is identically zero. -/
def factorsOriginalSixthLengthsAll :
    D.OriginalSixthLengthBinding parent a step G rootLength := by
  have hproduct : (f).source.scale₁ * (f).source.scale₂ * (f).source.base ^ (f).source.beforeLength ≤
      (f).source.base ^ (G.skeleton.rawDegree +
        d.computedRawError G.skeleton.rawDegree error rectangle) := by
    have he := d.factors_source_scaleProduct (C := C) R side χ ideal hideal firstSign rectangle
      L selection hne
    cases side <;>
      exact he.trans_le (d.scaleProduct_le_computedRawError G.skeleton.rawDegree error rectangle)
  have hκ : D.parameters.κ = a.κ := by
    rw [hparameters]
    rfl
  have hm : D.parameters.m = G.literalRowParameter cutoff := by
    rw [hparameters]
    rfl
  have hq : D.parameters.q = G.literalSupportParameter rootLength := by
    rw [hparameters]
    rfl
  refine
    { slots := d.factorsOriginalSlots (C := C) R side χ ideal hideal firstSign rectangle L selection hne
        parent slots
      parent_z := domain.total_length
      parent_region := ⟨domain.kappa_lower, domain.kappa_upper, domain.capacity⟩
      kappa := hκ
      direct_slots := ?_
      scales := (G.literalEndpointWindows (f).source.base_gt_one cutoff rootLength hcutoff hsmall).reparameterize hm (congrArg (fun y : ℝ => y - rootLength) hq)
      rawScaleError := d.computedRawError G.skeleton.rawDegree error rectangle
      rawScaleError_nonneg := d.computedRawError_nonneg G.skeleton.rawDegree error rectangle herr
      original_scale_product := hproduct }
  intro hd
  have hc : k ≤ parent.geometry.slotCount := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective slots.index slots.index.injective
  rw [direct hd] at hc
  exact Nat.eq_zero_of_le_zero hc

@[simp] theorem factorsOriginalSixthLengthsAll_rawError :
    (d.factorsOriginalSixthLengthsAll R side χ ideal hideal firstSign rectangle L selection hne
      D parent a step G domain slots direct cutoff rootLength hcutoff hsmall hparameters error herr).rawScaleError = d.computedRawError G.skeleton.rawDegree error rectangle := rfl

@[simp] theorem factorsOriginalSixthLengthsAll_error :
    (d.factorsOriginalSixthLengthsAll R side χ ideal hideal firstSign rectangle L selection hne
      D parent a step G domain slots direct cutoff rootLength hcutoff hsmall hparameters error herr).scales.error = cutoff := by
  sorry

/-- With the original norm windows, the whole binding is identical
to the earlier small-error binding, including its same scale endpoints
and slot embedding. The proof fields agree by proof irrelevance. -/
theorem factorsOriginalSixthLengthsAll_eq
    (annulus : ℝ) (cap : ℕ)
    (hbound : d.scaleProduct rectangle *
      ((Ideal.absNorm G.literalFirstExtraction.val : ℝ) *
        (Ideal.absNorm G.ideals.second.val : ℝ)) ≤
      annulus ^ (2 * cap) * (f).source.base ^ (a.n₁ + a.n₂ + a.z))
    (hthreshold : annulus ^ (2 * cap) ≤ (f).source.base ^ error) :
    d.factorsOriginalSixthLengthsAll R side χ ideal hideal firstSign rectangle L selection hne
      D parent a step G domain slots direct cutoff rootLength hcutoff hsmall hparameters error herr =
    d.factorsOriginalSixthLengths R side χ ideal hideal firstSign rectangle L selection hne
      D parent a step G domain slots direct cutoff rootLength hcutoff hsmall hparameters
      annulus cap error herr hbound hthreshold := by
  sorry

end Frame
end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStepV2

end

