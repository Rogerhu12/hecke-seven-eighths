import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalParentTuples
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMovingCoefficientBound
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalActiveColumnNorm
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalUnionColumnNorm
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalMovingParentSource

/-!
# First terminal windows from the actual original atoms

The raw single-profile windows bound the actual whole centered
coefficient with its original negative central exponent. A column in
the original Cartesian carrier supplies an original paired row, so no
nonempty-row premise is needed to use the norm-profile identities.

The constructor below then installs the original injective padded
factor tuple, the coarse full-carrier tail window and the independent
sharp nonzero-profile product window. Its two coefficient seminorm
constants come from the fixed original row-ball test. The columns,
canonical common blocks, full centered coefficient and Gram profiles
are the original ones throughout.

Only the genuine physical mask, modulus, inverse-radius and chosen
cutoff windows remain for the full-mask provider. No whole coefficient,
pair-product estimate, final terminal bound or source comparison is an
input. The actual moving-recipe wrapper proves its arithmetic atom
bounds and leaves these same physical windows as its arguments.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments MeasureTheory

variable {K : Type} [Field K] [NumberField K]

private theorem original_first_atom_norm_le (c f : ℂ) (B : ℝ)
    (hc : ‖c‖ ≤ 1) (hf : ‖f‖ ≤ B) : ‖c * f‖ ≤ B := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul hc hf (norm_nonneg _) zero_le_one

namespace ParentConstantAtoms

section OriginalProfiles

variable {Q : Type*} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (atoms : ParentConstantAtoms Q d a Z t)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {B : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window
  (OriginalProfileAtomBounds.profileOrders orders) d B)

include profiles

/-- An actual column contains an original plain-support witness row.
The two row-independent norm profiles therefore inherit their bounds
from the same original single-profile record, even when the original
carrier may be empty. -/
theorem original_profile_bounds_of_column
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain) (ht : t ∈ heightDomain)
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).columns) :
    (∀ x, ‖atoms.leftProfile x‖ ≤ B) ∧
      (∀ x, ‖atoms.rightProfile x‖ ≤ B) ∧
      (∀ i x, ‖(d.geometry.slots i).profile t x‖ ≤ B) := by
  have hm := Finset.mem_product.mp hv
  have hplain := Finset.mem_product.mp hm.1
  obtain ⟨u, hu, _⟩ := Finset.mem_biUnion.mp hplain.1
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [← atoms.left_profile u hu, profiles.left_eq]
    exact (OriginalProfileAtomBounds.norm_le_profileOrders orders (profiles.leftRep u t) x).trans
      (profiles.left_bound u (hrows u hu) t ht)
  · intro x
    rw [← atoms.right_profile u hu, profiles.right_eq]
    exact (OriginalProfileAtomBounds.norm_le_profileOrders orders (profiles.rightRep u t) x).trans
      (profiles.right_bound u (hrows u hu) t ht)
  · intro i x
    rw [profiles.prime_eq]
    exact (OriginalProfileAtomBounds.norm_le_profileOrders orders (profiles.primeRep i t) x).trans
      (profiles.prime_bound i t ht)

/-- The original arithmetic and profile atoms prove the whole
coefficient window. Both rectangles retain their central factors and
the same product of comparison scales. -/
theorem coefficient_norm_le_raw_profile_window
    (hleftArithmetic : ∀ I, ‖atoms.leftArithmetic I‖ ≤ 1)
    (hrightArithmetic : ∀ I, ‖atoms.rightArithmetic I‖ ≤ 1)
    (hprimeArithmetic : ∀ i p, ‖atoms.primeArithmetic i p‖ ≤ 1)
    (cap : ℕ) (hcap : d.geometry.slotCount ≤ cap) (hB : 1 ≤ B) (hZ : 0 < Z)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain) (ht : t ∈ heightDomain)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).columns) :
    ‖(atoms.values Y₁ Y₂).coefficient centered v‖ ≤
      (2 * B ^ (cap + 2)) * Z ^ (-(a.n₁ + a.n₂ + d.geometry.totalLength) / 2) := by
  obtain ⟨hleft, hright, hprime⟩ := atoms.original_profile_bounds_of_column profiles hrows ht v hv
  exact atoms.coefficient_norm_le_original_central_cap cap hcap B hB hZ
    (fun comparison I _ => original_first_atom_norm_le _ _ B (hleftArithmetic I)
      (hleft (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁))))
    (fun comparison I _ => original_first_atom_norm_le _ _ B (hrightArithmetic I)
      (hright (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂))))
    (fun i p _ => original_first_atom_norm_le _ _ B (hprimeArithmetic i p)
      (hprime i ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)))
    centered hY₁ hcomparison v hv

end OriginalProfiles
end ParentConstantAtoms

namespace ParentRawAtoms

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {Γ : Subgroup A.U} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (raw : ParentRawAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂)

/-- A transparent name for exactly the common blocks used by the
canonical first source. No block, ideal or generator is chosen again. -/
abbrev originalFirstBlocks (C : A.GeneralArithmeticContext σ η hS) :
    ∀ DE : FirstZeroLabel raw.exteriorColumns raw.exteriorColumns
      raw.columnExterior raw.columnExterior,
      FirstCommonCharacterBlock raw.columnExterior raw.columnExterior DE.val :=
  fun DE => canonicalFirstCommonBlock C raw.exteriorColumns raw.exteriorColumns
    raw.columnExterior raw.columnExterior DE.val DE.property

end ParentRawAtoms

namespace ParentConstantAtoms

section FirstWindows

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (atoms : ParentConstantAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t)

/-- Construct both first terminal windows on the unchanged actual
source. The tuple injection, coefficients and two distinct ideal-product
windows are conclusions of the original atom dictionaries. The physical
mask, modulus and inverse-radius bounds remain literal original inputs. -/
def canonicalOriginalFirstWindows
    (C : A.GeneralArithmeticContext σ η hS)
    (hleftArithmetic : ∀ I, ‖atoms.leftArithmetic I‖ ≤ 1)
    (hrightArithmetic : ∀ I, ‖atoms.rightArithmetic I‖ ≤ 1)
    (hprimeArithmetic : ∀ i p, ‖atoms.primeArithmetic i p‖ ≤ 1)
    (cap : ℕ) (orders : Finset (ℕ × ℕ))
    (B annulus loss leftExponent rightExponent : ℝ)
    (hB : 1 ≤ B) (hannulus : 1 ≤ annulus) (hloss : 0 ≤ loss)
    (hcap : d.geometry.slotCount ≤ cap)
    (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss)
    (centered : Bool) {floor padding : ℝ}
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hleftExponent : a.n₁ ≤ leftExponent) (hrightExponent : a.n₂ ≤ rightExponent)
    (hY₁le : Y₁ ≤ Z ^ leftExponent) (hY₂le : Y₂ ≤ Z ^ rightExponent)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window
      (OriginalProfileAtomBounds.profileOrders orders) d B)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
    (sTail sZero : Finset (ℕ × ℕ))
    (X normBound Lmax Nsave decay maskExponent modulusExponent zeroRadiusExponent : ℝ)
    (hcolumnExponent : leftExponent + rightExponent + d.geometry.totalLength + loss ≤ normBound)
    (hmask : ∀ v ∈ firstZeroPairs (atoms.raw Y₁ Y₂).exteriorColumns
        (atoms.raw Y₁ Y₂).exteriorColumns (atoms.raw Y₁ Y₂).columnExterior
        (atoms.raw Y₁ Y₂).columnExterior,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          (((atoms.raw Y₁ Y₂).originalFirstBlocks C v.1).mask M))).val ≤ Z ^ maskExponent)
    (hmodulus : ∀ v ∈ firstZeroPairs (atoms.raw Y₁ Y₂).exteriorColumns
        (atoms.raw Y₁ Y₂).exteriorColumns (atoms.raw Y₁ Y₂).columnExterior
        (atoms.raw Y₁ Y₂).columnExterior,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        ⟨(((atoms.raw Y₁ Y₂).originalFirstBlocks C v.1).pair hΓ C
          (fun _ _ => CanonicalRowBall.archTest K A.Sf 1) v.2.1 v.2.2).modulus,
         (((atoms.raw Y₁ Y₂).originalFirstBlocks C v.1).pair hΓ C
          (fun _ _ => CanonicalRowBall.archTest K A.Sf 1) v.2.1 v.2.2).modulus_ne_zero⟩).val ≤
            Z ^ modulusExponent)
    (hinverse : radius.val⁻¹ ≤ Z ^ modulusExponent)
    (hzeroInverse : radius.val⁻¹ ≤ Z ^ zeroRadiusExponent)
    (hdegree : firstTailExponent (2 * (cap + 2))
      (2 * (leftExponent + rightExponent + d.geometry.totalLength + loss))
      (2 * (-(a.n₁ + a.n₂ + d.geometry.totalLength) / 2))
      maskExponent modulusExponent ≤ Lmax)
    (hcutoff : X = Z ^ firstTailCutoffExponent Lmax Nsave decay)
    (maskIdeal : Ideal (𝓞 K)) (hmaskIdeal : maskIdeal ≠ 0)
    (hmaskNorm : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ normBound)
    (originalMask : OriginalMaskPrimeData M maskIdeal) :
    FirstDualOriginalWindows (hΓ := hΓ) C
      (atoms.raw Y₁ Y₂).exteriorColumns (atoms.raw Y₁ Y₂).columnExterior
      ((atoms.raw Y₁ Y₂).originalFirstBlocks C)
      (fun i j => ((atoms.values Y₁ Y₂).coefficient centered i *
        star ((atoms.values Y₁ Y₂).coefficient centered j)) • CanonicalRowBall.archTest K A.Sf 1)
      radius M sTail sZero (2 * (cap + 2)) Z X normBound Lmax Nsave decay := by
  let raw := atoms.raw Y₁ Y₂
  have hz : 0 < Z := zero_lt_one.trans domain.scale
  have hlength : 0 ≤ d.geometry.totalLength :=
    Finset.sum_nonneg (fun i _ => (d.geometry.slots i).length_pos.le)
  have hcoarse : 0 ≤ leftExponent + rightExponent + d.geometry.totalLength + loss :=
    add_nonneg (add_nonneg (add_nonneg
      (domain.plain_left_nonneg.trans hleftExponent)
      (domain.plain_right_nonneg.trans hrightExponent)) hlength) hloss
  have hsharp : 0 ≤ a.n₁ + a.n₂ + d.geometry.totalLength + loss :=
    add_nonneg (add_nonneg (add_nonneg domain.plain_left_nonneg domain.plain_right_nonneg)
      hlength) hloss
  have htuple := raw.original_first_tail_pair_data cap hcap
    raw.exteriorColumns raw.exteriorColumns (fun _ h => h) (fun _ h => h)
  have hcolumn (i : raw.Column) (hi : i ∈ raw.exteriorColumns) :
      (Ideal.absNorm (raw.columnExterior i).val : ℝ) ≤
        Z ^ (leftExponent + rightExponent + d.geometry.totalLength + loss) :=
    raw.original_union_column_norm_le_power profiles cap annulus loss leftExponent rightExponent
      hannulus hcap hannulusZ hz hY₁ hY₂
      (Real.rpow_le_rpow_of_exponent_le domain.scale.le hleftExponent)
      (Real.rpow_le_rpow_of_exponent_le domain.scale.le hrightExponent)
      hY₁le hY₂le hrows ht hwindow i hi
  have hpair (ij : raw.Column × raw.Column) (hij : ij ∈ raw.exteriorColumns ×ˢ raw.exteriorColumns) :
      (Ideal.absNorm ((raw.columnExterior ij.1).val * (raw.columnExterior ij.2).val) : ℝ) ≤
        Z ^ (2 * (leftExponent + rightExponent + d.geometry.totalLength + loss)) := by
    rw [map_mul, Nat.cast_mul]
    exact (mul_le_mul (hcolumn ij.1 (Finset.mem_product.mp hij).1)
      (hcolumn ij.2 (Finset.mem_product.mp hij).2) (Nat.cast_nonneg _)
      (Real.rpow_nonneg hz.le _)).trans_eq
        (by rw [← Real.rpow_add hz]; congr 1; ring)
  have hcoefficient (i : raw.Column) (hi : i ∈ raw.exteriorColumns) :
      ‖(atoms.values Y₁ Y₂).coefficient centered i‖ ≤
        (2 * B ^ (cap + 2)) * Z ^ (-(a.n₁ + a.n₂ + d.geometry.totalLength) / 2) :=
    atoms.coefficient_norm_le_raw_profile_window profiles
      hleftArithmetic hrightArithmetic hprimeArithmetic cap hcap hB hz hrows ht centered
      domain.comparison_scale_left_nonneg domain.comparison_product_eq_power
      i (Finset.mem_filter.mp hi).1
  exact CanonicalRowBall.firstDualOriginalWindows C raw.exteriorColumns raw.columnExterior
    (raw.originalFirstBlocks C) ((atoms.values Y₁ Y₂).coefficient centered) radius M sTail sZero
    (2 * (cap + 2)) Z X normBound Lmax Nsave decay
    (2 * (leftExponent + rightExponent + d.geometry.totalLength + loss))
    (2 * B ^ (cap + 2)) (-(a.n₁ + a.n₂ + d.geometry.totalLength) / 2)
    maskExponent modulusExponent domain.scale.le (mul_nonneg (by norm_num) hcoarse)
    (mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans hB) _))
    (raw.originalPairIdealFactors cap hcap) htuple.1 htuple.2 hpair hcoefficient
    hmask hmodulus hinverse hdegree hcutoff maskIdeal hmaskIdeal hmaskNorm originalMask
    (fun i hi => (hcolumn i hi).trans
      (Real.rpow_le_rpow_of_exponent_le domain.scale.le hcolumnExponent))
    ⟨zeroRadiusExponent, hzeroInverse⟩
    ⟨2 * (a.n₁ + a.n₂ + d.geometry.totalLength + loss), mul_nonneg (by norm_num) hsharp,
      fun ij hij hp => atoms.original_active_gram_pair_norm_of_domain profiles
        cap annulus loss hannulus hcap hannulusZ hrows ht hwindow domain
        (CanonicalRowBall.archTest K A.Sf 1) ij hij hp⟩

end FirstWindows
end ParentConstantAtoms

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K} {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- The actual moving and fixed masks, and the original correction
character, are bounded internally before the complete coefficient. The
raw profile windows are used only on an original row supplied by the
actual column's carrier membership. -/
theorem coefficient_norm_le_raw_profile_window
    (W : NormProfileRecipe data) (ξ : X)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 0 < Z)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap) (B : ℝ) (hB : 1 ≤ B)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
    {orders : Finset (ℕ × ℕ)}
    (profiles : RawProfileWindow rowDomain heightDomain window
      (OriginalProfileAtomBounds.profileOrders orders) (data ξ) B)
    (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain) (ht : t ∈ heightDomain)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (v : (((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t).raw Y₁ Y₂).Column)
    (hv : v ∈ (((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t).raw Y₁ Y₂).columns) :
    ‖(((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t).values Y₁ Y₂).coefficient centered v‖ ≤
      (2 * B ^ (cap + 2)) *
        Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) / 2) :=
  ((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t).coefficient_norm_le_raw_profile_window
    profiles (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
    (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap hB hZ hrows ht centered hY₁ hcomparison v hv

section FirstWindows

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]

/-- The complete factory for the original moving arithmetic recipe.
Partial application fills all three arithmetic atom bounds internally;
the remaining arguments are exactly the original profile, scale,
physical-mask, modulus, radius and cutoff windows of the preceding
constructor. Its result uses the same original sixth-unit orbit source. -/
def canonicalOriginalFirstWindows
    (W : NormProfileRecipe data) (ξ : X) (a : RealParameters) (Z t Y₁ Y₂ : ℝ)
    (C : A.GeneralArithmeticContext σ η hS) :=
  ParentConstantAtoms.canonicalOriginalFirstWindows
    (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (Y₁ := Y₁) (Y₂ := Y₂)
    ((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t) C
    (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
    (Q.arithmeticAtoms_prime_norm_le_one ξ)

end FirstWindows
end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_profile_bounds_of_column
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.coefficient_norm_le_raw_profile_window
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.canonicalOriginalFirstWindows
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.coefficient_norm_le_raw_profile_window
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalOriginalFirstWindows
