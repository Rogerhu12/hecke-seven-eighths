import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFirstDualCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalDualTerminalWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalParentSource

/-!
# First pure-dual windows for the fixed original row-ball test

The Gram profile is literally `(c i * star (c j)) • archTest 1`.
Its two finite seminorm bounds follow from the individual original
coefficient windows and the already fixed row-ball seminorm values.
The same columns, common blocks, complete masks and physical cutoff
then construct both original first terminal windows internally.

Only original ideal-factor, norm, radius and mask dictionaries remain
as inputs. In particular the profile is unrestricted at the additive
origin, and no terminal normalization or source estimate is supplied.
The final atom lemmas retain the two original comparison rectangles
and every prime slot before bounding their centered difference.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]

namespace CanonicalRowBall

/-- The scalar is a single original complex Gram coefficient. The
finite row-ball seminorm is fixed before its moving columns or scale. -/
theorem firstGramSeminorm_eq {ι : Type*} (c : ι → ℂ)
    (orders : Finset (ℕ × ℕ)) (i j : ι) :
    orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
        ((c i * star (c j)) • archTest K A.Sf 1) =
      ‖c i‖ * ‖c j‖ * terminalSeminorm A orders := by
  rw [map_smul_eq_mul, norm_mul, norm_star]

/-- Two individual original coefficient windows give the exact
profile exponent `2 * coefficientExponent`, including negative values. -/
theorem firstGramSeminorm_le {ι : Type*} (columns : Finset ι) (c : ι → ℂ)
    (orders : Finset (ℕ × ℕ)) (Z coefficientConstant coefficientExponent : ℝ)
    (hZ : 1 ≤ Z) (hconstant : 0 ≤ coefficientConstant)
    (hcoefficient : ∀ i ∈ columns,
      ‖c i‖ ≤ coefficientConstant * Z ^ coefficientExponent)
    (i : ι) (hi : i ∈ columns) (j : ι) (hj : j ∈ columns) :
    orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
        ((c i * star (c j)) • archTest K A.Sf 1) ≤
      (coefficientConstant ^ 2 * terminalSeminorm A orders) *
        Z ^ (2 * coefficientExponent) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  rw [firstGramSeminorm_eq]
  calc
    _ ≤ (coefficientConstant * Z ^ coefficientExponent) *
        (coefficientConstant * Z ^ coefficientExponent) * terminalSeminorm A orders :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (hcoefficient i hi) (hcoefficient j hj) (norm_nonneg _)
          (mul_nonneg hconstant (Real.rpow_nonneg hz.le _)))
        (terminalSeminorm_nonneg (A := A) orders)
    _ = _ := by
      rw [show (2 : ℝ) * coefficientExponent =
        coefficientExponent + coefficientExponent by ring, Real.rpow_add hz]
      ring

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]

/-- Construct the first pure-dual windows of the same original Gram
profiles. The modulus window uses the unweighted fixed test: multiplying
its profile by the original coefficient leaves the actual modulus
definitionally unchanged. Complete mask windows are supplied per actual
common block, so an external full-mask constructor can be used directly.
The optional `zeroRadius` supplies the independent sharp original
inverse-radius window; its default preserves the earlier constructor. -/
def firstDualOriginalWindows
    (C : A.GeneralArithmeticContext σ η hS)
    {ι : Type*} (columns : Finset ι) (I : ι → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel columns columns I I,
      FirstCommonCharacterBlock I I DE.val)
    (c : ι → ℂ) (radius : {r : ℝ // 0 < r})
    (M : Finset (HeightOneSpectrum A.R)) (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ)
    (Z X normBound Lmax Nsave decay productExponent coefficientConstant coefficientExponent
      maskExponent modulusExponent : ℝ)
    (hZ : 1 ≤ Z) (hproduct : 0 ≤ productExponent)
    (hconstant : 0 ≤ coefficientConstant)
    (factors : ι × ι → Fin k → Ideal (𝓞 K))
    (hfactors : Set.InjOn factors (columns ×ˢ columns : Set (ι × ι)))
    (hfactor : ∀ ij ∈ columns ×ˢ columns,
      PowerfulDiagonal.tupleIdeal (factors ij) = (I ij.1).val * (I ij.2).val)
    (hproductNorm : ∀ ij ∈ columns ×ˢ columns,
      (Ideal.absNorm ((I ij.1).val * (I ij.2).val) : ℝ) ≤ Z ^ productExponent)
    (hcoefficient : ∀ i ∈ columns,
      ‖c i‖ ≤ coefficientConstant * Z ^ coefficientExponent)
    (hmask : ∀ v ∈ firstZeroPairs columns columns I I,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          ((blocks v.1).mask M))).val ≤ Z ^ maskExponent)
    (hmodulus : ∀ v ∈ firstZeroPairs columns columns I I,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        ⟨((blocks v.1).pair hΓ C (fun _ _ => archTest K A.Sf 1) v.2.1 v.2.2).modulus,
          ((blocks v.1).pair hΓ C (fun _ _ => archTest K A.Sf 1)
            v.2.1 v.2.2).modulus_ne_zero⟩).val ≤ Z ^ modulusExponent)
    (hinverse : radius.val⁻¹ ≤ Z ^ modulusExponent)
    (hdegree : firstTailExponent k productExponent (2 * coefficientExponent)
      maskExponent modulusExponent ≤ Lmax)
    (hcutoff : X = Z ^ firstTailCutoffExponent Lmax Nsave decay)
    (maskIdeal : Ideal (𝓞 K)) (hmaskIdeal : maskIdeal ≠ 0)
    (hmaskNorm : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ normBound)
    (originalMask : OriginalMaskPrimeData M maskIdeal)
    (hcolumn : ∀ i ∈ columns, (Ideal.absNorm (I i).val : ℝ) ≤ Z ^ normBound)
    (zeroRadius : {exponent : ℝ // radius.val⁻¹ ≤ Z ^ exponent} :=
      ⟨modulusExponent, hinverse⟩) :
    FirstDualOriginalWindows (hΓ := hΓ) C columns I blocks
      (fun i j => (c i * star (c j)) • archTest K A.Sf 1) radius M
      sTail sZero k Z X normBound Lmax Nsave decay where
  productExponent := productExponent
  profileExponent := 2 * coefficientExponent
  maskExponent := maskExponent
  modulusExponent := modulusExponent
  tailProfileConstant := coefficientConstant ^ 2 * terminalSeminorm A sTail
  zeroProfileConstant := coefficientConstant ^ 2 * terminalSeminorm A sZero
  zeroProfileConstant_nonneg :=
    mul_nonneg (sq_nonneg coefficientConstant) (terminalSeminorm_nonneg sZero)
  zeroProfileExponent := 2 * coefficientExponent
  zeroInverseRadiusExponent := zeroRadius.val
  zero_inverse_radius := zeroRadius.property
  windows := {
    base_ge_one := hZ
    productExponent_nonneg := hproduct
    amplitude_nonneg :=
      mul_nonneg (sq_nonneg coefficientConstant) (terminalSeminorm_nonneg sTail)
    factors := factors
    factors_injective := hfactors
    factor_product := hfactor
    product_norm := hproductNorm
    profile_seminorm := by
      intro v hv
      have hm := (mem_firstZeroPairs columns columns I I v).mp hv
      exact firstGramSeminorm_le columns c sTail Z coefficientConstant coefficientExponent
        hZ hconstant hcoefficient v.2.1 hm.1 v.2.2 hm.2.1
    mask_norm := hmask
    modulus_norm := by
      intro v hv
      exact hmodulus v hv
    inverse_radius := hinverse }
  exponent_bound := hdegree
  cutoff_eq := hcutoff
  zero_profile := by
    intro v hv
    have hm := (mem_firstZeroPairs columns columns I I v).mp hv
    exact firstGramSeminorm_le columns c sZero Z coefficientConstant coefficientExponent
      hZ hconstant hcoefficient v.2.1 hm.1 v.2.2 hm.2.1
  maskIdeal := maskIdeal
  mask_ne_zero := hmaskIdeal
  mask_norm := hmaskNorm
  original_mask := originalMask
  column_norm := hcolumn

end CanonicalRowBall

namespace ParentRawAtoms.ConstantValues

variable {Q : Type*} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable {raw : ParentRawAtoms Q d a Z t Y₁ Y₂}
variable (values : raw.ConstantValues)

/-- Only individual original atoms are bounded. Both comparison
scales and every slot remain in the displayed product. -/
theorem rectangle_norm_le_original_atoms
    (leftBound rightBound : Bool → ℝ) (primeBound : Fin d.geometry.slotCount → ℝ)
    (hleft : ∀ comparison, 0 ≤ leftBound comparison)
    (hright : ∀ comparison, 0 ≤ rightBound comparison)
    (hleftAtom : ∀ comparison I, I ∈ raw.leftColumns →
      ‖values.left comparison I‖ ≤ leftBound comparison)
    (hrightAtom : ∀ comparison I, I ∈ raw.rightColumns →
      ‖values.right comparison I‖ ≤ rightBound comparison)
    (hprimeAtom : ∀ i p, p ∈ raw.slotColumns i → ‖values.prime i p‖ ≤ primeBound i)
    (comparison : Bool) (v : raw.Column) (hv : v ∈ raw.columns) :
    ‖values.rectangle comparison v‖ ≤
      leftBound comparison * rightBound comparison * ∏ i, primeBound i := by
  have hm : (v.1.1 ∈ raw.leftColumns ∧ v.1.2 ∈ raw.rightColumns) ∧
      (∀ i, v.2 i ∈ raw.slotColumns i) := by
    simpa only [ParentRawAtoms.columns, childCartesianColumns,
      Finset.mem_product, Fintype.mem_piFinset] using hv
  rw [rectangle, norm_mul, norm_mul, norm_prod]
  exact mul_le_mul
    (mul_le_mul (hleftAtom comparison _ hm.1.1) (hrightAtom comparison _ hm.1.2)
      (norm_nonneg _) (hleft comparison))
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hprimeAtom i _ (hm.2 i)))
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (mul_nonneg (hleft comparison) (hright comparison))

/-- The centered coefficient is estimated from its two literal
rectangles; the ordinary case retains just the original first one. -/
theorem coefficient_norm_le_original_atoms
    (leftBound rightBound : Bool → ℝ) (primeBound : Fin d.geometry.slotCount → ℝ)
    (hleft : ∀ comparison, 0 ≤ leftBound comparison)
    (hright : ∀ comparison, 0 ≤ rightBound comparison)
    (hleftAtom : ∀ comparison I, I ∈ raw.leftColumns →
      ‖values.left comparison I‖ ≤ leftBound comparison)
    (hrightAtom : ∀ comparison I, I ∈ raw.rightColumns →
      ‖values.right comparison I‖ ≤ rightBound comparison)
    (hprimeAtom : ∀ i p, p ∈ raw.slotColumns i → ‖values.prime i p‖ ≤ primeBound i)
    (centered : Bool) (v : raw.Column) (hv : v ∈ raw.columns) :
    ‖values.coefficient centered v‖ ≤
      (leftBound false * rightBound false +
        if centered then leftBound true * rightBound true else 0) * ∏ i, primeBound i := by
  have hrectangle := values.rectangle_norm_le_original_atoms leftBound rightBound primeBound
    hleft hright hleftAtom hrightAtom hprimeAtom
  cases centered with
  | false =>
      change ‖values.rectangle false v - 0‖ ≤
        (leftBound false * rightBound false + 0) * ∏ i, primeBound i
      simpa only [sub_zero, add_zero] using hrectangle false v hv
  | true =>
      change ‖values.rectangle false v - values.rectangle true v‖ ≤
        (leftBound false * rightBound false + leftBound true * rightBound true) *
          ∏ i, primeBound i
      calc
        _ ≤ ‖values.rectangle false v‖ + ‖values.rectangle true v‖ := norm_sub_le _ _
        _ ≤ leftBound false * rightBound false * (∏ i, primeBound i) +
            leftBound true * rightBound true * (∏ i, primeBound i) :=
          add_le_add (hrectangle false v hv) (hrectangle true v hv)
        _ = _ := by ring

/-- A uniform bound on the individual original atoms pays both
rectangles, including the case of no prime slots. -/
theorem coefficient_norm_le_uniform_atom_bound
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hleftAtom : ∀ comparison I, I ∈ raw.leftColumns →
      ‖values.left comparison I‖ ≤ bound)
    (hrightAtom : ∀ comparison I, I ∈ raw.rightColumns →
      ‖values.right comparison I‖ ≤ bound)
    (hprimeAtom : ∀ i p, p ∈ raw.slotColumns i → ‖values.prime i p‖ ≤ bound)
    (centered : Bool) (v : raw.Column) (hv : v ∈ raw.columns) :
    ‖values.coefficient centered v‖ ≤ 2 * bound ^ (d.geometry.slotCount + 2) := by
  have h := values.coefficient_norm_le_original_atoms
    (fun _ => bound) (fun _ => bound) (fun _ => bound)
    (fun _ => hbound) (fun _ => hbound) hleftAtom hrightAtom hprimeAtom centered v hv
  have hsum : bound * bound + (if centered then bound * bound else 0) ≤
      2 * (bound * bound) := by
    cases centered with
    | false =>
        change bound * bound + 0 ≤ 2 * (bound * bound)
        nlinarith [sq_nonneg bound]
    | true =>
        change bound * bound + bound * bound ≤ 2 * (bound * bound)
        linarith
  have hprod : (∏ _i : Fin d.geometry.slotCount, bound) =
      bound ^ d.geometry.slotCount := by simp
  calc
    _ ≤ (bound * bound + (if centered then bound * bound else 0)) *
        (∏ _i : Fin d.geometry.slotCount, bound) := h
    _ ≤ 2 * (bound * bound) * (∏ _i : Fin d.geometry.slotCount, bound) :=
      mul_le_mul_of_nonneg_right hsum (Finset.prod_nonneg fun _ _ => hbound)
    _ = _ := by rw [hprod, pow_add, pow_two]; ring

/-- The degree can be fixed from the original slot cap before the
moving model or its coefficient carrier is chosen. -/
theorem coefficient_norm_le_original_atom_cap
    (cap : ℕ) (hslots : d.geometry.slotCount ≤ cap)
    (bound : ℝ) (hbound : 1 ≤ bound)
    (hleftAtom : ∀ comparison I, I ∈ raw.leftColumns →
      ‖values.left comparison I‖ ≤ bound)
    (hrightAtom : ∀ comparison I, I ∈ raw.rightColumns →
      ‖values.right comparison I‖ ≤ bound)
    (hprimeAtom : ∀ i p, p ∈ raw.slotColumns i → ‖values.prime i p‖ ≤ bound)
    (centered : Bool) (v : raw.Column) (hv : v ∈ raw.columns) :
    ‖values.coefficient centered v‖ ≤ 2 * bound ^ (cap + 2) :=
  (values.coefficient_norm_le_uniform_atom_bound bound (zero_le_one.trans hbound)
    hleftAtom hrightAtom hprimeAtom centered v hv).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hbound (Nat.add_le_add_right hslots 2)) (by norm_num))

end ParentRawAtoms.ConstantValues

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalRowBall.firstGramSeminorm_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalRowBall.firstDualOriginalWindows
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.ConstantValues.coefficient_norm_le_original_atoms
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.ConstantValues.coefficient_norm_le_original_atom_cap
