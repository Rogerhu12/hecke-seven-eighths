import HeckeSkeleton.Moments.MOM_INV_STEP.LocalSource
import HeckeSkeleton.Moments.MOM_INV_STEP.CubeLabels
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualFiniteSource
import HeckeGeneral.Analysis.MarkedThetaReflection

/-!
# The cube identity on actual selected ideal generators

`AllowedGeneratorInput` is the explicit MOM_BASE compatibility input.
Its reciprocity law identifies the selected-generator numerator row
with the denominator row. Actual denominator multiplicativity then
produces a genuine monoid row on exterior ideals, including at bad
residues, and connects the cube table to the selected canonical
generators used in the marked block.

The monoid is an explicit submonoid; this file adds no global instance
for the pre-existing `ExteriorIdeal` type.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalIdealRow

open NumberField IsDedekindDomain
  HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubeAlgebra
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset

abbrev exteriorMonoid : Submonoid (NonzeroIdeal K) where
  carrier := {I | ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ Sset}
  one_mem' := by
    intro p hp
    change p.asIdeal ∣ (1 : Ideal (𝓞 K)) at hp
    exact (p.irreducible.not_isUnit (isUnit_of_dvd_one hp)).elim
  mul_mem' := by
    intro I J hI hJ p hp
    rcases p.prime.dvd_mul.mp hp with hp | hp
    · exact hI p hp
    · exact hJ p hp

local notation "E" => exteriorMonoid K S

/-- Explicit packaging avoids relying on elaborator coercion search
between the existing subtype and the carrier of its submonoid. -/
def toExterior (I : E) : Ext := ⟨I.val, I.property⟩

def ofExterior (I : Ext) : E := ⟨I.val, I.property⟩

@[simp] theorem toExterior_val (I : E) : (toExterior K S I).val = I.val := rfl

@[simp] theorem ofExterior_val (I : Ext) : (ofExterior K S I).val = I.val := rfl

@[simp] theorem toExterior_ofExterior (I : Ext) :
    toExterior K S (ofExterior K S I) = I := rfl

@[simp] theorem toExterior_mul (I J : E) :
    toExterior K S (I * J) =
      exteriorMul K Sset (toExterior K S I) (toExterior K S J) := rfl

def primeIdeal (p : ExteriorPrime K Sset) : E :=
  ofExterior K S (exteriorPrimeIdeal K Sset p)

@[simp] theorem primeIdeal_val (p : ExteriorPrime K Sset) :
    (primeIdeal K S p).val.val = p.val.asIdeal := rfl

def idealValue : E →* Ideal (𝓞 K) :=
  (nonZeroDivisors (Ideal (𝓞 K))).subtype.comp (exteriorMonoid K S).subtype

@[simp] theorem idealValue_apply (I : E) : idealValue K S I = I.val.val := rfl

theorem product_idealValue {ι : Type*} (p : ι → E) (B : Finset ι) (e : ι → ℕ) :
    (primeProduct p B e).val.val =
      primeProduct (fun i => (p i).val.val) B e := by
  change idealValue K S (primeProduct p B e) = _
  simp only [primeProduct, map_prod, map_pow, idealValue_apply]

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

def generator (I : E) : OS := D.generator (toExterior K S I)

@[simp] theorem generator_ofExterior (I : Ext) :
    generator K S D (ofExterior K S I) = D.generator I := rfl

theorem generator_contraction (I : E) :
    sIntegerModulusContraction K Sset (generator K S D I) = I.val.val := by
  unfold generator
  unfold sIntegerModulusContraction
  rw [D.generator_span]
  exact under_map_coprime_sIntegerIdeal K Sset I.val.val
    (sexticIdeal_coprime_S K Sset I.val.val I.property)

/-- Build the monoid row using the already proved denominator
multiplicativity. Reciprocity below identifies it with the literal
canonical numerator row, avoiding inference between two subtype carriers. -/
def row (_compatibility : AllowedGeneratorInput K Sset D) (n : Ext) : E →* ℂ where
  toFun I := sIntegerSexticIdealEvaluation K Sset D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) (D.generator n)
  map_one' := by
    exact sIntegerSexticIdealEvaluation_top K Sset
      D.root6 D.primitive6 D.embedding (1 : E).property
      (fun p hp => D.away_six p ((1 : E).property p hp)) (D.generator n)
  map_mul' := by
    intro I J
    exact ActualFiniteSource.PrimeBlock.actual_ideal_mul_denominator K Sset
      D.root6 D.primitive6 D.embedding I.val.val J.val.val
      (nonZeroDivisors.coe_ne_zero I.val) (nonZeroDivisors.coe_ne_zero J.val)
      (fun p hp => hp.elim (I.property p) (J.property p))
      (fun p hp => D.away_six p (hp.elim (I.property p) (J.property p))) (D.generator n)

@[simp] theorem row_apply (n : Ext) (I : E) :
    row K S D hallowed n I = idealSymbol K Sset D n (generator K S D I) := by
  exact hallowed.reciprocity (toExterior K S I) n

include hallowed in
theorem fourth_label_mul (n : Ext) (I J : E) :
    idealSymbol K Sset D n (generator K S D (I * J)) ^ 4 =
      idealSymbol K Sset D n (generator K S D I) ^ 4 *
        idealSymbol K Sset D n (generator K S D J) ^ 4 := by
  have h := congrArg (fun w : ℂ => w ^ 4) ((row K S D hallowed n).map_mul I J)
  simpa only [row_apply, mul_pow] using h

include hallowed in
/-- Canonical generators of products and products of prime generators
give exactly the same scalar row, with no nonvanishing assumption. -/
theorem generator_product_row (n : Ext) {ι : Type*}
    (p : ι → E) (B : Finset ι) (e : ι → ℕ) :
    idealSymbol K Sset D n (generator K S D (primeProduct p B e)) =
      idealSymbol K Sset D n (∏ i ∈ B, generator K S D (p i) ^ e i) := by
  rw [← row_apply K S D hallowed n (primeProduct p B e)]
  change row K S D hallowed n (∏ i ∈ B, p i ^ e i) =
    LocalSource.actualRow K Sset D.root6 D.primitive6 D.embedding n.val.val
      (nonZeroDivisors.coe_ne_zero n.val) n.property
      (fun p hp => D.away_six p (n.property p hp))
        (∏ i ∈ B, generator K S D (p i) ^ e i)
  simp only [map_prod, map_pow, row_apply, LocalSource.actualRow_apply, idealSymbol]

include hallowed in
theorem prime_generator_product_row (n : Ext) {ι : Type*}
    (p : ι → ExteriorPrime K Sset) (B : Finset ι) (e : ι → ℕ) :
    idealSymbol K Sset D n
      (generator K S D (primeProduct (fun i => primeIdeal K S (p i)) B e)) =
      idealSymbol K Sset D n
        (∏ i ∈ B, D.generator (exteriorPrimeIdeal K Sset (p i)) ^ e i) :=
  generator_product_row K S D hallowed n (fun i => primeIdeal K S (p i)) B e

theorem row_mask (n : Ext) (I : E) :
    sixthMask (row K S D hallowed n) I =
      if IsCoprime n.val.val I.val.val then 1 else 0 := by
  have h := LocalSource.actualRow_mask K Sset D.root6 D.primitive6 D.embedding n.val.val
    (nonZeroDivisors.coe_ne_zero n.val) n.property
      (fun p hp => D.away_six p (n.property p hp)) (generator K S D I)
  rw [generator_contraction] at h
  change row K S D hallowed n I ^ 6 = _
  rw [row_apply]
  exact h

theorem row_zero_or_one (n : Ext) (I : E) :
    row K S D hallowed n I ^ 6 = 0 ∨ row K S D hallowed n I ^ 6 = 1 := by
  have h := row_mask K S D hallowed n I
  by_cases hc : IsCoprime n.val.val I.val.val
  · right
    simpa only [sixthMask, if_pos hc] using h
  · left
    simpa only [sixthMask, if_neg hc] using h

include hallowed in
/-- The original fourth-power label enters the same inverse row as f².
The proof includes a vanishing label character, so no extra coprimality
assumption is needed. -/
theorem fourth_label_absorb_row (n : Ext) (f z : E) :
    idealSymbol K Sset D n (generator K S D f) ^ 4 *
        star (idealSymbol K Sset D n (generator K S D z)) =
      star (idealSymbol K Sset D n (generator K S D (z * f ^ 2))) := by
  let χ := row K S D hallowed n
  have hfour : χ f ^ 4 = star (χ f ^ 2) := by
    rcases row_zero_or_one K S D hallowed n f with hz | hz
    · have hf0 : χ f = 0 := (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hz
      simp only [hf0, zero_pow (by decide : (4 : ℕ) ≠ 0),
        zero_pow (by decide : (2 : ℕ) ≠ 0), star_zero]
    · have hn : ‖χ f ^ 2‖ = 1 := by
        rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one hz (by decide), one_pow]
      have hm : χ f ^ 4 * χ f ^ 2 = 1 := by
        simpa only [← pow_add] using hz
      rw [Complex.star_def]
      exact (eq_inv_of_mul_eq_one_left hm).trans (Complex.inv_eq_conj hn)
  have h : χ f ^ 4 * star (χ z) = star (χ (z * f ^ 2)) := by
    rw [map_mul, map_pow, star_mul, hfour]
    exact mul_comm _ _
  simpa only [χ, row_apply] using h

include hallowed in
/-- The first surviving factor uses the actual selected generator of J
and the actual ideal q₀ puncture. No ideal is assumed principal over 𝓞 K. -/
theorem first_pass_label_identity (n : Ext) {ι : Type*}
    (p : ι → E) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (side : Bool) :
    (if IsCoprime n.val.val (cubeRadical p B).val.val then 1 else 0) *
      idealSymbol K Sset D n (generator K S D (aLabel p B (if side then ε₂ else ε₁))) ^ 4 *
      idealSymbol K Sset D n (generator K S D (crtLabel p B v ε₁ ε₂ side)) *
      idealSymbol K Sset D n (generator K S D (dilationLabel p B v ε₁ ε₂)) =
    idealSymbol K Sset D n (generator K S D (jLabel p B v ε₁ ε₂)) ^ 4 *
      (if IsCoprime n.val.val (b0Label p B v ε₁ ε₂).val.val then 1 else 0) := by
  have h := CubeAlgebra.first_pass_label_identity (row K S D hallowed n)
    (row_zero_or_one K S D hallowed n) p B v ε₁ ε₂ hv side
  rw [row_mask, row_mask] at h
  simpa only [row_apply] using h

include hallowed in
/-- The same actual ideal row absorbs the dual dilation at the same time
as it produces J and q₀, retaining every zero of the inverse character. -/
theorem first_pass_after_dual_dilation (n : Ext) {ι : Type*}
    (p : ι → E) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (side : Bool) (z : E) :
    ((if IsCoprime n.val.val (cubeRadical p B).val.val then 1 else 0) *
      idealSymbol K Sset D n (generator K S D (aLabel p B (if side then ε₂ else ε₁))) ^ 4 *
      idealSymbol K Sset D n (generator K S D (crtLabel p B v ε₁ ε₂ side))) *
      star (idealSymbol K Sset D n (generator K S D z)) =
    (idealSymbol K Sset D n (generator K S D (jLabel p B v ε₁ ε₂)) ^ 4 *
      (if IsCoprime n.val.val (b0Label p B v ε₁ ε₂).val.val then 1 else 0)) *
      star (idealSymbol K Sset D n (generator K S D (z * dilationLabel p B v ε₁ ε₂))) := by
  have h := CubeAlgebra.first_pass_after_dual_dilation (row K S D hallowed n)
    (row_zero_or_one K S D hallowed n) p B v ε₁ ε₂ hv side z
  rw [row_mask, row_mask] at h
  simpa only [row_apply] using h

include hallowed in
/-- A frozen common source factor C stays in the new label C·J, while
the original label f enters the row as f². The cube dilation is unchanged. -/
theorem common_factor_after_dual_dilation (n : Ext) {ι : Type*}
    (p : ι → E) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (side : Bool) (C f z : E) :
    (if IsCoprime n.val.val (cubeRadical p B).val.val then 1 else 0) *
      idealSymbol K Sset D n
        (generator K S D (aLabel p B (if side then ε₂ else ε₁) * C)) ^ 4 *
      idealSymbol K Sset D n (generator K S D (crtLabel p B v ε₁ ε₂ side)) *
      idealSymbol K Sset D n (generator K S D f) ^ 4 *
      star (idealSymbol K Sset D n (generator K S D z)) =
    (idealSymbol K Sset D n (generator K S D (C * jLabel p B v ε₁ ε₂)) ^ 4 *
      (if IsCoprime n.val.val (b0Label p B v ε₁ ε₂).val.val then 1 else 0)) *
      star (idealSymbol K Sset D n
        (generator K S D (z * f ^ 2 * dilationLabel p B v ε₁ ε₂))) := by
  have h := congrArg (fun w : ℂ => idealSymbol K Sset D n (generator K S D C) ^ 4 * w)
    (first_pass_after_dual_dilation K S D hallowed n p B v ε₁ ε₂ hv side (z * f ^ 2))
  rw [← fourth_label_absorb_row K S D hallowed n f z] at h
  rw [fourth_label_mul K S D hallowed n (aLabel p B (if side then ε₂ else ε₁)) C,
    fourth_label_mul K S D hallowed n C (jLabel p B v ε₁ ε₂)]
  convert h using 1 <;> ring

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalIdealRow

end
