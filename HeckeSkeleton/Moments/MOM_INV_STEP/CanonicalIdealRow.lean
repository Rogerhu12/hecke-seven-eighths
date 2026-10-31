import HeckeSkeleton.Moments.MOM_INV_STEP.LocalSource
import HeckeSkeleton.Moments.MOM_INV_STEP.CubeLabels
import HeckeGeneral.Analysis.MarkedThetaReflection

/-!
# The cube identity on actual selected ideal generators

`AllowedGeneratorInput` is the explicit MOM_BASE compatibility input.
Its multiplicative generator defect is an actual sixth power of an
S-unit. The existing sextic evaluation theorem removes exactly that
defect, including at bad residues. This produces a genuine monoid row
on actual exterior ideals and connects the cube table to the selected
canonical generators used in the marked block.

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

def primeIdeal (p : ExteriorPrime K Sset) : E := exteriorPrimeIdeal K Sset p

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

variable (D : ThetaArithmeticData K Sset)
variable (hallowed : AllowedGeneratorInput K Sset D)

theorem generator_contraction (I : E) :
    sIntegerModulusContraction K Sset (D.generator I) = I.val.val := by
  unfold sIntegerModulusContraction
  rw [D.generator_span]
  exact under_map_coprime_sIntegerIdeal K Sset I.val.val
    (sexticIdeal_coprime_S K Sset I.val.val I.property)

/-- The literal canonical numerator-ideal row. Multiplicativity is
proved from the supplied allowed section and actual sixth-unit invariance. -/
def row (n : Ext) : E →* ℂ where
  toFun I := idealSymbol K Sset D n (D.generator I)
  map_one' := by
    rw [hallowed.reciprocity n (1 : E)]
    exact sIntegerSexticIdealEvaluation_top K Sset
      D.root6 D.primitive6 D.embedding (1 : E).property
      (fun p hp => D.away_six p ((1 : E).property p hp)) (D.generator n)
  map_mul' := by
    intro I J
    obtain ⟨u, hu⟩ := hallowed.multiplicative I J
    change idealSymbol K Sset D n (D.generator (exteriorMul K Sset I J)) = _
    rw [hu, mul_assoc]
    calc
      _ = idealSymbol K Sset D n (D.generator I * D.generator J) :=
        sIntegerSexticIdealEvaluation_mul_sixth_power_unit K Sset
          D.root6 D.primitive6 D.embedding n.val.val
          (nonZeroDivisors.coe_ne_zero n.val) n.property
          (fun p hp => D.away_six p (n.property p hp)) u _
      _ = _ := sIntegerSexticIdealEvaluation_mul K Sset
        D.root6 D.primitive6 D.embedding n.val.val
        (nonZeroDivisors.coe_ne_zero n.val) n.property
        (fun p hp => D.away_six p (n.property p hp)) _ _

@[simp] theorem row_apply (n : Ext) (I : E) :
    row K S D hallowed n I = idealSymbol K Sset D n (D.generator I) := rfl

include hallowed in
/-- Canonical generators of products and products of prime generators
give exactly the same scalar row, with no nonvanishing assumption. -/
theorem generator_product_row (n : Ext) {ι : Type*}
    (p : ι → E) (B : Finset ι) (e : ι → ℕ) :
    idealSymbol K Sset D n (D.generator (primeProduct p B e)) =
      idealSymbol K Sset D n (∏ i ∈ B, D.generator (p i) ^ e i) := by
  change row K S D hallowed n (∏ i ∈ B, p i ^ e i) =
    LocalSource.actualRow K Sset D.root6 D.primitive6 D.embedding n.val.val
      (nonZeroDivisors.coe_ne_zero n.val) n.property
      (fun p hp => D.away_six p (n.property p hp))
        (∏ i ∈ B, D.generator (p i) ^ e i)
  simp only [map_prod, map_pow, row_apply, LocalSource.actualRow_apply, idealSymbol]

include hallowed in
theorem prime_generator_product_row (n : Ext) {ι : Type*}
    (p : ι → ExteriorPrime K Sset) (B : Finset ι) (e : ι → ℕ) :
    idealSymbol K Sset D n
      (D.generator (primeProduct (fun i => primeIdeal K S (p i)) B e)) =
      idealSymbol K Sset D n
        (∏ i ∈ B, D.generator (exteriorPrimeIdeal K Sset (p i)) ^ e i) :=
  generator_product_row K S D hallowed n (fun i => primeIdeal K S (p i)) B e

theorem row_mask (n : Ext) (I : E) :
    sixthMask (row K S D hallowed n) I =
      if IsCoprime n.val.val I.val.val then 1 else 0 := by
  have h := LocalSource.actualRow_mask K Sset D.root6 D.primitive6 D.embedding n.val.val
    (nonZeroDivisors.coe_ne_zero n.val) n.property
    (fun p hp => D.away_six p (n.property p hp)) (D.generator I)
  rw [generator_contraction] at h
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
/-- The first surviving factor uses the actual selected generator of J
and the actual ideal q₀ puncture. No ideal is assumed principal over 𝓞 K. -/
theorem first_pass_label_identity (n : Ext) {ι : Type*}
    (p : ι → E) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (side : Bool) :
    (if IsCoprime n.val.val (cubeRadical p B).val.val then 1 else 0) *
      idealSymbol K Sset D n (D.generator (aLabel p B (if side then ε₂ else ε₁))) ^ 4 *
      idealSymbol K Sset D n (D.generator (crtLabel p B v ε₁ ε₂ side)) *
      idealSymbol K Sset D n (D.generator (dilationLabel p B v ε₁ ε₂)) =
    idealSymbol K Sset D n (D.generator (jLabel p B v ε₁ ε₂)) ^ 4 *
      (if IsCoprime n.val.val (b0Label p B v ε₁ ε₂).val.val then 1 else 0) := by
  have h := CubeAlgebra.first_pass_label_identity (row K S D hallowed n)
    (row_zero_or_one K S D hallowed n) p B v ε₁ ε₂ hv side
  rw [row_mask, row_mask] at h
  exact h

include hallowed in
/-- The same actual ideal row absorbs the dual dilation at the same time
as it produces J and q₀, retaining every zero of the inverse character. -/
theorem first_pass_after_dual_dilation (n : Ext) {ι : Type*}
    (p : ι → E) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (side : Bool) (z : E) :
    ((if IsCoprime n.val.val (cubeRadical p B).val.val then 1 else 0) *
      idealSymbol K Sset D n (D.generator (aLabel p B (if side then ε₂ else ε₁))) ^ 4 *
      idealSymbol K Sset D n (D.generator (crtLabel p B v ε₁ ε₂ side))) *
      star (idealSymbol K Sset D n (D.generator z)) =
    (idealSymbol K Sset D n (D.generator (jLabel p B v ε₁ ε₂)) ^ 4 *
      (if IsCoprime n.val.val (b0Label p B v ε₁ ε₂).val.val then 1 else 0)) *
      star (idealSymbol K Sset D n (D.generator (z * dilationLabel p B v ε₁ ε₂))) := by
  have h := CubeAlgebra.first_pass_after_dual_dilation (row K S D hallowed n)
    (row_zero_or_one K S D hallowed n) p B v ε₁ ε₂ hv side z
  rw [row_mask, row_mask] at h
  exact h

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalIdealRow

end
