import HeckeGeneral.Arithmetic.SIntegerOrbitNorm
import HeckeGeneral.Arithmetic.SLocalNormSectionAlgebra

/-!
# The actual norm-one shift of an inverse S-integer modulus

The local inverse diagonal of the modulus splits into its positive radial
section and a genuine element of the existing norm-one group. For a base
point `section r * x`, inversion and division by the modulus therefore give
radius `1 / (r * q_c)` and norm-one variable `t_c * x⁻¹`. No subgroup is
enlarged, and neither a Haar normalization nor a fundamental-domain
invariance property enters these algebraic identities.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "OS" => S.integer K
local notation "G" => sLocalMultiplicativeGroup K S
local notation "T" => sLocalNormOneGroup K S

variable (c : S.integer K) (hc : c ≠ 0)

local notation "q" => sIntegerElementNorm K S (Subtype.mk c hc)
local notation "δ" => sLocalNonzeroIntegerDiagonal K S (Subtype.mk c hc)

/-- The inverse modulus's norm-one component, in the original local group. -/
def sIntegerModulusNormOneShift : T := by
  refine ⟨sLocalNormSection K S q * δ⁻¹, ?_⟩
  change sLocalProductNormHom K S (sLocalNormSection K S q * δ⁻¹) = 1
  have hq : sLocalProductNormHom K S (sLocalNormSection K S q) =
      sLocalProductNormHom K S δ := by
    apply Units.ext
    exact sLocalProductNorm_section K S q
  rw [map_mul, map_inv, hq, mul_inv_cancel]

@[simp] theorem sIntegerModulusNormOneShift_coe :
    (sIntegerModulusNormOneShift K S c hc : G) =
      sLocalNormSection K S q * δ⁻¹ := rfl

/-- The actual inverse diagonal has its inverse arithmetic norm as radius. -/
theorem sIntegerModulus_invDiagonal_eq_section_mul_shift :
    δ⁻¹ = sLocalNormSection K S ⟨(q).val⁻¹, inv_pos.mpr (q).property⟩ *
      (sIntegerModulusNormOneShift K S c hc : G) := by
  rw [sLocalNormSection_inv, sIntegerModulusNormOneShift_coe]
  simp only [← mul_assoc, inv_mul_cancel, one_mul]

/-- Inverse Poisson scaling gives precisely the translated inverse Haar variable. -/
theorem sIntegerModulus_inverseBase_eq_section_shift
    (r : {r : ℝ // 0 < r}) (x : T) :
    (sLocalNormSection K S r * (x : G))⁻¹ * δ⁻¹ =
      sLocalNormSection K S
        ⟨(r.val * (q).val)⁻¹, inv_pos.mpr (mul_pos r.property (q).property)⟩ *
      ((sIntegerModulusNormOneShift K S c hc * x⁻¹ : T) : G) := by
  have hsection : sLocalNormSection K S
      ⟨(r.val * (q).val)⁻¹, inv_pos.mpr (mul_pos r.property (q).property)⟩ =
      (sLocalNormSection K S r)⁻¹ * (sLocalNormSection K S q)⁻¹ := by
    rw [sLocalNormSection_inv K S
      ⟨r.val * (q).val, mul_pos r.property (q).property⟩,
      sLocalNormSection_mul K S r q, mul_inv_rev]
    exact mul_comm _ _
  rw [hsection, mul_inv_rev,
    sIntegerModulus_invDiagonal_eq_section_mul_shift K S c hc,
    sLocalNormSection_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  ac_rfl

/-- The resulting radius is the reciprocal of the original radius times modulus norm. -/
theorem sIntegerModulus_inverseBase_norm
    (r : {r : ℝ // 0 < r}) (x : T) :
    sLocalProductNorm K S ((sLocalNormSection K S r * (x : G))⁻¹ * δ⁻¹) =
      (r.val * (q).val)⁻¹ := by
  rw [sIntegerModulus_inverseBase_eq_section_shift K S c hc r x,
    sLocalProductNorm_mul, sLocalProductNorm_section]
  have ht : sLocalProductNorm K S
      ((sIntegerModulusNormOneShift K S c hc * x⁻¹ : T) : G) = 1 :=
    (mem_sLocalNormOneGroup K S _).mp
      (sIntegerModulusNormOneShift K S c hc * x⁻¹).property
  rw [ht, mul_one]

end HeckeGeneral.Arithmetic
