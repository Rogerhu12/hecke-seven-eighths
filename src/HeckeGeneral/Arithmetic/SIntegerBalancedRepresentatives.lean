import HeckeGeneral.Arithmetic.SIntegerCompactDenominators
import HeckeGeneral.Arithmetic.SIntegerOrbitEnumeration
import HeckeGeneral.Arithmetic.SIntegerOrbitNorm

/-!
# Uniform integral representatives for the actual S-integer orbits

Normalize a nonzero S-integer by its actual product norm, reduce it into the
proved compact norm-one representative set by an element of the given
subgroup, and clear one common denominator on the finite projection. This
produces ordinary integral representatives with archimedean arithmetic norm
bounded linearly by the original S-local norm. No PID assumption or choice
of a single ideal sector is imposed.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "G" => sLocalMultiplicativeGroup K S
local notation "N" => NonzeroRingElements (S.integer K)

theorem sLocalProductNorm_inv (p : G) :
    sLocalProductNorm K S p⁻¹ = (sLocalProductNorm K S p)⁻¹ := by
  have h := congrArg (fun u : ℝˣ => (u : ℝ)) (map_inv (sLocalProductNormHom K S) p)
  exact h

/-- The positive radial section changes no finite coordinate. -/
theorem mixedNorm_sLocalNormSection (r : {r : ℝ // 0 < r}) :
    mixedEmbedding.norm (sLocalNormSection K S r).1.val = r.val := by
  have h := sLocalProductNorm_section K S r
  change mixedEmbedding.norm (sLocalNormSection K S r).1.val *
    (∏ v : S, ‖(1 : v.val.adicCompletion K)‖) = r.val at h
  simpa only [norm_one, Finset.prod_const_one, mul_one] using h

/-- A single denominator and a single linear constant work for every
nonzero S-integer, while the correcting unit belongs to the actual subgroup. -/
theorem exists_uniform_integral_sInteger_representatives
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex] :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∃ C : ℝ, 0 < C ∧ ∀ a : N,
      ∃ u : Γ, ∃ b : NonzeroRingElements (𝓞 K),
        (b.val : K) = (d : K) * (((u.val : Kˣ) : K) * (a.val : K)) ∧
        mixedEmbedding.norm (mixedEmbedding K (b.val : K)) ≤
          C * (sIntegerElementNorm K S a).val := by
  let D : Set G := sUnitCompactRepresentativeSet K S Γ
  have hD : IsCompact D := isCompact_sUnitCompactRepresentativeSet K S Γ
  let finiteProjection : G → ((v : S) → v.val.adicCompletion K) :=
    fun x v => (x.2 v).val
  have hproj : Continuous finiteProjection := by
    apply continuous_pi
    intro v
    exact Units.continuous_val.comp ((continuous_apply v).comp continuous_snd)
  obtain ⟨d, hd, hclear⟩ :=
    exists_nonzero_integer_mul_sIntegers_mem_range_of_compact K S (Set.toFinite S)
      (finiteProjection '' D) (hD.image hproj)
  let archNorm : G → ℝ := fun x => mixedEmbedding.norm x.1.val
  have harch : Continuous archNorm :=
    (mixedEmbedding.continuous_norm K).comp (Units.continuous_val.comp continuous_fst)
  obtain ⟨B, hB, hbound⟩ := (hD.image harch).isBounded.exists_pos_norm_le
  let nd := mixedEmbedding.norm (mixedEmbedding K (d : K))
  have hnd : 0 ≤ nd := mixedEmbedding.norm_nonneg _
  refine ⟨d, hd, (1 + nd) * B, mul_pos (by linarith) hB, fun a => ?_⟩
  let r := sIntegerElementNorm K S a
  let δ := sLocalNonzeroIntegerDiagonal K S a
  let x : G := (sLocalNormSection K S r)⁻¹ * δ
  have hx : sLocalProductNorm K S x = 1 := by
    change sLocalProductNorm K S ((sLocalNormSection K S r)⁻¹ * δ) = 1
    rw [sLocalProductNorm_mul, sLocalProductNorm_inv, sLocalProductNorm_section]
    change r.val⁻¹ * r.val = 1
    exact inv_mul_cancel₀ r.property.ne'
  obtain ⟨u, hu⟩ := exists_subgroup_mem_sUnitCompactRepresentativeSet K S Γ x hx
  let y : G := sLocalDiagonal K S (u : S.unit K) * x
  have hy : y ∈ D := hu
  let a' : N := sIntegerOrbitTranslate K S Γ u a
  have hδ : sLocalNonzeroIntegerDiagonal K S a' =
      sLocalNormSection K S r * y := by
    rw [sLocalNonzeroIntegerDiagonal_eq_of_unit_mul K S a' a (u : S.unit K)
      (sIntegerOrbitTranslate_val K S Γ u a).symm]
    dsimp only [y, x, δ]
    calc
      _ = sLocalDiagonal K S (u : S.unit K) *
          (sLocalNormSection K S r * ((sLocalNormSection K S r)⁻¹ *
            sLocalNonzeroIntegerDiagonal K S a)) := by rw [mul_inv_cancel_left]
      _ = _ := by ac_rfl
  have hfinite : (fun v : S => algebraMap K (v.val.adicCompletion K) (a'.val : K)) =
      finiteProjection y := by
    funext v
    change ((sLocalNonzeroIntegerDiagonal K S a').2 v).val = (y.2 v).val
    rw [hδ]
    change (1 : v.val.adicCompletion K) * (y.2 v).val = (y.2 v).val
    exact one_mul _
  obtain ⟨b, hb⟩ := hclear a'.val (by rw [hfinite]; exact Set.mem_image_of_mem _ hy)
  have hbfield : (b : K) = (d : K) * (a'.val : K) := hb
  have hda : (d : K) ≠ 0 := by
    intro h
    exact hd (RingOfIntegers.coe_injective (by simpa only [map_zero] using h))
  have ha' : (a'.val : K) ≠ 0 := (nonzeroSIntegerFieldUnit K S a').ne_zero
  have hb0 : b ≠ 0 := by
    intro h
    have he := hb
    rw [h, map_zero] at he
    exact (mul_ne_zero hda ha') he.symm
  refine ⟨u, ⟨b, hb0⟩, ?_, ?_⟩
  · exact hb.trans (congrArg (fun z : K => (d : K) * z)
      (sIntegerOrbitTranslate_val K S Γ u a))
  · have hyBound : mixedEmbedding.norm y.1.val ≤ B := by
      have ht := hbound _ (Set.mem_image_of_mem archNorm hy)
      simpa only [archNorm, Real.norm_of_nonneg (mixedEmbedding.norm_nonneg _)] using ht
    have harchδ : mixedEmbedding K (a'.val : K) =
        (sLocalNormSection K S r).1.val * y.1.val := by
      exact congrArg (fun z : G => z.1.val) hδ
    have hnorm : mixedEmbedding.norm (mixedEmbedding K (b : K)) =
        nd * (r.val * mixedEmbedding.norm y.1.val) := by
      rw [hbfield, map_mul, map_mul, harchδ, map_mul, mixedNorm_sLocalNormSection]
    rw [hnorm]
    calc
      nd * (r.val * mixedEmbedding.norm y.1.val) ≤ nd * (r.val * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyBound r.property.le) hnd
      _ ≤ (1 + nd) * B * r.val := by nlinarith [mul_pos r.property hB]

end HeckeGeneral.Arithmetic
