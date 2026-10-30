import HeckeGeneral.Arithmetic.SUnitCompactDenominators
import HeckeGeneral.Arithmetic.SLocalNormSection
import HeckeGeneral.Analysis.SUnitHaar

/-!
# Uniform denominators selected by compact finite-place support

For finite local multipliers in a compact set, every S-unit detected by a
compactly supported finite-place function has one common integral multiple.
The relevant compact set is additive: it is the image of the whole support
times the compact multiplier set under multiplication by the inverse unit.
Its coordinates may be zero, so no separation of the support from zero is
assumed.

The final specialization uses the actual compact closure of the chosen
fundamental domain. The finite coordinates of the positive radial section
are one; hence the resulting nonzero integer is independent of that radial
parameter.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "U" => SFiniteLocalGroup K S

omit [Fintype S] in
/-- The inverse is taken in the actual local unit groups, where it is continuous. -/
private theorem continuous_finiteSupportQuotient :
    Continuous (fun p : ((v : S) → v.val.adicCompletion K) × U =>
      fun v : S => p.1 v * ((p.2 v)⁻¹).val) := by
  apply continuous_pi
  intro v
  exact ((continuous_apply v).comp continuous_fst).mul
    (Units.continuous_val.comp (((continuous_apply v).comp continuous_snd).inv))

/-- The common denominator depends only on the finite support and multiplier compact set. -/
theorem exists_nonzero_integer_mul_sUnit_mem_range_of_finite_support
    (B : Set U) (hB : IsCompact B)
    (φfin : ((v : S) → v.val.adicCompletion K) → ℂ) (hφ : HasCompactSupport φfin) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ y ∈ B, ∀ u : S.unit K,
      φfin (fun v : S => (y v).val * ((sLocalDiagonal K S u).2 v).val) ≠ 0 →
        algebraMap (𝓞 K) K a * ((u : Kˣ) : K) ∈ (algebraMap (𝓞 K) K).range := by
  let q : ((v : S) → v.val.adicCompletion K) × U →
      ((v : S) → v.val.adicCompletion K) := fun p v => p.1 v * ((p.2 v)⁻¹).val
  let C : Set ((v : S) → v.val.adicCompletion K) := q '' (tsupport φfin ×ˢ B)
  have hC : IsCompact C :=
    (hφ.isCompact.prod hB).image (continuous_finiteSupportQuotient K S)
  obtain ⟨a, ha, hclear⟩ :=
    exists_nonzero_integer_mul_sUnits_mem_range_of_compact K S (Set.toFinite S) C hC
  refine ⟨a, ha, fun y hy u hu => hclear u ?_⟩
  let z : (v : S) → v.val.adicCompletion K :=
    fun v => (y v).val * ((sLocalDiagonal K S u).2 v).val
  have hz : z ∈ tsupport φfin := by
    apply subset_closure
    exact hu
  refine ⟨(z, y), ⟨hz, hy⟩, ?_⟩
  funext v
  change (y v).val * ((sLocalDiagonal K S u).2 v).val * ((y v)⁻¹).val =
    ((sLocalDiagonal K S u).2 v).val
  calc
    _ = ((sLocalDiagonal K S u).2 v).val * ((y v).val * ((y v)⁻¹).val) := by
      ac_rfl
    _ = _ := by rw [Units.mul_inv, mul_one]

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "T" => sLocalNormOneGroup K S
local notation "G" => sLocalMultiplicativeGroup K S

/-- The actual finite projection of the compact domain closure is compact in unit topology. -/
theorem isCompact_finiteProjection_sUnitFundamentalDomain_closure :
    IsCompact ((fun x : T => (x : G).2) '' closure (sUnitFundamentalDomain K S Γ)) :=
  (isCompact_closure_sUnitFundamentalDomain K S Γ).image
    (continuous_snd.comp continuous_subtype_val)

/-- One denominator works for every point of the actual domain closure and every
positive radius, because the radial section has trivial finite coordinates. -/
theorem exists_nonzero_integer_mul_sUnit_mem_range_on_radial_domain
    (φfin : ((v : S) → v.val.adicCompletion K) → ℂ) (hφ : HasCompactSupport φfin) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ r : {r : ℝ // 0 < r},
      ∀ x ∈ closure (sUnitFundamentalDomain K S Γ), ∀ u : S.unit K,
        φfin (fun v : S =>
          ((sLocalNormSection K S r * (x : G) * sLocalDiagonal K S u).2 v).val) ≠ 0 →
          algebraMap (𝓞 K) K a * ((u : Kˣ) : K) ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨a, ha, hclear⟩ := exists_nonzero_integer_mul_sUnit_mem_range_of_finite_support K S
    ((fun x : T => (x : G).2) '' closure (sUnitFundamentalDomain K S Γ))
    (isCompact_finiteProjection_sUnitFundamentalDomain_closure K S Γ) φfin hφ
  refine ⟨a, ha, fun r x hx u hu => ?_⟩
  apply hclear (x : G).2 (Set.mem_image_of_mem _ hx) u
  have hfinite : (sLocalNormSection K S r * (x : G) * sLocalDiagonal K S u).2 =
      (x : G).2 * (sLocalDiagonal K S u).2 := by
    change (1 * (x : G).2) * (sLocalDiagonal K S u).2 = _
    rw [one_mul]
  simpa only [hfinite, Pi.mul_apply, Units.val_mul] using hu

end HeckeGeneral.Analysis
