import HeckeGeneral.Characters.LocalConductor
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
UNCOMPILED cache candidate, 2026-10-11; no Lean/Lake invocation.

Uniform bad-prime conductor control by an actual local power-neighborhood
proof. The inverse function theorem is valid over every complete
NontriviallyNormedField; no real/complex scalar restriction occurs in its API.
At 1 the strict derivative of x^6 is 6, nonzero in characteristic zero.
Consequently the actual image of the sixth-power map contains a neighborhood
of 1. No openness, root existence, or conductor bound is assumed.

This gives an existential depth depending only on K and p, chosen BEFORE the
Hecke character. It includes primes above 2 and 3 and does not use CFT, R,
coefficient calibration, or any earlier cache draft. It does NOT claim the
explicit numerical depth 2*v_p(6)+1. The only extra imports are mathlib.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain Filter Topology
open scoped Classical

/-- A genuine sixth root of every sufficiently small principal unit in a
complete characteristic-zero normed field. The radius is independent of any
character and roots are constructed as actual field units. -/
theorem exists_radius_units_sixthPower
    (F : Type*) [NontriviallyNormedField F] [CompleteSpace F] [CharZero F] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : Fˣ, ‖u.val - 1‖ < ε →
      ∃ w : Fˣ, w ^ 6 = u := by
  have hderiv : HasStrictDerivAt (fun x : F => x ^ 6) (6 : F) 1 := by
    simpa using hasStrictDerivAt_pow 6 (1 : F)
  have hmap : Filter.map (fun x : F => x ^ 6) (𝓝 (1 : F)) = 𝓝 (1 : F) := by
    simpa using hderiv.map_nhds_eq (by norm_num : (6 : F) ≠ 0)
  have hrange : Set.range (fun x : F => x ^ 6) ∈ 𝓝 (1 : F) := by
    rw [← hmap]
    exact Filter.range_mem_map
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hrange
  refine ⟨ε, hε, fun u hu => ?_⟩
  obtain ⟨y, hy⟩ := hball (by
    simpa only [Metric.mem_ball, dist_eq_norm] using hu)
  have hy0 : y ≠ 0 := by
    intro hzero
    exact Units.ne_zero u (by simpa [hzero] using hy.symm)
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply Units.ext
  exact hy

variable (K : Type*) [Field K] [NumberField K]

/-- A depth selected solely from the local field kills every actual Hecke
character of exponent dividing six. This is uniform also at the wild primes;
no assumptions about its conductor, kernel, continuity modulus or radicand
are present. -/
theorem exists_uniform_localConductorExponent_bound_pow_six
    (p : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℕ, 0 < n ∧ ∀ χ : HeckeCharacter K, χ ^ 6 = 1 →
      localConductorExponent K χ p ≤ n := by
  have hq : (1 : ℝ) < residueCard K p := by
    exact_mod_cast one_lt_residueCard K p
  -- Extend the EXISTING normalized normed-field instance, preserving its
  -- norm and topology definitionally; the inverse uniformizer witnesses
  -- nontriviality. No alternate local norm is installed.
  letI : NontriviallyNormedField (p.adicCompletion K) :=
    { (inferInstance : NormedField (p.adicCompletion K)) with
      non_trivial := ⟨(localUniformizer K p)⁻¹, by
        rw [norm_inv, localUniformizer_norm, inv_inv]
        exact hq⟩ }
  letI : CharZero (p.adicCompletion K) :=
    Algebra.charZero_of_charZero K (p.adicCompletion K)
  obtain ⟨ε, hε, hroot⟩ := exists_radius_units_sixthPower (p.adicCompletion K)
  have hinv : (residueCard K p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hinv
  refine ⟨n + 1, Nat.succ_pos n, fun χ hχ => ?_⟩
  apply localConductorExponent_le K χ p
  change ∀ u : (p.adicCompletion K)ˣ,
    ‖u.val - 1‖ ≤ (residueCard K p : ℝ)⁻¹ ^ (n + 1) →
      localComponent K p χ u = 1
  intro u hu
  have hpow : (residueCard K p : ℝ)⁻¹ ^ (n + 1) ≤
      (residueCard K p : ℝ)⁻¹ ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (by positivity) hinv.le
  obtain ⟨w, hw⟩ := hroot u (hu.trans_lt (hpow.trans_lt hn))
  have hwχ : localComponent K p χ w ^ 6 = 1 := by
    change χ (localIdeleClassMap K p w) ^ 6 = 1
    simpa only [ContinuousMonoidHom.pow_apply,
      ContinuousMonoidHom.coe_one, Pi.one_apply] using
      congrArg (fun η : HeckeCharacter K => η (localIdeleClassMap K p w)) hχ
  rw [← hw, map_pow, hwχ]

end HeckeGeneral.Characters
