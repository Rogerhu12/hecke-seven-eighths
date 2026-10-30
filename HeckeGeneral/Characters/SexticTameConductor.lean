import HeckeGeneral.Characters.LocalResidueTower
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
An actual Hecke character killed by six has conductor depth at most one
at every prime not containing six. The proof uses the already proved finite
local conductor and elementary linearization of sixth powers in a local ring.
No pro-p structure, tame-conductor input, kernel inclusion input, or conductor
bound input is added to the final theorem.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

/-- If six is invertible, sixth powers cover each positive successive
principal-unit layer. A character killed by six therefore drops one depth.
The higher-depth triviality here is an induction step, supplied below by the
proved actual conductor; it is not an input to the final Hecke theorem. -/
private theorem sixthOrderLocalCharacter_depth_drop
    {R G : Type*} [CommRing R] [IsLocalRing R] [Group G]
    (ψ : Rˣ →* G) (h6 : IsUnit (6 : R)) {n : ℕ} (hn : 0 < n)
    (hψ6 : ∀ u : Rˣ, ψ u ^ 6 = 1)
    (hnext : ∀ u : Rˣ,
      u.val - 1 ∈ IsLocalRing.maximalIdeal R ^ (n + 1) → ψ u = 1)
    (u : Rˣ) (hu : u.val - 1 ∈ IsLocalRing.maximalIdeal R ^ n) :
    ψ u = 1 := by
  let m : Ideal R := IsLocalRing.maximalIdeal R
  obtain ⟨six, hsix⟩ := h6
  let b : R := six.inv * (u.val - 1)
  have hb : b ∈ m ^ n := (m ^ n).mul_mem_left six.inv hu
  have hb1 : b ∈ m := by
    have hle : m ^ n ≤ m ^ 1 := Ideal.pow_le_pow_right (by omega : 1 ≤ n)
    simpa only [pow_one] using hle hb
  have hnon : -b ∈ nonunits R := by
    rw [← IsLocalRing.mem_maximalIdeal]
    exact m.neg_mem hb1
  have hunit : IsUnit (1 + b) := by
    simpa only [sub_neg_eq_add] using
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-b) hnon
  obtain ⟨w, hw⟩ := hunit
  have h6b : (6 : R) * b = u.val - 1 := by
    calc
      (6 : R) * b = (six.val * six.inv) * (u.val - 1) := by
        rw [← hsix]
        dsimp [b]
        ring
      _ = u.val - 1 := by rw [six.val_inv, one_mul]
  have huvalue : u.val = 1 + (6 : R) * b := by
    rw [h6b]
    ring
  have hbb : b * b ∈ m ^ (n + n) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hb hb
  have hbb' : b * b ∈ m ^ (n + 1) :=
    Ideal.pow_le_pow_right (by omega : n + 1 ≤ n + n) hbb
  have herror : w.val ^ 6 - u.val ∈ m ^ (n + 1) := by
    rw [hw, huvalue]
    have hexpand : (1 + b) ^ 6 - (1 + (6 : R) * b) =
        (b * b) * (15 + 20 * b + 15 * b ^ 2 + 6 * b ^ 3 + b ^ 4) := by ring
    rw [hexpand]
    exact (m ^ (n + 1)).mul_mem_right _ hbb'
  have hratio : (w ^ 6 * u⁻¹).val - 1 ∈ m ^ (n + 1) := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    change w.val ^ 6 * u.inv - 1 ∈ m ^ (n + 1)
    have heq : w.val ^ 6 * u.inv - 1 = (w.val ^ 6 - u.val) * u.inv := by
      rw [sub_mul, u.val_inv]
    rw [heq]
    exact (m ^ (n + 1)).mul_mem_right u.inv herror
  have hh := hnext (w ^ 6 * u⁻¹) hratio
  simpa only [map_mul, map_pow, map_inv, hψ6 w, one_mul, inv_eq_one] using hh

variable (K : Type*) [Field K] [NumberField K]

/-- A global prime not containing six makes six a unit in the actual local
integer ring. Completion and finite residue comparison are already proved. -/
theorem localInteger_six_isUnit_of_not_mem
    (p : HeightOneSpectrum (𝓞 K)) (hp6 : (6 : 𝓞 K) ∉ p.asIdeal) :
    IsUnit (6 : LocalIntegerRing K p) := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro h6
  have hz : globalToLocalResidue K p 1 (6 : 𝓞 K) = 0 := by
    change Ideal.Quotient.mk (localMaximalIdeal K p ^ 1)
      (algebraMap (𝓞 K) (LocalIntegerRing K p) (6 : 𝓞 K)) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [map_ofNat, pow_one, localMaximalIdeal] using h6
  have hglobal := (globalToLocalResidue_eq_zero_iff K p 1 (6 : 𝓞 K)).mp hz
  exact hp6 (by simpa only [pow_one] using hglobal)

/-- The actual local conductor of any sixth-order Hecke character is tame
away from six. No assumption about that character's conductor or kernel is
required. Characters of order dividing six, including the trivial character,
are all included. -/
theorem localConductorExponent_le_one_of_pow_six_eq_one
    (χ : HeckeCharacter K) (hχ : χ ^ 6 = 1)
    (p : HeightOneSpectrum (𝓞 K)) (hp6 : (6 : 𝓞 K) ∉ p.asIdeal) :
    localConductorExponent K χ p ≤ 1 := by
  let c := localConductorExponent K χ p
  let ψ : (LocalIntegerRing K p)ˣ →* Circle :=
    (localIntegralComponent K p χ).toMonoidHom
  have hψ6 : ∀ u : (LocalIntegerRing K p)ˣ, ψ u ^ 6 = 1 := by
    intro u
    change χ (localIdeleClassMap K p (localIntegerUnitsEmbedding K p u)) ^ 6 = 1
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.coe_one, Pi.one_apply] using
      congrArg (fun η : HeckeCharacter K =>
        η (localIdeleClassMap K p (localIntegerUnitsEmbedding K p u))) hχ
  have h6 : IsUnit (6 : LocalIntegerRing K p) :=
    localInteger_six_isUnit_of_not_mem K p hp6
  by_contra hbound
  have hc : 1 < c := Nat.lt_of_not_ge hbound
  have hn : 0 < c - 1 := by omega
  have hsucc : c - 1 + 1 = c := by omega
  have hnext : ∀ u : (LocalIntegerRing K p)ˣ,
      u.val - 1 ∈ IsLocalRing.maximalIdeal (LocalIntegerRing K p) ^ (c - 1 + 1) →
        ψ u = 1 := by
    intro u hu
    have humem : u ∈ principalUnits K p c := by
      apply (mem_principalUnits_iff K p c u).mpr
      simpa only [hsucc, localMaximalIdeal] using hu
    exact conductor_principalUnits_le_ker K p χ humem
  have hdrop : principalUnits K p (c - 1) ≤ ψ.ker := by
    intro u hu
    change ψ u = 1
    exact sixthOrderLocalCharacter_depth_drop ψ h6 hn hψ6 hnext u
      ((mem_principalUnits_iff K p (c - 1) u).mp hu)
  have hsmaller : c ≤ c - 1 :=
    (localConductorExponent_le_iff K χ p (c - 1)).mpr
      ((trivialAtDepth_iff_principalUnits_le_ker K p χ (c - 1)).mpr hdrop)
  omega

/-- Explicit first-principal-unit triviality for the actual local component. -/
theorem principalUnits_one_le_ker_of_pow_six_eq_one
    (χ : HeckeCharacter K) (hχ : χ ^ 6 = 1)
    (p : HeightOneSpectrum (𝓞 K)) (hp6 : (6 : 𝓞 K) ∉ p.asIdeal) :
    principalUnits K p 1 ≤ (localIntegralComponent K p χ).toMonoidHom.ker :=
  (trivialAtDepth_iff_principalUnits_le_ker K p χ 1).mp
    ((localConductorExponent_le_iff K χ p 1).mp
      (localConductorExponent_le_one_of_pow_six_eq_one K χ hχ p hp6))

end HeckeGeneral.Characters
