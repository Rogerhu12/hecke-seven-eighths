import HeckeGeneral.Analysis.SUnitSchwartzSlice
import Mathlib.Basic.ENNReal.BigOperators

/-!
# Integrability of actual positive-norm tensor Schwartz slices

Compact finite-place support supplies a single nonzero integral denominator
on the compact closure of the actual S-unit fundamental domain. Every global
unit detected by that support then maps injectively to the same nonzero trace
integer lattice. The remaining archimedean multipliers form a compact set of
actual mixed-space units, so their inverse operator norms have one bound.
Schwartz decay gives bounded finite orbital sums before any orbital
summability or integrability is assumed. Haar unfolding then proves actual
integrability on the norm-one local group.

All subgroup elements and ideal sectors are retained. Finite-place support
is compact in the additive completion product and may contain zero. Constants
may depend on the field, finite set, subgroup, test functions and fixed
strictly positive radius; no uniform assertion as the radius tends to zero
is made here.

Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open scoped Classical BigOperators ENNReal nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "G" => sLocalMultiplicativeGroup K S
local notation "T" => sLocalNormOneGroup K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => mixedEmbedding.mixedSpace K

omit [Fintype S] in
/-- Continuity and compact support give a genuine global bound, including
outside the support where the function is zero. -/
theorem exists_pos_norm_finiteTestFunction_le (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : (Π v : S, v.val.adicCompletion K), ‖ψ z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    (hψsupport.isCompact.image hψ).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun z => ?_⟩
  by_cases hz : ψ z = 0
  · simpa only [hz, norm_zero] using hC.le
  · exact hbound _ (Set.mem_image_of_mem ψ (subset_closure hz))

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

/-- The actual archimedean multiplier after clearing a global denominator. -/
def clearedSLocalTraceMultiplier (a : 𝓞 K) (ha : a ≠ 0) (p : G) : Wˣ :=
  p.1 * (Units.map (mixedEmbedding K).toMonoidHom
    (Units.mk0 (algebraMap (𝓞 K) K a) (RingOfIntegers.coe_ne_zero_iff.mpr ha)))⁻¹

omit [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
  [Γ.FiniteIndex] in
/-- A reusable quantitative finite-sum estimate. The arithmetic injection of
the active subgroup elements into the actual trace integer lattice is proved
inside this lemma. The displayed denominator and inverse bound are its local
inputs; the slice-integrability theorem constructs both without assumptions. -/
theorem sum_norm_sLocalTensorTestFunction_sUnit_le
    (φ : SchwartzMap V ℂ) (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (a : 𝓞 K) (ha : a ≠ 0) (p : G) (M : ℕ)
    (hM : Module.finrank ℤ
      (traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) < M)
    {B C : ℝ}
    (hB : ‖(traceUnitMulEquiv K (clearedSLocalTraceMultiplier K S a ha p)).symm.toContinuousLinearMap‖ ≤ B)
    (hC : 0 ≤ C) (hψbound : ∀ z : (Π v : S, v.val.adicCompletion K), ‖ψ z‖ ≤ C)
    (hclear : ∀ u : Γ,
      ψ (fun v : S => ((p * sLocalDiagonal K S (u : S.unit K)).2 v).val) ≠ 0 →
        algebraMap (𝓞 K) K a * (((u : S.unit K) : Kˣ) : K) ∈
          (algebraMap (𝓞 K) K).range)
    (t : Finset Γ) :
    (∑ u ∈ t, ‖sLocalTensorTestFunction K S φ ψ
      (p * sLocalDiagonal K S (u : S.unit K))‖) ≤
      C * (SchwartzMap.seminorm ℂ M 0 φ * B ^ M) *
        latticeInversePowerMass
          (traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) M := by
  let L : Submodule ℤ V := traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let aW : Wˣ := Units.map (mixedEmbedding K).toMonoidHom
    (Units.mk0 (algebraMap (𝓞 K) K a) (RingOfIntegers.coe_ne_zero_iff.mpr ha))
  let b : Γ → ℂ := fun u => ψ (fun v : S =>
    ((p * sLocalDiagonal K S (u : S.unit K)).2 v).val)
  let v : Γ → V := fun u => (traceToMixed K).symm
    ((p * sLocalDiagonal K S (u : S.unit K)).1 : W)
  let j : {u : Γ // b u ≠ 0} → NonzeroLattice L := fun u =>
    clearedUnitTraceLatticeEmbedding K a ha
      ⟨((u.val : S.unit K) : Kˣ), hclear u.val u.property⟩
  have hj : Function.Injective j := by
    intro u w huw
    have hu := (clearedUnitTraceLatticeEmbedding K a ha).injective huw
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : IntegralMultipleUnits K a => z.val) hu
  have hmatch : ∀ u : {u : Γ // b u ≠ 0},
      traceUnitMulEquiv K (clearedSLocalTraceMultiplier K S a ha p)
        (((j u : NonzeroLattice L) : L) : V) = v u.val := by
    intro u
    rw [show (((j u : NonzeroLattice L) : L) : V) =
        traceEmbedding K (algebraMap (𝓞 K) K a *
          (((u.val : Γ) : S.unit K) : Kˣ)) from rfl]
    apply (traceToMixed K).injective
    rw [traceToMixed_traceUnitMulEquiv]
    simp only [v, traceEmbedding, ContinuousLinearEquiv.apply_symm_apply]
    change (clearedSLocalTraceMultiplier K S a ha p : W) * mixedEmbedding K
        (algebraMap (𝓞 K) K a * (((u.val : Γ) : S.unit K) : Kˣ)) =
      ((p * sLocalDiagonal K S (u.val : S.unit K)).1 : W)
    rw [map_mul]
    change ((p.1 * aW⁻¹ : Wˣ) : W) *
        ((aW * (sLocalDiagonal K S (u.val : S.unit K)).1 : Wˣ) : W) =
      ((p.1 * (sLocalDiagonal K S (u.val : S.unit K)).1 : Wˣ) : W)
    rw [← Units.val_mul]
    exact congrArg Units.val (by simp only [mul_assoc, inv_mul_cancel_left])
  have hreal := sum_norm_weighted_schwartz_le_of_support L φ
    (traceUnitMulEquiv K (clearedSLocalTraceMultiplier K S a ha p)) M hM
    hB hC v b (fun u => hψbound _) j hj hmatch t
  have hterm (u : Γ) :
      ‖sLocalTensorTestFunction K S φ ψ (p * sLocalDiagonal K S (u : S.unit K))‖ =
      ‖b u * φ (v u)‖ := by
    change ‖φ (v u) * b u‖ = ‖b u * φ (v u)‖
    rw [mul_comm]
  simpa only [hterm] using hreal

/-- Uniform finite sums on the compact domain closure. The support-dependent
arithmetic denominator and the inverse operator bound are constructed. -/
theorem exists_sLocalSchwartzSlice_finite_gamma_sums_bound
    (φ : SchwartzMap V ℂ) (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ x ∈ closure (sUnitFundamentalDomain K S Γ), ∀ t : Finset Γ,
        (∑ u ∈ t, ‖sLocalSchwartzSlice K S φ ψ r
          (sLocalNormOneDiagonal K S (u : S.unit K) * x)‖) ≤ D := by
  obtain ⟨a, ha, hclear⟩ :=
    exists_nonzero_integer_mul_sUnit_mem_range_on_radial_domain K S Γ ψ hψsupport
  obtain ⟨C, hC, hψbound⟩ :=
    exists_pos_norm_finiteTestFunction_le K S ψ hψ hψsupport
  let multiplier : T → Wˣ := fun x => clearedSLocalTraceMultiplier K S a ha
    (sLocalNormSection K S r * (x : G))
  have hmultiplier : Continuous multiplier := by
    exact (continuous_fst.comp (continuous_const.mul continuous_subtype_val)).mul
      continuous_const
  let P : Set Wˣ := multiplier '' closure (sUnitFundamentalDomain K S Γ)
  have hP : IsCompact P :=
    (isCompact_closure_sUnitFundamentalDomain K S Γ).image hmultiplier
  obtain ⟨B, hB, hBbound⟩ := exists_uniform_traceUnit_inverse_bound K P hP
  let L : Submodule ℤ V := traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let M : ℕ := Module.finrank ℤ L + 1
  have hM : Module.finrank ℤ L < M := Nat.lt_succ_self _
  let D : ℝ := C * (SchwartzMap.seminorm ℂ M 0 φ * B ^ M) *
    latticeInversePowerMass L M
  have hmass : 0 ≤ latticeInversePowerMass L M := by
    apply tsum_nonneg
    intro l
    positivity
  have hseminorm : 0 ≤ SchwartzMap.seminorm ℂ M 0 φ :=
    apply_nonneg (SchwartzMap.seminorm ℂ M 0) φ
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  refine ⟨D, hD, fun x hx t => ?_⟩
  have hreal := sum_norm_sLocalTensorTestFunction_sUnit_le K S Γ φ ψ a ha
    (sLocalNormSection K S r * (x : G)) M hM
    (hBbound _ (Set.mem_image_of_mem _ hx)) hC.le hψbound
    (fun u hu => hclear r x hx (u : S.unit K) hu) t
  have hterm (u : Γ) :
      sLocalSchwartzSlice K S φ ψ r
        (sLocalNormOneDiagonal K S (u : S.unit K) * x) =
      sLocalTensorTestFunction K S φ ψ
        ((sLocalNormSection K S r * (x : G)) * sLocalDiagonal K S (u : S.unit K)) := by
    unfold sLocalSchwartzSlice
    congr 1
    change sLocalNormSection K S r *
      (sLocalDiagonal K S (u : S.unit K) * (x : G)) = _
    ac_rfl
  simpa only [hterm] using hreal

omit [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
  [Γ.FiniteIndex] in
/-- Exact finite-sum transport from global subgroup elements to the opposite
group acting in Haar unfolding. This retains every subgroup element. -/
theorem sLocalOrbit_enorm_sum_le_of_gamma_bound (f : T → ℂ) (x : T) {D : ℝ}
    (hbound : ∀ t : Finset Γ,
      (∑ u ∈ t, ‖f (sLocalNormOneDiagonal K S (u : S.unit K) * x)‖) ≤ D) :
    ∀ t : Finset (sLocalNormOneGamma K S Γ).op,
      (∑ g ∈ t, ‖f (g • x)‖ₑ) ≤ ENNReal.ofReal D := by
  intro t
  let e := sLocalGammaActionEquiv K S Γ
  have hreindex : (∑ g ∈ t, ‖f (g • x)‖) =
      ∑ u ∈ t.map e.symm.toEmbedding,
        ‖f (sLocalNormOneDiagonal K S (u : S.unit K) * x)‖ := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro g _hg
    change ‖f (g • x)‖ =
      ‖f (sLocalNormOneDiagonal K S (e.symm g : S.unit K) * x)‖
    have he := sLocalGammaActionEquiv_smul K S Γ (e.symm g) x
    change e (e.symm g) • x =
      sLocalNormOneDiagonal K S (e.symm g : S.unit K) * x at he
    rw [Equiv.apply_symm_apply] at he
    exact congrArg (fun y => ‖f y‖) he
  have hreal : (∑ g ∈ t, ‖f (g • x)‖) ≤ D := by
    rw [hreindex]
    exact hbound _
  have henn := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_sum_of_nonneg (fun g _hg => norm_nonneg _)] at henn
  simpa only [ofReal_norm] using henn

/-- Extended-norm finite sums in the literal Haar action are bounded, with
the full subgroup index retained by the action equivalence. -/
theorem exists_sLocalSchwartzSlice_finite_orbit_sums_bound
    (φ : SchwartzMap V ℂ) (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ x ∈ sUnitFundamentalDomain K S Γ,
        ∀ t : Finset (sLocalNormOneGamma K S Γ).op,
          (∑ g ∈ t, ‖sLocalSchwartzSlice K S φ ψ r (g • x)‖ₑ) ≤ C := by
  obtain ⟨D, _hD, hbound⟩ :=
    exists_sLocalSchwartzSlice_finite_gamma_sums_bound K S Γ φ ψ hψ hψsupport r
  refine ⟨ENNReal.ofReal D, ENNReal.ofReal_lt_top, fun x hx => ?_⟩
  exact sLocalOrbit_enorm_sum_le_of_gamma_bound K S Γ
    (sLocalSchwartzSlice K S φ ψ r) x (hbound x (subset_closure hx))

include Γ in
/-- Genuine Haar integrability of every actual positive-norm tensor Schwartz
slice. The finite function needs continuity and additive compact support;
no orbital convergence or integrability assumption is present. -/
theorem integrable_sLocalSchwartzSlice
    (φ : SchwartzMap V ℂ) (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) :
    Integrable (sLocalSchwartzSlice K S φ ψ r) (sUnitHaarMeasure K S) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_sLocalSchwartzSlice_finite_orbit_sums_bound K S Γ φ ψ hψ hψsupport r
  exact integrable_sUnitHaar_of_finite_orbit_sums_bound K S Γ
    (continuous_sLocalSchwartzSlice K S φ ψ hψ r).aestronglyMeasurable hC hbound

end HeckeGeneral.Analysis
