import FLTReuse.Md2cadaa4525e04a6
import HeckeGeneral.Arithmetic.SUnitArchimedeanBalancing
import Mathlib.Topology.Compactness.Compact
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Uniform integral denominators on compact finite-local sets

The public finite-adele pointwise denominator theorem and the openness of
integral finite adeles give one nonzero integer clearing an entire compact
set. A finite additive S-product, including its zero coordinates, is embedded
by zero extension through an actual restricted-product chart. Its compact
image therefore has a common denominator. For global S-units whose coordinate
values lie in this additive compact set, the valuations outside S are already
one, so the same denominator places every such global element in the actual
ring-of-integers image. Compactness in the local unit-group topology is not
required.

All fields and local products retain their original universes. No PID,
S-unit finite-generation, or analytic-integrability input is assumed.
Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Filter
open scoped Classical BigOperators RestrictedProduct

variable (K : Type*) [Field K] [NumberField K]

/-- One actual nonzero integer clears every finite adele in a compact set.
The denominator is a finite product obtained from an open cover. -/
theorem exists_nonzero_integer_mul_compact_finiteAdeles_mem_integral
    (C : Set (FiniteAdeleRing (𝓞 K) K)) (hC : IsCompact C) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ y ∈ C,
      algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) a * y ∈
        NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K := by
  classical
  let U : {a : 𝓞 K // a ≠ 0} → Set (FiniteAdeleRing (𝓞 K) K) := fun a =>
    (fun y => algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) a.val * y) ⁻¹'
      NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K
  have hU : ∀ a, IsOpen (U a) := fun a =>
    (NumberField.AdelicBox.isOpen_integralFiniteAdeles K).preimage
      (continuous_const.mul continuous_id)
  have hcover : C ⊆ ⋃ a, U a := by
    intro y _hy
    obtain ⟨a, ha, hya⟩ :=
      NumberField.AdelicBox.exists_mul_mem_integralFiniteAdeles (𝓞 K) K y
    exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hya⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hU hcover
  let a : 𝓞 K := ∏ s ∈ t, s.val
  have ha : a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s _ => s.property
  refine ⟨a, ha, fun y hy => ?_⟩
  obtain ⟨s, hs, hsy⟩ := Set.mem_iUnion₂.mp (ht hy)
  change algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) s.val * y ∈
    NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K at hsy
  obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem (fun s : {a : 𝓞 K // a ≠ 0} => s.val) hs
  change a = s.val * b at hb
  have heq : algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) a * y =
      algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b *
        (algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) s.val * y) := by
    rw [hb, map_mul]
    ac_rfl
  rw [heq]
  intro v
  exact mul_mem
    (NumberField.AdelicBox.algebraMap_mem_adicCompletionIntegers (𝓞 K) K v b)
    (hsy v)

variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- A finite local tuple in the principal-filter chart integral away from S. -/
private def finiteLocalZeroExtensionChart
    (x : (v : S) → v.val.adicCompletion K) :
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      (Filter.principal Sᶜ) :=
  ⟨fun v => if hv : v ∈ S then x ⟨v, hv⟩ else (0 : v.adicCompletion K), by
    rw [Filter.eventually_principal]
    intro v hv
    simp only [Set.mem_compl_iff] at hv
    dsimp only
    rw [dite_eq_right hv]
    exact zero_mem _⟩

/-- Actual zero extension into the finite adele ring, for finite S. -/
def finiteLocalZeroExtension (hS : S.Finite)
    (x : (v : S) → v.val.adicCompletion K) : FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.inclusion _ _
    (Filter.le_principal_iff.mpr hS.compl_mem_cofinite)
    (finiteLocalZeroExtensionChart K S x)

@[simp]
theorem finiteLocalZeroExtension_apply_mem (hS : S.Finite)
    (x : (v : S) → v.val.adicCompletion K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
    finiteLocalZeroExtension K S hS x v = x ⟨v, hv⟩ := by
  change (if hv' : v ∈ S then x ⟨v, hv'⟩ else (0 : v.adicCompletion K)) = x ⟨v, hv⟩
  rw [dite_eq_left hv]

@[simp]
theorem finiteLocalZeroExtension_apply_notMem (hS : S.Finite)
    (x : (v : S) → v.val.adicCompletion K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    finiteLocalZeroExtension K S hS x v = 0 := by
  change (if hv' : v ∈ S then x ⟨v, hv'⟩ else (0 : v.adicCompletion K)) =
    (0 : v.adicCompletion K)
  rw [dite_eq_right hv]

/-- Continuity uses the restricted-product principal chart, without a universe reduction. -/
theorem continuous_finiteLocalZeroExtension (hS : S.Finite) :
    Continuous (finiteLocalZeroExtension K S hS) := by
  have hc : Continuous (finiteLocalZeroExtensionChart K S) := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    change Continuous (fun x : (v : S) → v.val.adicCompletion K =>
      fun v => if hv : v ∈ S then x ⟨v, hv⟩ else 0)
    apply continuous_pi
    intro v
    by_cases hv : v ∈ S
    · simpa only [dite_eq_left hv] using
        (continuous_apply (⟨v, hv⟩ : S))
    · simpa only [dite_eq_right hv] using
        (continuous_const : Continuous
          (fun _ : (w : S) → w.val.adicCompletion K => (0 : v.adicCompletion K)))
  exact (RestrictedProduct.continuous_inclusion
    (Filter.le_principal_iff.mpr hS.compl_mem_cofinite)).comp hc

/-- Additive finite-local compactness produces actual global integral multiples
of every S-unit whose coordinate values lie in the compact set. Zero is allowed
in this set; compactness of its intersection with the unit group is not assumed. -/
theorem exists_nonzero_integer_mul_sUnits_mem_range_of_compact
    (hS : S.Finite)
    (C : Set ((v : S) → v.val.adicCompletion K)) (hC : IsCompact C) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ u : S.unit K,
      (fun v : S => ((sLocalDiagonal K S u).2 v).val) ∈ C →
      algebraMap (𝓞 K) K a * ((u : Kˣ) : K) ∈ (algebraMap (𝓞 K) K).range := by
  have himage := hC.image (continuous_finiteLocalZeroExtension K S hS)
  obtain ⟨a, ha, hclear⟩ :=
    exists_nonzero_integer_mul_compact_finiteAdeles_mem_integral K
      (finiteLocalZeroExtension K S hS '' C) himage
  refine ⟨a, ha, fun u hu => ?_⟩
  have hlocal := hclear (finiteLocalZeroExtension K S hS
    (fun v : S => ((sLocalDiagonal K S u).2 v).val))
    (Set.mem_image_of_mem _ hu)
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one K
  intro v
  by_cases hv : v ∈ S
  · have hle := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp (hlocal v)
    change Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) *
      finiteLocalZeroExtension K S hS
        (fun w : S => ((sLocalDiagonal K S u).2 w).val) v) ≤ 1 at hle
    rw [finiteLocalZeroExtension_apply_mem K S hS _ v hv] at hle
    change Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) *
      algebraMap K (v.adicCompletion K) ((u : Kˣ) : K)) ≤ 1 at hle
    rw [← map_mul] at hle
    change Valued.v ((algebraMap (𝓞 K) K a * ((u : Kˣ) : K) : K) :
      v.adicCompletion K) ≤ 1 at hle
    rwa [adicCompletion.valued_coe] at hle
  · rw [map_mul, u.property v hv, mul_one]
    exact v.valuation_le_one a

end HeckeGeneral.Arithmetic
