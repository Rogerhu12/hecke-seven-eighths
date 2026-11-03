import HeckeGeneral.Characters.LocalComponent
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Basic
import Mathlib.Tactic

/-!
Finite-order continuous circle-valued characters have open kernels.
The topological argument only needs a continuous function with finite range
into a T1 space. The circle argument bounds the range by the roots of the
nonzero polynomial X^n-1. No topological-group assumption on the source is
used beyond the topological space already present in a continuous hom.
The last theorem specializes to the actual finite local Hecke component.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.FiniteOrderKernelOpen

open NumberField IsDedekindDomain
open HeckeGeneral.Characters
open scoped Classical

/-- A finite range in a T1 space makes every fiber of a continuous function
open, even when the whole codomain is not discrete. -/
theorem isOpen_fiber_of_continuous_finite_range
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    (f : X → Y) (hf : Continuous f) (hfinite : (Set.range f).Finite) (y : Y) :
    IsOpen {x : X | f x = y} := by
  have hclosed : IsClosed ((Set.range f) \ {y}) :=
    (hfinite.subset Set.sdiff_subset).isClosed
  have hopen : IsOpen (f ⁻¹' (((Set.range f) \ {y})ᶜ)) :=
    hclosed.isOpen_compl.preimage hf
  have heq : f ⁻¹' (((Set.range f) \ {y})ᶜ) = {x : X | f x = y} := by
    ext x
    have hx : f x ∈ Set.range f := ⟨x, rfl⟩
    simp [hx]
  rwa [heq] at hopen

theorem isOpen_ker_of_finite_range
    {G H : Type*} [Group G] [Monoid H]
    [TopologicalSpace G] [TopologicalSpace H] [T1Space H]
    (f : G →* H) (hf : Continuous f) (hfinite : (Set.range f).Finite) :
    IsOpen (f.ker : Set G) := by
  change IsOpen {g : G | f g = 1}
  exact isOpen_fiber_of_continuous_finite_range f hf hfinite 1

/-- The finite torsion set is proved by the actual complex polynomial;
no discrete topology is imposed on the circle. -/
theorem finite_circle_roots (n : ℕ) (hn : 0 < n) :
    Set.Finite {z : Circle | z ^ n = 1} := by
  have hc : Set.Finite {z : ℂ | z ^ n = 1} := by
    simpa only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using
      Polynomial.finite_setOfPred_isRoot
        (Polynomial.X_pow_sub_C_ne_zero (R := ℂ) hn 1)
  have hpre : Set.Finite
      (((↑) : Circle → ℂ) ⁻¹' {z : ℂ | z ^ n = 1}) :=
    Set.Finite.preimage Circle.coe_injective.injOn hc
  apply hpre.subset
  intro z hz
  change (z : ℂ) ^ n = 1
  calc
    (z : ℂ) ^ n = Circle.coeHom (z ^ n) := (_root_.map_pow Circle.coeHom z n).symm
    _ = Circle.coeHom 1 := congrArg Circle.coeHom hz
    _ = 1 := _root_.map_one Circle.coeHom

theorem finite_range_circle_of_pow_eq_one
    {X : Type*} (f : X → Circle) (n : ℕ) (hn : 0 < n)
    (hpow : ∀ x : X, f x ^ n = 1) : (Set.range f).Finite := by
  apply (finite_circle_roots n hn).subset
  rintro z ⟨x, rfl⟩
  exact hpow x

theorem isOpen_ker_circle_of_pow_eq_one
    {G : Type*} [Group G] [TopologicalSpace G]
    (f : G →ₜ* Circle) (n : ℕ) (hn : 0 < n)
    (hpow : ∀ g : G, f g ^ n = 1) :
    IsOpen (f.toMonoidHom.ker : Set G) := by
  exact isOpen_ker_of_finite_range f.toMonoidHom f.continuous
    (finite_range_circle_of_pow_eq_one f n hn hpow)

/-- The character-theoretic finite-order predicate supplies a common
positive exponent on the full source group, rather than only on units. -/
theorem isOpen_ker_circle_of_finiteOrder
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (f : G →ₜ* Circle) (hf : FiniteOrder f) :
    IsOpen (f.toMonoidHom.ker : Set G) := by
  obtain ⟨n, hn, hpow⟩ := (finiteOrder_iff_pointwise f).mp hf
  exact isOpen_ker_circle_of_pow_eq_one f n hn hpow

variable (K : Type*) [Field K] [NumberField K]

/-- Openness of the kernel of the actual local component at any finite
place. It follows by pullback from finite order of the global character. -/
theorem isOpen_ker_localComponent_of_finiteOrder
    (χ : HeckeCharacter K) (hχ : FiniteOrder χ) (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen ((localComponent K v χ).toMonoidHom.ker : Set (v.adicCompletion K)ˣ) := by
  obtain ⟨n, hn, hpow⟩ := (finiteOrder_iff_pointwise χ).mp hχ
  apply isOpen_ker_circle_of_pow_eq_one (localComponent K v χ) n hn
  intro u
  rw [localComponent_apply]
  exact hpow (localIdeleClassMap K v u)

end HeckeSkeleton.FiniteOrderKernelOpen
