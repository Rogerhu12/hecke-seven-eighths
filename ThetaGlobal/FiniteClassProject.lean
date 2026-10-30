import HeckeSkeleton.SixthLocalFinite
import HeckeAxiom.ArithmeticChoice
import ThetaGlobal.FinitePowerQuotient
import ThetaGlobal.FiniteClassExpansion

/-!
# The actual fixed-choice power-class dictionary

The skeleton uses units of `mixedSpace`; Axiom uses the product of infinite
completions.  Their sixth-power quotients are identified through their
identical finite coordinates.  The resulting map preserves every rational
diagonal and therefore the allowed generator classes.

This module also fixes the reflected class mask to the chosen arithmetic
context's actual complement and actual sextic Hilbert pairing.  No arbitrary
class-set or pairing is substituted for the chosen one.
-/

set_option autoImplicit false
noncomputable section
namespace ThetaGlobal.ProjectFiniteClass

open NumberField IsDedekindDomain
open DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.FinitePowerQuotient ThetaGlobal.FiniteClass
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)

abbrev LocalClass (p : A.Sf) :=
  (p.val.adicCompletion F)ˣ ⧸
    (powMonoidHom 6 : (p.val.adicCompletion F)ˣ →* (p.val.adicCompletion F)ˣ).range

instance localClass_finite (p : A.Sf) : Finite (LocalClass A p) := by
  have := HeckeSkeleton.SixthLocalFinite.finiteIndex_local F p.val
  exact Subgroup.finite_quotient_of_finiteIndex

/-- The unit-sector quotient is already the same type in both projects. -/
theorem unitQuotient_eq :
    SixthUnitClasses F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) = A.UnitQuotient := rfl

/-- Finite-coordinate identification of the skeleton's local class group. -/
def skeletonFiniteClassEquiv :
    SixthLocalClasses F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) ≃*
      (∀ p : A.Sf, LocalClass A p) := by
  letI := primitive12_totallyComplex F A.zeta12 A.primitive_zeta12
  exact finitePartEquiv (mixedEmbedding.mixedSpace F)ˣ
    (fun p : A.Sf => (p.val.adicCompletion F)ˣ) 6
    (HeckeSkeleton.SixthLocalFinite.mixed_unit_sixth_power F)

/-- Finite-coordinate identification of Axiom's local class group. -/
def axiomFiniteClassEquiv : A.V ≃* (∀ p : A.Sf, LocalClass A p) :=
  finitePartEquiv (∀ w : InfinitePlace F, w.Completionˣ)
    (fun p : A.Sf => (p.val.adicCompletion F)ˣ) 6
    (fun g =>
      ⟨fun w => Classical.choose (A.infinite_unit_isPower w 6 (Or.inr (Or.inr rfl)) (g w)),
        funext fun w => Classical.choose_spec
          (A.infinite_unit_isPower w 6 (Or.inr (Or.inr rfl)) (g w))⟩)

/-- Canonical dictionary preserving the entire finite component. -/
def skeletonAxiomClassEquiv :
    SixthLocalClasses F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) ≃* A.V :=
  (skeletonFiniteClassEquiv A).trans (axiomFiniteClassEquiv A).symm

@[simp] theorem skeletonFiniteClassEquiv_mk
    (x : sLocalMultiplicativeGroup F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) :
    skeletonFiniteClassEquiv A (QuotientGroup.mk x) =
      fun p : A.Sf => (QuotientGroup.mk (x.2 p) : LocalClass A p) := rfl

@[simp] theorem axiomFiniteClassEquiv_mk (x : A.G) :
    axiomFiniteClassEquiv A (QuotientGroup.mk' A.sixthPowers x) =
      fun p : A.Sf => (QuotientGroup.mk (x.2 p) : LocalClass A p) := rfl

/-- The discarded complex coordinates may be chosen arbitrarily, because
every one of them is a sixth power. -/
theorem skeletonAxiomClassEquiv_mk
    (x : sLocalMultiplicativeGroup F (A.Sf : Set (HeightOneSpectrum (𝓞 F))))
    (a : ∀ w : InfinitePlace F, w.Completionˣ) :
    skeletonAxiomClassEquiv A (QuotientGroup.mk x) =
      QuotientGroup.mk' A.sixthPowers (a, x.2) := by
  apply (axiomFiniteClassEquiv A).injective
  simp [skeletonAxiomClassEquiv]

/-- Exact class dictionary on rational diagonal elements. -/
theorem skeletonAxiomClassEquiv_diagonal (a : Fˣ) :
    skeletonAxiomClassEquiv A
      (QuotientGroup.mk (sLocalFieldUnitDiagonal F
        (A.Sf : Set (HeightOneSpectrum (𝓞 F))) a)) = A.sClass a := by
  exact skeletonAxiomClassEquiv_mk A _ (A.diagonal a).1

/-- Actual finite local classes are assembled into the skeleton quotient
by the inverse of its canonical finite-coordinate equivalence. -/
def assemble : (∀ p : A.Sf, LocalClass A p) →
    SixthLocalClasses F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) :=
  (skeletonFiniteClassEquiv A).symm

@[simp] theorem assemble_finite_representatives
    (x : ∀ p : A.Sf, (p.val.adicCompletion F)ˣ) :
    assemble A (fun p => (QuotientGroup.mk (x p) : LocalClass A p)) =
      QuotientGroup.mk ((1 : (mixedEmbedding.mixedSpace F)ˣ), x) := by
  apply (skeletonFiniteClassEquiv A).injective
  simp [assemble]

/-- Pull back the actual chosen allowed complement along the canonical
class dictionary.  Taking `B = X.C.correction.B` keeps the same choice. -/
def allowedClasses (B : Subgroup A.V) :
    Set (SixthLocalClasses F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) :=
  (skeletonAxiomClassEquiv A) ⁻¹' (B : Set A.V)

/-- The actual chosen sextic Hilbert pairing, transported to the skeleton
class group and evaluated through its fixed field embedding. -/
def hilbert (σ : F →+* ℂ)
    (x y : SixthLocalClasses F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) : ℂ :=
  σ ((A.H_S6 (skeletonAxiomClassEquiv A x) (skeletonAxiomClassEquiv A y) : Fˣ) : F)

theorem hilbert_norm_one (σ : F →+* ℂ)
    (x y : SixthLocalClasses F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) :
    ‖hilbert A σ x y‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := 6) _ (by decide)
  unfold hilbert
  rw [← map_pow]
  have h := congrArg (fun u : Fˣ => (u : F))
    (A.H_S6 (skeletonAxiomClassEquiv A x) (skeletonAxiomClassEquiv A y)).property
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, map_one] using congrArg σ h

/-- The paper's Hilbert convention is the inverse of Axiom's pairing.
This follows consistently from the unit-reciprocity convention and from
the inverse Hilbert square in the literal reflected sheet integrand. -/
def reflectedHilbert (σ : F →+* ℂ)
    (x y : SixthLocalClasses F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) : ℂ :=
  (hilbert A σ x y)⁻¹

theorem reflectedHilbert_norm_one (σ : F →+* ℂ)
    (x y : SixthLocalClasses F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) :
    ‖reflectedHilbert A σ x y‖ = 1 := by
  rw [reflectedHilbert, norm_inv, hilbert_norm_one, inv_one]

/-- The exact actual mask entering the finite shell table, using the
inverse Axiom Hilbert convention required by the reflected source. -/
def reflectedClassMask (B : Subgroup A.V) (σ : F →+* ℂ)
    (κ c : SixthLocalClasses F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) : ℂ :=
  powerClassMask (allowedClasses A B) (reflectedHilbert A σ) κ c

/-- The specification uses Axiom's literal chosen complement and pairing,
with no independent arithmetic selection. -/
theorem reflectedClassMask_spec (B : Subgroup A.V) (σ : F →+* ℂ)
    (κ c : SixthLocalClasses F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) :
    reflectedClassMask A B σ κ c =
      if skeletonAxiomClassEquiv A κ * (skeletonAxiomClassEquiv A c)⁻¹ ∈ B then
        (σ ((A.H_S6 (skeletonAxiomClassEquiv A κ)
          (skeletonAxiomClassEquiv A c) : Fˣ) : F) ^ 2)⁻¹
      else 0 := by
  simp only [reflectedClassMask, powerClassMask, allowedClasses,
    Set.mem_preimage, map_mul, map_inv, reflectedHilbert, hilbert, inv_pow]

variable {S₀ : Finset (HeightOneSpectrum (𝓞 F))} {root12 : F} {σ : F →+* ℂ}

/-- Specialization to the one fixed arithmetic choice used by Base.lean. -/
def chosenClassMask (X : HeckeAxiom.ArithmeticChoice F S₀ root12 σ) :=
  reflectedClassMask X.A X.C.correction.B σ

end ThetaGlobal.ProjectFiniteClass

#print axioms ThetaGlobal.ProjectFiniteClass.skeletonAxiomClassEquiv_diagonal
#print axioms ThetaGlobal.ProjectFiniteClass.hilbert_norm_one
