import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Power-class quotients after removing a power-divisible factor

Both project models of the S-local group have the same finite-place
coordinates and different presentations of the complex coordinates.
Since sixth powers are surjective on the latter, their sixth-power class
groups are canonically identified through the finite coordinates.  This
avoids an arbitrary equivalence of archimedean models.
-/

set_option autoImplicit false
noncomputable section
namespace ThetaGlobal.FinitePowerQuotient

open scoped Classical

variable {P : Type*} (G : Type*) [CommGroup G]
variable (H : P → Type*) [∀ p, CommGroup (H p)] (n : ℕ)

abbrev PowerClass (A : Type*) [CommGroup A] := A ⧸ (powMonoidHom n : A →* A).range

/-- Projection to the actual local power classes in every finite factor. -/
def finitePartHom : PowerClass n (G × (∀ p, H p)) →* (∀ p, PowerClass n (H p)) :=
  QuotientGroup.lift (powMonoidHom n : (G × (∀ p, H p)) →* _).range
    { toFun := fun x p => QuotientGroup.mk' (powMonoidHom n : H p →* H p).range (x.2 p)
      map_one' := by funext p; exact map_one _
      map_mul' := by intro x y; funext p; exact map_mul _ _ _ }
    (by
      rintro x ⟨y, rfl⟩
      funext p
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨y.2 p, rfl⟩)

@[simp] theorem finitePartHom_mk (x : G × (∀ p, H p)) :
    finitePartHom G H n (QuotientGroup.mk x) =
      fun p => (QuotientGroup.mk (x.2 p) : PowerClass n (H p)) := rfl

/-- Only surjectivity of the n-th-power map on the discarded factor is
needed for injectivity; no assumption on the local quotient is used. -/
theorem finitePartHom_injective (hG : ∀ g : G, ∃ x, x ^ n = g) :
    Function.Injective (finitePartHom G H n) := by
  intro c d hcd
  induction c using QuotientGroup.induction_on with | H a => ?_
  induction d using QuotientGroup.induction_on with | H b => ?_
  apply QuotientGroup.eq.mpr
  have hv : ∀ p, ∃ q : H p, q ^ n = (a.2 p)⁻¹ * b.2 p := by
    intro p
    have h := congrFun hcd p
    obtain ⟨q, hq⟩ := QuotientGroup.eq.mp h
    exact ⟨q, hq⟩
  let q : ∀ p, H p := fun p => Classical.choose (hv p)
  have hq : ∀ p, q p ^ n = (a.2 p)⁻¹ * b.2 p :=
    fun p => Classical.choose_spec (hv p)
  obtain ⟨x, hx⟩ := hG (a.1⁻¹ * b.1)
  exact ⟨(x, q), Prod.ext hx (funext hq)⟩

theorem finitePartHom_surjective : Function.Surjective (finitePartHom G H n) := by
  intro c
  refine ⟨QuotientGroup.mk ((1 : G), fun p => Quotient.out (c p)), ?_⟩
  funext p
  simp

/-- Canonical removal of a factor whose n-th-power map is surjective. -/
def finitePartEquiv (hG : ∀ g : G, ∃ x, x ^ n = g) :
    PowerClass n (G × (∀ p, H p)) ≃* (∀ p, PowerClass n (H p)) :=
  MulEquiv.ofBijective (finitePartHom G H n)
    ⟨finitePartHom_injective G H n hG, finitePartHom_surjective G H n⟩

@[simp] theorem finitePartEquiv_mk (hG : ∀ g : G, ∃ x, x ^ n = g)
    (x : G × (∀ p, H p)) :
    finitePartEquiv G H n hG (QuotientGroup.mk x) =
      fun p => (QuotientGroup.mk (x.2 p) : PowerClass n (H p)) := rfl

variable (G' : Type*) [CommGroup G']

/-- Exact comparison of two archimedean presentations sharing the same
finite local groups. -/
def changeDivisibleFactor
    (hG : ∀ g : G, ∃ x, x ^ n = g) (hG' : ∀ g : G', ∃ x, x ^ n = g) :
    PowerClass n (G × (∀ p, H p)) ≃* PowerClass n (G' × (∀ p, H p)) :=
  (finitePartEquiv G H n hG).trans (finitePartEquiv G' H n hG').symm

/-- The class of a genuine element is determined by its finite coordinates;
this formula supplies the dictionary on every actual rational diagonal. -/
theorem changeDivisibleFactor_mk
    (hG : ∀ g : G, ∃ x, x ^ n = g) (hG' : ∀ g : G', ∃ x, x ^ n = g)
    (a : G) (a' : G') (b : ∀ p, H p) :
    changeDivisibleFactor G H n G' hG hG' (QuotientGroup.mk (a, b)) =
      (QuotientGroup.mk (a', b) : PowerClass n (G' × (∀ p, H p))) := by
  apply (finitePartEquiv G' H n hG').injective
  simp [changeDivisibleFactor]

end ThetaGlobal.FinitePowerQuotient

#print axioms ThetaGlobal.FinitePowerQuotient.finitePartEquiv
#print axioms ThetaGlobal.FinitePowerQuotient.changeDivisibleFactor_mk
