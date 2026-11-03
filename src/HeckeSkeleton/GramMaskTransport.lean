import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Topology.LocallyConstant.Basic

/-!
Exact algebra for transporting a reference orbit mask to the SAME new
generator section. The correction is evaluated at the label of the input;
no independent section, complement, unit subgroup, or scalar phase is chosen.

The label/correction compatibility is an explicit hypothesis. Constancy on
sixth-power cosets alone does not imply invariance under a correction lift
representing a general unit class. No arithmetic reciprocity dictionary,
local constancy of the actual labels, or cleared-fiber depth is constructed.
The orbit-mask application is allowed to hold only on the diagonal domain,
as in the actual reference-mask theorem, rather than on all local points.
-/
set_option autoImplicit false

namespace HeckeSkeleton.GramMaskTransport

variable {X E T I V : Type*} [Group X]

/-- The exact orbit predicate of a specified generator section, using the
specified original subgroup. -/
def sectionOrbit (Γ : Subgroup X) (sourceSection : I → X) (x : X) : Prop :=
  ∃ i : I, ∃ γ : Γ, x = (γ : X) * sourceSection i

/-- Transport by the label-dependent correction, with literal right division.
This definition works for predicates, Boolean masks, and complex masks. -/
def transportMask (τ : X → T) (lift : E → X) (f : T → E)
    (M0 : X → V) (x : X) : V :=
  M0 (x / lift (f (τ x)))

/-- Right-multiplication invariance under each supplied correction also
gives right-division invariance. No homomorphism property of the lift is
assumed, and its representatives are not assumed to be sixth powers. -/
theorem label_div_lift (τ : X → T) (lift : E → X)
    (hlift : ∀ e x, τ (x * lift e) = τ x) (e : E) (x : X) :
    τ (x / lift e) = τ x := by
  have h := hlift e (x / lift e)
  simpa only [div_mul_cancel] using h.symm

/-- Exact orbit transport. The two sections have the SAME index and the
SAME original subgroup. In the commutative arithmetic application the
displayed right correction is also the usual unit-times-generator formula.
The compatibility `hlift` is an arithmetic obligation, not a consequence
of finite-range rigidity. -/
theorem sectionOrbit_transport_iff
    (Γ : Subgroup X) (reference target : I → X) (label : I → T)
    (τ : X → T) (lift : E → X) (f : T → E)
    (hreference : ∀ i, τ (reference i) = label i)
    (hΓ : ∀ (γ : Γ) x, τ ((γ : X) * x) = τ x)
    (hlift : ∀ e x, τ (x * lift e) = τ x)
    (hsection : ∀ i, target i = reference i * lift (f (label i))) (x : X) :
    sectionOrbit Γ target x ↔
      sectionOrbit Γ reference (x / lift (f (τ x))) := by
  constructor
  · rintro ⟨i, γ, rfl⟩
    have hlabel : τ ((γ : X) * target i) = label i := by
      rw [hΓ γ, hsection i, hlift, hreference i]
    refine ⟨i, γ, ?_⟩
    rw [hlabel, hsection i, ← mul_assoc, mul_div_cancel_right]
  · rintro ⟨i, γ, hx⟩
    have hlabel : τ x = label i := by
      calc
        τ x = τ (x / lift (f (τ x))) := (label_div_lift τ lift hlift _ x).symm
        _ = τ ((γ : X) * reference i) := congrArg τ hx
        _ = label i := (hΓ γ _).trans (hreference i)
    refine ⟨i, γ, ?_⟩
    calc
      x = (x / lift (f (τ x))) * lift (f (τ x)) := (div_mul_cancel _ _).symm
      _ = ((γ : X) * reference i) * lift (f (label i)) := by rw [hx, hlabel]
      _ = (γ : X) * target i := by rw [hsection i, mul_assoc]

/-- A reference mask valid only on the diagonal/source domain transports
to an exact mask of the target section on that SAME domain. Its stability
under the actual correction must be supplied explicitly. -/
theorem exact_mask_transport_on
    (Γ : Subgroup X) (reference target : I → X) (label : I → T)
    (τ : X → T) (lift : E → X) (f : T → E) (M0 : X → Prop) (D : Set X)
    (hreference : ∀ i, τ (reference i) = label i)
    (hΓ : ∀ (γ : Γ) x, τ ((γ : X) * x) = τ x)
    (hlift : ∀ e x, τ (x * lift e) = τ x)
    (hsection : ∀ i, target i = reference i * lift (f (label i)))
    (hD : ∀ x ∈ D, x / lift (f (τ x)) ∈ D)
    (hmask : ∀ x ∈ D, M0 x ↔ sectionOrbit Γ reference x)
    (x : X) (hx : x ∈ D) :
    transportMask τ lift f M0 x ↔ sectionOrbit Γ target x := by
  change M0 (x / lift (f (τ x))) ↔ sectionOrbit Γ target x
  exact (hmask _ (hD x hx)).trans
    (sectionOrbit_transport_iff Γ reference target label τ lift f
      hreference hΓ hlift hsection x).symm

/-- Left subgroup invariance transports without any commutation assumption:
the correction is on the right, and the original subgroup acts on the left.
Thus no enlargement of the original sixth-unit subgroup is needed. -/
theorem transportMask_subgroup_mul_left
    (H : Subgroup X) (τ : X → T) (lift : E → X) (f : T → E) (M0 : X → V)
    (hτ : ∀ (h : H) x, τ ((h : X) * x) = τ x)
    (hM0 : ∀ (h : H) x, M0 ((h : X) * x) = M0 x)
    (h : H) (x : X) :
    transportMask τ lift f M0 ((h : X) * x) = transportMask τ lift f M0 x := by
  unfold transportMask
  rw [hτ h x, mul_div_assoc]
  exact hM0 h _

/-- Two points in the same left coset of the FIXED subgroup have exactly
the same transported mask, with no discarded sector or phase. -/
theorem transportMask_eq_of_div_mem
    (H : Subgroup X) (τ : X → T) (lift : E → X) (f : T → E) (M0 : X → V)
    (hτ : ∀ (h : H) x, τ ((h : X) * x) = τ x)
    (hM0 : ∀ (h : H) x, M0 ((h : X) * x) = M0 x)
    (x y : X) (hxy : y / x ∈ H) :
    transportMask τ lift f M0 y = transportMask τ lift f M0 x := by
  let h : H := ⟨y / x, hxy⟩
  have hrep : (h : X) * x = y := div_mul_cancel y x
  calc
    transportMask τ lift f M0 y = transportMask τ lift f M0 ((h : X) * x) :=
      congrArg (transportMask τ lift f M0) hrep.symm
    _ = transportMask τ lift f M0 x :=
      transportMask_subgroup_mul_left H τ lift f M0 hτ hM0 h x

/-- Right-coset invariance uses exactly the commutation needed to move the
correction past the subgroup element. It is automatic for the commutative
finite local unit group, but is explicit for a general group. -/
theorem transportMask_subgroup_mul_right
    (H : Subgroup X) (τ : X → T) (lift : E → X) (f : T → E) (M0 : X → V)
    (hτ : ∀ (h : H) x, τ (x * (h : X)) = τ x)
    (hM0 : ∀ (h : H) x, M0 (x * (h : X)) = M0 x)
    (hcommute : ∀ e (h : H), Commute (h : X) (lift e))
    (h : H) (x : X) :
    transportMask τ lift f M0 (x * (h : X)) = transportMask τ lift f M0 x := by
  unfold transportMask
  rw [hτ h x]
  have hdiv : (x * (h : X)) / lift (f (τ x)) =
      (x / lift (f (τ x))) * (h : X) := by
    simp only [div_eq_mul_inv, mul_assoc]
    rw [(hcommute (f (τ x)) h).inv_right.eq]
  rw [hdiv]
  exact hM0 h _

variable {Q : Type*} [Group Q]

/-- If the reference mask factors through an actual local quotient, the
new mask has the explicit joint label `(tau x, q x)`. For finite `T,Q`
this is a fixed finite label space; no new complement is selected. -/
theorem transportMask_joint_label
    (τ : X → T) (lift : E → X) (f : T → E)
    (q : X →* Q) (select : Q → V) (M0 : X → V)
    (hM0 : ∀ x, M0 x = select (q x)) (x : X) :
    transportMask τ lift f M0 x =
      (fun a : T × Q => select (a.2 / q (lift (f a.1)))) (τ x, q x) := by
  unfold transportMask
  rw [hM0, map_div]

/-- Local constancy of the two PROVIDED labels gives local constancy of
the transported mask. No local depth for those labels is inferred here. -/
theorem transportMask_isLocallyConstant [TopologicalSpace X]
    (τ : X → T) (lift : E → X) (f : T → E)
    (q : X →* Q) (select : Q → V) (M0 : X → V)
    (hM0 : ∀ x, M0 x = select (q x))
    (hτ : IsLocallyConstant τ) (hq : IsLocallyConstant (fun x : X => q x)) :
    IsLocallyConstant (transportMask τ lift f M0) := by
  have hfactor : transportMask τ lift f M0 =
      (fun a : T × Q => select (a.2 / q (lift (f a.1)))) ∘
        (fun x : X => (τ x, q x)) := by
    funext x
    exact transportMask_joint_label τ lift f q select M0 hM0 x
  rw [hfactor]
  exact (hτ.prodMk hq).comp _

/-- An explicit finite locally constant label for the transported mask,
once the actual finite labels and their local constancy have been supplied.
Specializing `V` to `Bool` has exactly the shape used by a finite orbit mask.
The resulting label is the SAME joint label, merely enumerated by `Fin n`;
this enumeration does not establish any arithmetic identification or depth. -/
theorem exists_finite_local_label [TopologicalSpace X] [Finite T] [Finite Q]
    (τ : X → T) (lift : E → X) (f : T → E)
    (q : X →* Q) (select : Q → V) (M0 : X → V)
    (hM0 : ∀ x, M0 x = select (q x))
    (hτ : IsLocallyConstant τ) (hq : IsLocallyConstant (fun x : X => q x)) :
    ∃ n : ℕ, ∃ label : X → Fin n, IsLocallyConstant label ∧
      ∃ selectNew : Fin n → V,
        ∀ x, transportMask τ lift f M0 x = selectNew (label x) := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  letI : Fintype Q := Fintype.ofFinite Q
  let e := Fintype.equivFin (T × Q)
  let selectJoint : T × Q → V :=
    fun a => select (a.2 / q (lift (f a.1)))
  refine ⟨Fintype.card (T × Q), fun x => e (τ x, q x), ?_,
    fun j => selectJoint (e.symm j), ?_⟩
  · exact (hτ.prodMk hq).comp e
  · intro x
    change transportMask τ lift f M0 x = selectJoint (e.symm (e (τ x, q x)))
    rw [Equiv.symm_apply_apply]
    exact transportMask_joint_label τ lift f q select M0 hM0 x

end HeckeSkeleton.GramMaskTransport
