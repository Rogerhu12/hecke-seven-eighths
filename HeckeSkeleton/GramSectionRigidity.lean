import HeckeGeneral.Analysis.PhysicalProbeData
import HeckeGeneral.Arithmetic.SIntegerOrbitEnumeration
import Mathlib.Tactic.Ring

/-!
Finite algebra for the GR-12 same-section mask frontier.
No sorry, axiom, Gram estimate, or witness-identification assumption is used
by the proofs below. The arithmetic reciprocity/separation dictionary remains
an explicit unproved obligation, rather than an assertion of this file.
-/

noncomputable section

namespace HeckeSkeleton.GramSectionRigidity

/-- Tests may omit any finite set of primes. This is the exact abstract
form needed when reciprocity is available only for coprime ideals. -/
def SeparatesOutsideFinite {R T E V : Type*}
    (probeLabel : R → T) (pairing : T → E → V) : Prop :=
  ∀ (F : Finset R) (x y : E),
    (∀ r : R, r ∉ F → pairing (probeLabel r) x = pairing (probeLabel r) y) → x = y

/-- A reciprocal pairing forces the unit twist to be constant on each
finite-label fiber. Only probes outside the two finite bad supports occur.
In the arithmetic application `I` is an actual exterior ideal, `R` an
exterior prime, `twist I` the quotient of TWO actual generator sections
modulo sixth units, and `bad I` its prime support. -/
theorem reciprocal_twist_fiber_rigidity {I R T E V : Type*}
    (label : I → T) (twist : I → E)
    (probeLabel : R → T) (probeTwist : R → E) (bad : I → Finset R)
    (pairing : T → E → V)
    (hrec : ∀ i r, r ∉ bad i →
      pairing (probeLabel r) (twist i) = pairing (label i) (probeTwist r))
    (hsep : SeparatesOutsideFinite probeLabel pairing)
    {i j : I} (hlabel : label i = label j) : twist i = twist j := by
  classical
  apply hsep (bad i ∪ bad j)
  intro r hr
  have hr' : r ∉ bad i ∧ r ∉ bad j := by
    simpa only [Finset.mem_union, not_or] using hr
  calc
    pairing (probeLabel r) (twist i) = pairing (label i) (probeTwist r) :=
      hrec i r hr'.1
    _ = pairing (label j) (probeTwist r) := congrArg (fun t => pairing t (probeTwist r)) hlabel
    _ = pairing (probeLabel r) (twist j) := (hrec j r hr'.2).symm

/-- Exact factorization through the image of the labels. No surjectivity
of prime labels, or prime in a specified Frobenius class, is assumed. -/
theorem reciprocal_twist_factors_through_labels {I R T E V : Type*}
    (label : I → T) (twist : I → E)
    (probeLabel : R → T) (probeTwist : R → E) (bad : I → Finset R)
    (pairing : T → E → V)
    (hrec : ∀ i r, r ∉ bad i →
      pairing (probeLabel r) (twist i) = pairing (label i) (probeTwist r))
    (hsep : SeparatesOutsideFinite probeLabel pairing) :
    ∃ f : Set.range label → E,
      ∀ i : I, f ⟨label i, ⟨i, rfl⟩⟩ = twist i := by
  classical
  refine ⟨fun t => twist (Classical.choose t.property), ?_⟩
  intro i
  apply reciprocal_twist_fiber_rigidity label twist probeLabel probeTwist bad pairing hrec hsep
  exact Classical.choose_spec (show ∃ j, label j = label i from ⟨i, rfl⟩)

/-- Finite labels force a finite range of actual unit twists. This is
finite-range rigidity only: it does NOT yet supply a fixed S-local mask. -/
theorem reciprocal_twist_finite_range {I R T E V : Type*} [Finite T]
    (label : I → T) (twist : I → E)
    (probeLabel : R → T) (probeTwist : R → E) (bad : I → Finset R)
    (pairing : T → E → V)
    (hrec : ∀ i r, r ∉ bad i →
      pairing (probeLabel r) (twist i) = pairing (label i) (probeTwist r))
    (hsep : SeparatesOutsideFinite probeLabel pairing) :
    (Set.range twist).Finite := by
  obtain ⟨f, hf⟩ := reciprocal_twist_factors_through_labels
    label twist probeLabel probeTwist bad pairing hrec hsep
  apply (Set.finite_range f).subset
  rintro x ⟨i, rfl⟩
  exact ⟨⟨label i, ⟨i, rfl⟩⟩, hf i⟩

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The missing finite-mask statement for the SAME input section. A finite
label and its local constancy must be proved; arbitrary representative
choices on the ideal/unit orbit quotient do not establish this predicate. -/
def SameGeneratorFiniteMask (D : ThetaArithmeticData K S) : Prop :=
  ∃ n : ℕ, ∃ label : SFiniteLocalGroup K S → Fin n,
    IsLocallyConstant label ∧ ∃ select : Fin n → Bool,
    ∀ m : NonzeroRingElements (S.integer K),
      select (label (sLocalNonzeroIntegerDiagonal K S m).2) = true ↔
        ∃ I : ExteriorIdeal K S, ∃ γ : sixthPowerUnits K S,
          m = sIntegerOrbitTranslate K S (sixthPowerUnits K S) γ
            ⟨D.generator I, D.generator_ne_zero I⟩

/-- A concrete sixth unit from P's OWN multiplicativity; no independently
chosen generator-division unit is asserted to belong to Gamma. -/
def sameGeneratorProductSector (D : ThetaArithmeticData K S)
    (hallowed : AllowedGeneratorInput K S D) (I J : ExteriorIdeal K S) :
    sixthPowerUnits K S :=
  let u := Classical.choose (hallowed.multiplicative I J)
  ⟨u ^ 6, ⟨u, rfl⟩⟩

theorem sameGeneratorProductSector_spec (D : ThetaArithmeticData K S)
    (hallowed : AllowedGeneratorInput K S D) (I J : ExteriorIdeal K S) :
    D.generator (exteriorMul K S I J) =
      (S.unitEquivUnitsInteger K (sameGeneratorProductSector K S D hallowed I J).val).val *
        D.generator I * D.generator J := by
  let u := Classical.choose (hallowed.multiplicative I J)
  change D.generator (exteriorMul K S I J) =
    (S.unitEquivUnitsInteger K (u ^ 6)).val * D.generator I * D.generator J
  rw [map_pow, Units.val_pow_eq_pow_val]
  exact Classical.choose_spec (hallowed.multiplicative I J)

/-- The same C,d,M generator section gives ONE actual sixth-unit factor
for the literal nested quotient. This is stronger than association of ideals. -/
theorem sameGenerator_nested_product (D : ThetaArithmeticData K S)
    (hallowed : AllowedGeneratorInput K S D) (C d M : ExteriorIdeal K S) :
    ∃ γ : sixthPowerUnits K S,
      D.generator (exteriorMul K S C (exteriorMul K S d M)) =
        (S.unitEquivUnitsInteger K γ.val).val *
          D.generator C * D.generator d * D.generator M := by
  refine ⟨sameGeneratorProductSector K S D hallowed C (exteriorMul K S d M) *
    sameGeneratorProductSector K S D hallowed d M, ?_⟩
  rw [sameGeneratorProductSector_spec K S D hallowed C (exteriorMul K S d M),
    sameGeneratorProductSector_spec K S D hallowed d M]
  simp only [Subgroup.coe_mul, map_mul, Units.val_mul]
  ring

/-- Exact SAME-divisor transport, together with uniqueness of the literal
two-stage quotient. The quotient is a translate by the original Gamma,
so subsequent Gamma-invariant coefficients may use it without a sector loss.
No claim about correlation outside the coprime locus is included. -/
theorem sameGenerator_nested_literal_quotient (D : ThetaArithmeticData K S)
    (hallowed : AllowedGeneratorInput K S D) (C d M : ExteriorIdeal K S) :
    ∃ γ : sixthPowerUnits K S,
      let m₀ := sIntegerOrbitTranslate K S (sixthPowerUnits K S) γ
        ⟨D.generator M, D.generator_ne_zero M⟩
      D.generator C * (D.generator d * m₀.val) =
        D.generator (exteriorMul K S C (exteriorMul K S d M)) ∧
      ∀ m : NonzeroRingElements (S.integer K),
        D.generator C * (D.generator d * m.val) =
          D.generator (exteriorMul K S C (exteriorMul K S d M)) → m = m₀ := by
  obtain ⟨γ, hγ⟩ := sameGenerator_nested_product K S D hallowed C d M
  refine ⟨γ, ?_⟩
  dsimp only
  have hm₀ : D.generator C * (D.generator d *
      (sIntegerOrbitTranslate K S (sixthPowerUnits K S) γ
        ⟨D.generator M, D.generator_ne_zero M⟩).val) =
      D.generator (exteriorMul K S C (exteriorMul K S d M)) := by
    change D.generator C * (D.generator d *
      ((S.unitEquivUnitsInteger K γ.val).val * D.generator M)) = _
    rw [hγ]
    ring
  refine ⟨hm₀, ?_⟩
  intro m hm
  apply Subtype.ext
  apply mul_left_cancel₀ (D.generator_ne_zero d)
  apply mul_left_cancel₀ (D.generator_ne_zero C)
  exact hm.trans hm₀.symm

end HeckeSkeleton.GramSectionRigidity
