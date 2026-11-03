import HeckeGeneral.Arithmetic.SIntegerModulus
import HeckeGeneral.Arithmetic.SIntegerOrbitEnumeration

/-! Actual periodic residue functions descend to every subgroup sector when
the literal unit action preserves the function. Their bounds come from the
proved finiteness of the actual principal residue ring. Nonunit arguments
are retained. -/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (Γ : Subgroup (S.unit K))
variable (c : S.integer K) (hc : c ≠ 0)



/-- The periodic coefficient on all actual subgroup orbits. -/
def sIntegerPeriodicOrbitWeight (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : S.integer K,
      f (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) : SIntegerOrbits K S Γ → ℂ :=
  Quotient.lift (fun a => f (Ideal.Quotient.mk _ a.val)) (by
    intro a b hab
    obtain ⟨u, hu⟩ := (sIntegerOrbitRelation_iff K S Γ a b).mp hab
    have he : (S.unitEquivUnitsInteger K u.val).val * b.val = a.val :=
      Subtype.ext hu
    have h := hinv u b.val
    rw [he] at h
    exact h)

@[simp] theorem sIntegerPeriodicOrbitWeight_mk (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : S.integer K,
      f (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) (a : NonzeroRingElements (S.integer K)) :
    sIntegerPeriodicOrbitWeight K S Γ c f hinv (Quotient.mk _ a) =
      f (Ideal.Quotient.mk _ a.val) := rfl

/-- An explicit finite L1 bound from the genuine quotient, including every
residue class. The nonzero proof supplies finiteness rather than a hypothesis
that the coefficient function is bounded. -/
def sIntegerPeriodicResidueL1 (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ) : ℝ :=
  letI := finite_sIntegerPrincipalResidue K S c hc
  letI := Fintype.ofFinite (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))
  ∑ z : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))), ‖f z‖

theorem sIntegerPeriodicResidueL1_nonneg (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ) :
    0 ≤ sIntegerPeriodicResidueL1 K S c hc f := by
  unfold sIntegerPeriodicResidueL1
  exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem norm_sIntegerPeriodicResidue_le_L1 (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ) (z : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))) :
    ‖f z‖ ≤ sIntegerPeriodicResidueL1 K S c hc f := by
  letI := finite_sIntegerPrincipalResidue K S c hc
  letI := Fintype.ofFinite (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))
  unfold sIntegerPeriodicResidueL1
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ z)

/-- A uniform bound on every orbit follows from the actual finite quotient. -/
theorem norm_sIntegerPeriodicOrbitWeight_le_L1 (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : S.integer K,
      f (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) (q : SIntegerOrbits K S Γ) :
    ‖sIntegerPeriodicOrbitWeight K S Γ c f hinv q‖ ≤
      sIntegerPeriodicResidueL1 K S c hc f := by
  refine Quotient.inductionOn q (fun a => ?_)
  rw [sIntegerPeriodicOrbitWeight_mk]
  exact norm_sIntegerPeriodicResidue_le_L1 K S c hc f _

include hc in
theorem exists_sIntegerPeriodicOrbitWeight_uniform_bound (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : S.integer K,
      f (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : SIntegerOrbits K S Γ,
      ‖sIntegerPeriodicOrbitWeight K S Γ c f hinv q‖ ≤ C :=
  ⟨sIntegerPeriodicResidueL1 K S c hc f,
    sIntegerPeriodicResidueL1_nonneg K S c hc f,
    norm_sIntegerPeriodicOrbitWeight_le_L1 K S Γ c hc f hinv⟩

end HeckeGeneral.Arithmetic

