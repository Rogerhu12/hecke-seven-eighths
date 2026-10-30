import HeckeGeneral.Characters.SIntegerModulusPhaseUnit
import HeckeGeneral.Arithmetic.SIntegerPeriodicWeights
import HeckeGeneral.Arithmetic.FiniteFourierBounds

/-!
# Actual periodic Fourier coefficients for a fixed S-unit subgroup

The finite ring is the genuine principal quotient of the valuation-defined
S-integers. Its finiteness is proved, and the additive character is the
actual positive S-local principal phase. Divisor pullback retains `f(d*a)`
for every divisor, without a unit or multiplicativity assumption. The
existing finite Fourier change-of-variable theorem transports the literal
original subgroup invariance to the dual coefficients and their orbits.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
variable (Γ : Subgroup (S.unit K))
variable (c : S.integer K) (hc : c ≠ 0)



/-- The actual reduction homomorphism on S-units, including its unit inverse. -/
def sIntegerResidueUnitHom : S.unit K →* (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))ˣ where
  toFun u := Units.map (Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K)))).toMonoidHom
    (S.unitEquivUnitsInteger K u)
  map_one' := by simp
  map_mul' u v := by simp

@[simp] theorem sIntegerResidueUnitHom_val (u : S.unit K) :
    (sIntegerResidueUnitHom K S c u : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))) =
      Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K)))
        (S.unitEquivUnitsInteger K u).val := rfl

/-- Literal invariance on S-integers is genuine unit invariance on the quotient. -/
theorem sIntegerPeriodic_unitInvariant (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : S.integer K,
      f (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) :
    PeriodicFourier.UnitInvariant (Γ.map (sIntegerResidueUnitHom K S c)) f := by
  intro u hu z
  obtain ⟨w, hw, rfl⟩ := hu
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  simpa only [sIntegerResidueUnitHom_val, ← map_mul] using hinv ⟨w, hw⟩ a

/-- The manuscript's unnormalized divisor transform, on the actual quotient. -/
def sIntegerPeriodicDivisorFourier (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ) (d : S.integer K) (h : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))) : ℂ :=
  letI := finite_sIntegerPrincipalResidue K S c hc
  letI := Fintype.ofFinite (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))
  PeriodicFourier.divisorTransform (sIntegerActualModulusAddCharacter K S hS c hc)
    f (Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))) d) h

/-- Every residue class, including zero and nonunits, occurs in this finite sum. -/
theorem sIntegerPeriodicDivisorFourier_apply (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ) (d : S.integer K) (h : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))) :
    sIntegerPeriodicDivisorFourier K S hS c hc f d h =
      letI := finite_sIntegerPrincipalResidue K S c hc
      letI := Fintype.ofFinite (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))
      ∑ a : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))), f (Ideal.Quotient.mk _ d * a) *
        sIntegerActualModulusAddCharacter K S hS c hc (h * a) := rfl

/-- The zero frequency is its literal sum and is retained. -/
theorem sIntegerPeriodicDivisorFourier_zero (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ) (d : S.integer K) :
    sIntegerPeriodicDivisorFourier K S hS c hc f d 0 =
      letI := finite_sIntegerPrincipalResidue K S c hc
      letI := Fintype.ofFinite (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))
      ∑ a : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))), f (Ideal.Quotient.mk _ d * a) := by
  letI := finite_sIntegerPrincipalResidue K S c hc
  letI := Fintype.ofFinite (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))
  exact PeriodicFourier.divisorTransform_zero _ f _

/-- The phase in each term is the actual standard S-local phase of h*a/c.
Representatives are chosen only to display the formula; the left side is
defined on the quotient and therefore independent of these representatives. -/
theorem sIntegerPeriodicDivisorFourier_principal_phase
    (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ) (d h : S.integer K) :
    sIntegerPeriodicDivisorFourier K S hS c hc f d (Ideal.Quotient.mk _ h) =
      letI := finite_sIntegerPrincipalResidue K S c hc
      letI := Fintype.ofFinite (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))
      ∑ a : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))), f (Ideal.Quotient.mk _ d * a) *
        sLocalPrincipalPhase K S (((h : K) * ((Quotient.out a : S.integer K) : K)) /
          (c : K)) := by
  letI := finite_sIntegerPrincipalResidue K S c hc
  letI := Fintype.ofFinite (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))
  rw [sIntegerPeriodicDivisorFourier_apply]
  apply Finset.sum_congr rfl
  intro a _ha
  congr 1
  calc
    _ = sIntegerActualModulusAddCharacter K S hS c hc
        (Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))) h *
          Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))) (Quotient.out a)) := by
      rw [Ideal.Quotient.mk_out]
    _ = sIntegerActualModulusAddCharacter K S hS c hc
        (Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))) (h * Quotient.out a)) := by
      rw [map_mul (Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))))]
    _ = _ := sIntegerActualModulusAddCharacter_mk K S hS c hc (h * Quotient.out a)

/-- No invertibility of d is needed for subgroup invariance of its pullback. -/
theorem sIntegerPeriodic_divisorPullback_unitInvariant (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : S.integer K,
      f (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) (d : S.integer K) :
    PeriodicFourier.UnitInvariant (Γ.map (sIntegerResidueUnitHom K S c))
      (fun a : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) => f (Ideal.Quotient.mk _ d * a)) :=
  PeriodicFourier.dilate_unitInvariant _ f
    (sIntegerPeriodic_unitInvariant K S Γ c f hinv) _

/-- The original subgroup, reduced to residue units, preserves every dual frequency. -/
theorem sIntegerPeriodicDivisorFourier_unit_invariant (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : S.integer K,
      f (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) (d : S.integer K) (u : Γ) (h : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))) :
    sIntegerPeriodicDivisorFourier K S hS c hc f d
        ((sIntegerResidueUnitHom K S c u.val : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))) * h) =
      sIntegerPeriodicDivisorFourier K S hS c hc f d h := by
  letI := finite_sIntegerPrincipalResidue K S c hc
  letI := Fintype.ofFinite (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))
  have hu : sIntegerResidueUnitHom K S c u.val ∈ Γ.map (sIntegerResidueUnitHom K S c) :=
    ⟨u.val, u.property, rfl⟩
  exact PeriodicFourier.fourier_unit_invariant
    (sIntegerActualModulusAddCharacter K S hS c hc)
    (PeriodicFourier.dilate (Ideal.Quotient.mk _ d) f)
    (sIntegerResidueUnitHom K S c u.val)
    (sIntegerPeriodic_divisorPullback_unitInvariant K S Γ c f hinv d _ hu) h

/-- Literal S-integer invariance has the exact form required for orbit descent. -/
theorem sIntegerPeriodicDivisorFourier_literal_invariant (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : S.integer K,
      f (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) (d : S.integer K) :
    ∀ u : Γ, ∀ a : S.integer K,
      sIntegerPeriodicDivisorFourier K S hS c hc f d
          (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u.val).val * a)) =
        sIntegerPeriodicDivisorFourier K S hS c hc f d (Ideal.Quotient.mk _ a) := by
  intro u a
  rw [map_mul]
  exact sIntegerPeriodicDivisorFourier_unit_invariant K S hS Γ c hc f hinv d u _

/-- The bound is the actual finite L1 mass of f(d*a), including nonunit fibres. -/
theorem norm_sIntegerPeriodicDivisorFourier_le_pullback_L1
    (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ) (d : S.integer K) (h : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))) :
    ‖sIntegerPeriodicDivisorFourier K S hS c hc f d h‖ ≤
      sIntegerPeriodicResidueL1 K S c hc (fun a : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) => f (Ideal.Quotient.mk _ d * a)) := by
  letI := finite_sIntegerPrincipalResidue K S c hc
  letI := Fintype.ofFinite (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))
  exact PeriodicFourier.norm_divisorTransform_le_pullback_mass
    (sIntegerActualModulusAddCharacter K S hS c hc) f _ h

/-- Actual Fourier coefficients on every sector of the original fixed subgroup. -/
def sIntegerPeriodicFourierOrbitWeight (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : S.integer K,
      f (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) (d : S.integer K) : SIntegerOrbits K S Γ → ℂ :=
  sIntegerPeriodicOrbitWeight K S Γ c
    (sIntegerPeriodicDivisorFourier K S hS c hc f d)
    (sIntegerPeriodicDivisorFourier_literal_invariant K S hS Γ c hc f hinv d)

@[simp] theorem sIntegerPeriodicFourierOrbitWeight_mk (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : S.integer K,
      f (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) (d : S.integer K)
    (a : NonzeroRingElements (S.integer K)) :
    sIntegerPeriodicFourierOrbitWeight K S hS Γ c hc f hinv d (Quotient.mk _ a) =
      sIntegerPeriodicDivisorFourier K S hS c hc f d (Ideal.Quotient.mk _ a.val) := rfl

/-- The orbit bound is independent of the chosen frequency and orbit. -/
theorem norm_sIntegerPeriodicFourierOrbitWeight_le_pullback_L1 (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : S.integer K,
      f (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) (d : S.integer K) (q : SIntegerOrbits K S Γ) :
    ‖sIntegerPeriodicFourierOrbitWeight K S hS Γ c hc f hinv d q‖ ≤
      sIntegerPeriodicResidueL1 K S c hc (fun a : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) => f (Ideal.Quotient.mk _ d * a)) := by
  refine Quotient.inductionOn q (fun a => ?_)
  rw [sIntegerPeriodicFourierOrbitWeight_mk]
  exact norm_sIntegerPeriodicDivisorFourier_le_pullback_L1 K S hS c hc f d _

end HeckeGeneral.Arithmetic

