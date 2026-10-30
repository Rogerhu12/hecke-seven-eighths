import HeckeGeneral.Analysis.TInputUniformMoments
import HeckeGeneral.Analysis.MomentWitnessCount

/-!
Continuous and rowwise parameter uniformity for the actual source moments.

Q quasi-riemann.tex 15149--15168 keeps the physical prime-profile height
separate from both conjugated plain-witness heights; it uses parameter
Sobolev AFTER fixing the physical parameters. Q 1123--1151 gives the
finite-dimensional parameter Sobolev rule and polynomial rowwise-height
cost. Q 12456--12469 applies this to independently chosen rowwise real and
imaginary twists, and to any fixed finite number of test parameters.
Q 12573--12578 and 9336--9337 require separated heights with uniform finite
seminorm orders. Q 9356--9395 explicitly propagates finite-dimensional
height vectors and polynomial profile-seminorm growth. M 283--304 and
1649--1657 retains this order of real choices, target, seminorm and height.

The earlier scale-and-finite-label interface does NOT give uniformity over
continuous profiles. Here xi is the global physical height vector; sigma
and tau are independently selected REAL and IMAGINARY vectors in EACH
actual ideal row. The finite dimension can be padded with zero coordinates
to accommodate the two distinct plain-witness heights. All their phases
are put into their respective actual profiles and the common scalar t
argument is evaluated at ZERO. Equality with the physical source factors
remains a literal coefficient/profile calibration obligation.

ParameterUniformCanonicalAdmissibility and ParameterUniformMI/PInput are
UNINSTANTIATED source inputs. They assert no final row count or high bound.
The threshold-count consumers at the end are proved from the displayed
actual finite energy sums, with exactly the same uniform constants.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ConditionalMoments

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- One set of constants for the entire continuous and rowwise family.
The two row maps retain independent choices for every component in every
actual ideal row; they are quantified AFTER C, scale threshold and height
data. The real-part compact bound is a pretarget choice. -/
def ParameterHeightBound {n : ℕ} {ι : Type} (active : ℝ → Finset ι)
    (realBound : ℝ)
    (E : ℝ → (Fin n → ℝ) → (NonzeroIdeal K → Fin n → ℝ) →
      (NonzeroIdeal K → Fin n → ℝ) → ι → ℝ)
    (power : ℝ → ι → ℝ) (ε : ℝ) : Prop :=
  ∃ C Z₀ A ceiling : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ 0 ≤ A ∧ 0 < ceiling ∧
    ∀ (Z : ℝ) (ξ : Fin n → ℝ), Z₀ ≤ Z → ‖ξ‖ ≤ Z ^ ceiling →
      ∀ σ τ : NonzeroIdeal K → Fin n → ℝ,
        (∀ u, ‖σ u‖ ≤ realBound) → (∀ u, ‖τ u‖ ≤ 1 + ‖ξ‖) →
        ∀ i ∈ active Z,
          E Z ξ σ τ i ≤ C * Z ^ (power Z i + ε) * (1 + ‖ξ‖) ^ A

/-- Structural source compatibility for a whole continuous parameter
family, not a collection of unrelated per-parameter admissibility proofs.
Both predicates must identify the actual canonical arithmetic rows,
sector/reciprocity coefficients, fixed initial masks and original zero
extensions. They must enforce disjoint analytic prime supports before
masks, coefficients independent of the moving row, common moving-puncture
budgets and recursive capacity rules throughout the family.

For each required finite derivative order, the annular/profile seminorms
and separated Fourier norms must have ONE polynomial growth bound in the
global height, uniformly in Z, active labels and ALL rowwise sigma/tau
choices in their stated ranges. This includes mixed derivatives for the
independent witness parameters, so Q's rowwise Sobolev rule applies.
Arithmetic data and conductors may not vary without a common source
calibration. The paired predicate also identifies the exact inducing
characters, exceptional exclusions and conjugated profiles/height signs.

These two named obligations contain no moment or count inequality. No
instance and no map from either older admissibility record is supplied. -/
structure ParameterUniformCanonicalAdmissibility (ω : HeckeCharacter K) where
  inverse : {n : ℕ} → {ι : Type} → RealBox → ℝ → ℕ →
    (active : ℝ → Finset ι) → (a : ℝ → ι → RealParameters) →
    (g : ℝ → (Fin n → ℝ) → ι → SlotGeometry K) →
    (ψ : HeckeCharacter K) →
    (ℝ → (Fin n → ℝ) → (NonzeroIdeal K → Fin n → ℝ) →
      (NonzeroIdeal K → Fin n → ℝ) → ι → MomentData K ω ψ) → Prop
  paired : {n : ℕ} → {ι : Type} → RealBox → ℝ → ℕ →
    (active : ℝ → Finset ι) → (a : ℝ → ι → RealParameters) →
    (g : ℝ → (Fin n → ℝ) → ι → SlotGeometry K) →
    (ψ : HeckeCharacter K) →
    (ℝ → (Fin n → ℝ) → (NonzeroIdeal K → Fin n → ℝ) →
      (NonzeroIdeal K → Fin n → ℝ) → ι → MomentData K ω ψ) → Prop

variable {K}

/-- Parameter dimension, compact real ranges and loss precede the mesh.
All numerical curves and analytic geometry precede the target; uniform
constants follow the whole actual profile/arithmetic family, and precede
every continuous or rowwise parameter choice. -/
def ParameterUniformMIInput (ω : HeckeCharacter K)
    (cal : ParameterUniformCanonicalAdmissibility K ω) : Prop :=
  ∀ n : ℕ, ∀ b : RealBox, ∀ ε : ℝ, 0 < ε →
    ∃ mesh : ℝ, 0 < mesh ∧
      ∀ {ι : Type} (active : ℝ → Finset ι) (a : ℝ → ι → RealParameters)
        (g : ℝ → (Fin n → ℝ) → ι → SlotGeometry K) (maxSlots : ℕ),
        (∀ Z, 1 ≤ Z → ∀ i ∈ active Z,
          InBox b (a Z i) ∧ MIRegion (a Z i) ∧ MIUniformMargins b (a Z i)) →
        (∀ Z ξ, 1 ≤ Z → ∀ i ∈ active Z,
          (g Z ξ i).fitsMesh mesh ∧ (g Z ξ i).totalLength = (a Z i).z ∧
          (g Z ξ i).slotCount ≤ maxSlots) →
        ∀ ψ : HeckeCharacter K, ψ ∈ HeckePacket K ω →
        ∀ d : ℝ → (Fin n → ℝ) → (NonzeroIdeal K → Fin n → ℝ) →
            (NonzeroIdeal K → Fin n → ℝ) → ι → MomentData K ω ψ,
          (∀ Z ξ σ τ, 1 ≤ Z → (∀ u, ‖σ u‖ ≤ b.upper) →
            (∀ u, ‖τ u‖ ≤ 1 + ‖ξ‖) → ∀ i ∈ active Z,
              (d Z ξ σ τ i).geometry = g Z ξ i) →
          cal.inverse b mesh maxSlots active a g ψ d →
          ParameterHeightBound K active b.upper
            (fun Z ξ σ τ i => inverseEnergy (d Z ξ σ τ i) (a Z i) Z 0)
            (fun Z i => (a Z i).m) ε

/-- P with independent continuous and rowwise witness profiles, retaining
the actual finite-order boundary, zero-slot branch and exceptional rows. -/
def ParameterUniformPInput (ω : HeckeCharacter K)
    (cal : ParameterUniformCanonicalAdmissibility K ω) : Prop :=
  ∀ n : ℕ, ∀ b : RealBox, ∀ ε : ℝ, 0 < ε →
    ∃ mesh : ℝ, 0 < mesh ∧
      ∀ {ι : Type} (active : ℝ → Finset ι) (a : ℝ → ι → RealParameters)
        (g : ℝ → (Fin n → ℝ) → ι → SlotGeometry K) (maxSlots : ℕ),
        (∀ Z, 1 ≤ Z → ∀ i ∈ active Z,
          InBox b (a Z i) ∧ PRegion (a Z i) ∧
          FiniteOrderBoundary (K := K) ((1 + (a Z i).κ) / 2)) →
        (∀ Z ξ, 1 ≤ Z → ∀ i ∈ active Z,
          (g Z ξ i).fitsMesh mesh ∧ (g Z ξ i).totalLength = (a Z i).z ∧
          (g Z ξ i).slotCount ≤ maxSlots) →
        ∀ ψ : HeckeCharacter K, ψ ∈ HeckePacket K ω →
        ∀ d : ℝ → (Fin n → ℝ) → (NonzeroIdeal K → Fin n → ℝ) →
            (NonzeroIdeal K → Fin n → ℝ) → ι → MomentData K ω ψ,
          (∀ Z ξ σ τ, 1 ≤ Z → (∀ u, ‖σ u‖ ≤ b.upper) →
            (∀ u, ‖τ u‖ ≤ 1 + ‖ξ‖) → ∀ i ∈ active Z,
              (d Z ξ σ τ i).geometry = g Z ξ i) →
          cal.paired b mesh maxSlots active a g ψ d →
          (∀ Z ξ σ τ, 1 ≤ Z → (∀ u, ‖σ u‖ ≤ b.upper) →
            (∀ u, ‖τ u‖ ≤ 1 + ‖ξ‖) → ∀ i ∈ active Z, ∀ j,
              (d Z ξ σ τ i).slotCoefficient j ∈ (d Z ξ σ τ i).theta) →
          ParameterHeightBound K active b.upper
            (fun Z ξ σ τ i => pairedEnergy (d Z ξ σ τ i) (a Z i) Z 0)
            (fun Z i => (a Z i).m + (a Z i).q) ε

variable (K)

omit [NumberField K] in
/-- A proved consumer: subtract the ACTUAL squared-norm threshold power.
Uniformity in the continuous and rowwise parameters is preserved verbatim. -/
theorem parameterHeightBound_energyWitnessRows {n : ℕ} {ι κ : Type}
    (active : ℝ → Finset ι) (realBound : ℝ)
    (F : ℝ → (Fin n → ℝ) → (NonzeroIdeal K → Fin n → ℝ) →
      (NonzeroIdeal K → Fin n → ℝ) → ι → Finset κ)
    (z : ℝ → (Fin n → ℝ) → (NonzeroIdeal K → Fin n → ℝ) →
      (NonzeroIdeal K → Fin n → ℝ) → ι → κ → ℂ)
    {p : ℝ → ι → ℝ} {ε : ℝ}
    (h : ParameterHeightBound K active realBound
      (fun Z ξ σ τ i => ∑ u ∈ F Z ξ σ τ i, ‖z Z ξ σ τ i u‖ ^ 2) p ε)
    (v : ℝ → ι → ℝ) :
    ParameterHeightBound K active realBound
      (fun Z ξ σ τ i =>
        ((energyWitnessRows (F Z ξ σ τ i) (z Z ξ σ τ i) Z (v Z i)).card : ℝ))
      (fun Z i => p Z i - v Z i) ε := by
  obtain ⟨C, Z₀, A, ceiling, hC, hZ₀, hA, hh, hb⟩ := h
  refine ⟨C, Z₀, A, ceiling, hC, hZ₀, hA, hh, ?_⟩
  intro Z ξ hZ hξ σ τ hσ hτ i hi
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one (hZ₀.trans hZ)
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hZpos (v Z i))).mp
  calc
    _ ≤ ∑ u ∈ F Z ξ σ τ i, ‖z Z ξ σ τ i u‖ ^ 2 := energyWitnessRows_card_mul_le ..
    _ ≤ C * Z ^ (p Z i + ε) * (1 + ‖ξ‖) ^ A := hb Z ξ hZ hξ σ τ hσ hτ i hi
    _ = _ := by
      have he : p Z i + ε = (p Z i - v Z i + ε) + v Z i := by ring
      rw [he, Real.rpow_add hZpos]
      ring

end HeckeGeneral.Analysis.ConditionalMoments
