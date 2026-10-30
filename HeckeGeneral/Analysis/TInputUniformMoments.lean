import HeckeGeneral.Analysis.MomentInputs

/-!
Compact-range, moving-label versions of the source moment inputs.

Q quasi-riemann.tex 9250--9268 fixes bounded real ranges and two positive
MI margins before the implied constant; 9334--9337 makes the canonical
bound uniform in moving moduli and outer ideals. Q 12573--12578 gives the
corresponding bounded-range and moving-label uniformity for P. M
hecke_seven_eighths_all_characters.tex 283--304 and 1467--1489 places real
losses, mesh and geometry before the finite-order target twist. Q
15223--15228 and 15815--15818 permits O((log U)^2) active dyadic labels.

The older MIInput/PInput chooses constants after each fixed parameter
tuple. No implication from those predicates to the inputs below is proved
or assumed. These are more precise conditional SOURCE MOMENT statements,
not theta constructions, row counts, high estimates or zero-free results.

All energies below are the existing literal finite ideal sums. A label
may depend on scale and the number of active labels may grow. One set of
constants is selected for the entire family before any active label is
selected. Conjugate presentations, height signs and zero masks remain in
MomentData and must be calibrated with their actual source coefficients.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ConditionalMoments

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Classical BigOperators

/-- Uniform constants for a whole active family, with a literal varying
scale exponent. The height ceiling and degree are uniform in the label. -/
def UniformPolynomialHeightBound {ι : Type} (active : ℝ → Finset ι)
    (E : ℝ → ℝ → ι → ℝ) (power : ℝ → ι → ℝ) (ε : ℝ) : Prop :=
  ∃ C Z₀ A ceiling : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ 0 ≤ A ∧ 0 < ceiling ∧
    ∀ Z t : ℝ, Z₀ ≤ Z → |t| ≤ Z ^ ceiling →
      ∀ i ∈ active Z, E Z t i ≤ C * Z ^ (power Z i + ε) * (1 + |t|) ^ A

variable (K : Type) [Field K] [NumberField K]

/-- Still-uninstantiated structural source calibration on an ENTIRE
scale-and-label family. This requires actual canonical row/sector and
reciprocity identification, initial fixed-S and presentation masks,
disjoint analytic supports before masks, row-independent prime
coefficients, and permitted rowwise profiles. The relevant FINITE
seminorm bounds, common arithmetic data, moving-puncture budgets and
recursive capacity rules must be uniform across all Z >= 1 and i in
active Z. A separate certificate with its own constant at each (Z,i)
does not satisfy this obligation.

The paired predicate additionally calibrates actual inducing characters,
exceptional rows, finite-order slot coefficients and reflection. These
are structural predicates only: they contain no energy/count estimate.
No instance, and no map from the older CanonicalAdmissibility, is given. -/
structure UniformCanonicalAdmissibility (ω : HeckeCharacter K) where
  inverse : {ι : Type} → RealBox → ℝ → ℕ →
    (active : ℝ → Finset ι) →
    (parameters : ℝ → ι → RealParameters) →
    (geometry : ℝ → ι → SlotGeometry K) →
    (ψ : HeckeCharacter K) → (ℝ → ι → MomentData K ω ψ) → Prop
  paired : {ι : Type} → RealBox → ℝ → ℕ →
    (active : ℝ → Finset ι) →
    (parameters : ℝ → ι → RealParameters) →
    (geometry : ℝ → ι → SlotGeometry K) →
    (ψ : HeckeCharacter K) → (ℝ → ι → MomentData K ω ψ) → Prop

variable {K}

/-- Uniform MI at the source's bounded-range level. Active labels,
parameter curves, geometry and a uniform slot-count bound precede the
target. Uniform constants follow the entire calibrated arithmetic family. -/
def UniformMIInput (ω : HeckeCharacter K) (cal : UniformCanonicalAdmissibility K ω) : Prop :=
  ∀ b : RealBox, ∀ ε : ℝ, 0 < ε →
    ∃ mesh : ℝ, 0 < mesh ∧
      ∀ {ι : Type} (active : ℝ → Finset ι)
        (a : ℝ → ι → RealParameters) (g : ℝ → ι → SlotGeometry K) (maxSlots : ℕ),
        (∀ Z, 1 ≤ Z → ∀ i ∈ active Z,
          InBox b (a Z i) ∧ MIRegion (a Z i) ∧ MIUniformMargins b (a Z i) ∧
          (g Z i).fitsMesh mesh ∧ (g Z i).totalLength = (a Z i).z ∧
          (g Z i).slotCount ≤ maxSlots) →
        ∀ ψ : HeckeCharacter K, ψ ∈ HeckePacket K ω →
        ∀ d : ℝ → ι → MomentData K ω ψ,
          (∀ Z, 1 ≤ Z → ∀ i ∈ active Z, (d Z i).geometry = g Z i) →
          cal.inverse b mesh maxSlots active a g ψ d →
          UniformPolynomialHeightBound active
            (fun Z t i => inverseEnergy (d Z i) (a Z i) Z t)
            (fun Z i => (a Z i).m) ε

/-- Uniform paired P. The dynamic finite-order boundary is explicit for
each active kappa. The zero-slot branch has only the pretarget compact
length bounds from InBox; the existing pairedEnergy retains its precise
exceptional-row exclusion. This statement assumes no improved boundary. -/
def UniformPInput (ω : HeckeCharacter K) (cal : UniformCanonicalAdmissibility K ω) : Prop :=
  ∀ b : RealBox, ∀ ε : ℝ, 0 < ε →
    ∃ mesh : ℝ, 0 < mesh ∧
      ∀ {ι : Type} (active : ℝ → Finset ι)
        (a : ℝ → ι → RealParameters) (g : ℝ → ι → SlotGeometry K) (maxSlots : ℕ),
        (∀ Z, 1 ≤ Z → ∀ i ∈ active Z,
          InBox b (a Z i) ∧ PRegion (a Z i) ∧
          FiniteOrderBoundary (K := K) ((1 + (a Z i).κ) / 2) ∧
          (g Z i).fitsMesh mesh ∧ (g Z i).totalLength = (a Z i).z ∧
          (g Z i).slotCount ≤ maxSlots) →
        ∀ ψ : HeckeCharacter K, ψ ∈ HeckePacket K ω →
        ∀ d : ℝ → ι → MomentData K ω ψ,
          (∀ Z, 1 ≤ Z → ∀ i ∈ active Z, (d Z i).geometry = g Z i) →
          cal.paired b mesh maxSlots active a g ψ d →
          (∀ Z, 1 ≤ Z → ∀ i ∈ active Z, ∀ j,
            (d Z i).slotCoefficient j ∈ (d Z i).theta) →
          UniformPolynomialHeightBound active
            (fun Z t i => pairedEnergy (d Z i) (a Z i) Z t)
            (fun Z i => (a Z i).m + (a Z i).q) ε

end HeckeGeneral.Analysis.ConditionalMoments
