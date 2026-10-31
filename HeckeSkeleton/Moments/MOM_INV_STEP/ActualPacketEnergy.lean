import HeckeSkeleton.Moments.MOM_INV_STEP.ActualReconstructionPacket
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalChildren

/-!
# The two actual canonical columns after the second Cauchy step

The left side below is an explicit finite sum of two literal canonical
coefficients: a₀, the fixed admissible background, the inherited puncture,
the sector row, the fourth-power label row, the surviving original marks,
and the norm cutoff. No residual coefficient on the moving column is
inserted. The two independent finite column sums are contracted exactly,
and the actual arithmetic packet then gives the two positive energies.

This is the final two-column contraction. The first transform and first
Cauchy eliminate the earlier residual column pair before the second
inverse norm is expanded. The four-column historical source in
`ActualSourceReindexing` must not be identified directly with the left
side of this module; that earlier analytic coefficient identity is a
separate step, not an input equality hidden in the theorems below.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualPacketEnergy

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers FixedTripleEnergy
open ActualSourceReindexing ActualReconstructionPacket CanonicalChildren
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)
variable {σ Sector : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

local notation "Ext" => ExteriorIdeal K S

/-- The literal canonical coefficient of one moving squarefree column.
All its family fields are fixed as the row and averaged label vary. -/
def columnSummand (C : ColumnFamily K S σ Θ ψ) (sectorUnit : Sector → S.unit K)
    (c : SecondChild K Sector) (n : Ext) : ℂ :=
  CoefficientCycle.canonicalCoefficient K S D C.lambda n *
    heckeIdealCoefficient K (C.background c.1) n.val *
    (if IsCoprime n.val.val (childPuncture C.originalPuncture c.1) then 1 else 0) *
    sectorRow K S D sectorUnit n c.2.2 * labelRow K S D n c.2.1 ^ 4 *
    divisorMark (C.survivors c.1) C.primeLists C.primeWeights n.val.val *
    C.cutoff c.1 ((n.val.val.absNorm : ℝ) / C.base ^ C.columnLength c.1)

theorem childValue_eq_sum (C : ColumnFamily K S σ Θ ψ)
    (sectorUnit : Sector → S.unit K) (c : SecondChild K Sector) :
    childValue K S D C sectorUnit c =
      ∑ n ∈ C.columns c.1, columnSummand K S D C sectorUnit c n := rfl

variable {Jo Jn : ℕ}
variable (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
variable (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
variable (sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector))

/-- Exact contraction of the final two residual columns, with every
original outer scalar and label zero retained. No equality with an
abstract packet sum is assumed. -/
theorem literal_child_expansion
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (scalar : SecondTuple K Sector Jo Jn → ℂ)
    (hscalar : ∀ x ∈ T, ‖scalar x.2.tuple‖ ≤ 1)
    (slotCap : ℕ) (ho : Jo ≤ 2 * slotCap) (hn : Jn ≤ 2 * slotCap)
    (C₁ C₂ : ColumnFamily K S σ Θ ψ) (sectorUnit : Sector → S.unit K) :
    (∑ t ∈ tupleRange oldLists newLists T,
      ∑ n ∈ C₁.columns t.outer, ∑ m ∈ C₂.columns t.outer,
        scalar t * labelZero t *
          columnSummand K S D C₁ sectorUnit (secondChild sectorTransport t) n *
          star (columnSummand K S D C₂ sectorUnit (secondChild sectorTransport t) m)) =
      (packet oldLists newLists sectorTransport T scalar hscalar slotCap ho hn).signedValue
        (childValue K S D C₁ sectorUnit) (childValue K S D C₂ sectorUnit) := by
  rw [packet_signedValue_eq_tuple_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [childValue_eq_sum, childValue_eq_sum]
  symm
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [star_sum, Finset.mul_sum]

/-- The literal second-pass canonical source is bounded by the two
canonical child energies. The reconstruction multiplicity and the
averaged-label divisor weight are supplied by the proved arithmetic
packet; the column and label normalizations are restored exactly.
There is no energy-bound premise in this theorem. -/
theorem literal_child_energy
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (scalar : SecondTuple K Sector Jo Jn → ℂ)
    (hscalar : ∀ x ∈ T, ‖scalar x.2.tuple‖ ≤ 1)
    (slotCap : ℕ) (ho : Jo ≤ 2 * slotCap) (hn : Jn ≤ 2 * slotCap)
    (C₁ C₂ : ColumnFamily K S σ Θ ψ) (sectorUnit : Sector → S.unit K)
    (V₁ V₂ : ℝ) (hZ₁ : 0 < C₁.base) (hZ₂ : 0 < C₂.base) :
    let P := packet oldLists newLists sectorTransport T scalar hscalar slotCap ho hn
    ‖∑ t ∈ tupleRange oldLists newLists T,
      ∑ n ∈ C₁.columns t.outer, ∑ m ∈ C₂.columns t.outer,
        scalar t * labelZero t *
          columnSummand K S D C₁ sectorUnit (secondChild sectorTransport t) n *
          star (columnSummand K S D C₂ sectorUnit (secondChild sectorTransport t) m)‖ ≤
      Real.sqrt (∑ γ ∈ P.triples, tripleDivisorWeight slotCap γ *
        (C₁.base ^ (C₁.columnLength γ + V₁) *
          CanonicalChildren.energy K S D C₁ sectorUnit V₁ slotCap P.labels P.rows γ)) *
      Real.sqrt (∑ γ ∈ P.triples, tripleDivisorWeight slotCap γ *
        (C₂.base ^ (C₂.columnLength γ + V₂) *
          CanonicalChildren.energy K S D C₂ sectorUnit V₂ slotCap P.labels P.rows γ)) := by
  intro P
  rw [literal_child_expansion K S D oldLists newLists sectorTransport
    T scalar hscalar slotCap ho hn C₁ C₂ sectorUnit]
  change ‖P.signedValue (childValue K S D C₁ sectorUnit)
    (childValue K S D C₂ sectorUnit)‖ ≤ _
  have hs := second_source_cauchy sectorTransport P.source P.oldLists P.newLists P.keep
    P.valid P.labels P.rows P.label_nonzero P.outer_nonzero P.child_mem slotCap
    P.old_cap P.new_cap P.scalar P.scalar_norm
    (childValue K S D C₁ sectorUnit) (childValue K S D C₂ sectorUnit)
  have hr₁ (γ : OuterTriple K) :
      childEnergy slotCap P.labels P.rows (childValue K S D C₁ sectorUnit) γ =
        C₁.base ^ (C₁.columnLength γ + V₁) *
          CanonicalChildren.energy K S D C₁ sectorUnit V₁ slotCap P.labels P.rows γ :=
    CanonicalChildren.energy_restore K S D C₁ sectorUnit V₁ slotCap P.labels P.rows γ hZ₁
  have hr₂ (γ : OuterTriple K) :
      childEnergy slotCap P.labels P.rows (childValue K S D C₂ sectorUnit) γ =
        C₂.base ^ (C₂.columnLength γ + V₂) *
          CanonicalChildren.energy K S D C₂ sectorUnit V₂ slotCap P.labels P.rows γ :=
    CanonicalChildren.energy_restore K S D C₂ sectorUnit V₂ slotCap P.labels P.rows γ hZ₂
  simp_rw [hr₁, hr₂] at hs
  exact hs

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualPacketEnergy

end
