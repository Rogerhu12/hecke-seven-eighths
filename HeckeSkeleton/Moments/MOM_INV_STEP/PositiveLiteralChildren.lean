import HeckeSkeleton.Moments.MOM_INV_STEP.PositiveReconstructionPacket
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondCommonEnvelope

/-!
# One literal canonical family on the actual reconstruction packet

All original slot choices, centers and frequencies are fixed before
this family is formed. The prior puncture triple is read from the new
triple alone. Its background, surviving lists, complete squarefree pool
and genuine Schwartz test therefore have no dependence on a new row or
label. The actual second column is proved equal to this family's column,
and the positive source enters the proved fixed-triple fiber bound.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PositiveLiteralChildren

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep FixedTripleFibers FixedTripleEnergy CanonicalChildren
open CanonicalNormPools PositiveReconstruction PositiveReconstructionPacket
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

def priorTriple (γ : OuterTriple K) : OuterTriple K := ⟨γ.q0,γ.quotient,1⟩

def family (C : ColumnFamily K Sset σ Θ ψ) (G : HeckeCharacter K)
    (hG : G ∈ Θ) (J : Finset σ) (U t : ℝ) : ColumnFamily K Sset σ Θ ψ where
  lambda := C.lambda
  background := fun γ => C.background (priorTriple K γ) * G⁻¹
  background_admissible := fun γ => BackgroundCycle.admissible_mul_inv K Θ ψ
    (C.background (priorTriple K γ)) G (C.background_admissible _) hG
  originalPuncture := C.originalPuncture
  originalSlots := C.originalSlots
  primeLists := C.primeLists
  primeWeights := C.primeWeights
  survivors := fun γ => C.survivors (priorTriple K γ) \ J
  survivors_subset := fun γ => Finset.sdiff_subset.trans (C.survivors_subset _)
  columns := fun _ => squarefreePool K Sset (2 * U)
  columns_squarefree := fun _ _ hn => squarefreePool_squarefree K Sset hn
  cutoff := fun _ => FinalMellinTests.weightedTest 0 t
  base := C.base
  columnLength := fun _ => Real.log U / Real.log C.base

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

theorem family_column (C : ColumnFamily K Sset σ Θ ψ) (G : HeckeCharacter K)
    (hG : G ∈ Θ) (J : Finset σ) (U t : ℝ) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (y : Ideal (𝓞 K) × Sector) :
    column K Sset D (family K S C G hG J U t) (CanonicalSectors.sectorUnit K Sset Γ) γ f y =
      column K Sset D (SecondCenteredFamily.family K S C (priorTriple K γ) G hG J U t)
        (CanonicalSectors.sectorUnit K Sset Γ) γ f y := rfl

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable {Jo Jn : ℕ} {N : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))))} {X : ℝ}
variable {oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K))}
variable {newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K))}
local notation "Src" => PositiveReconstruction.Source K S D Γ N X oldLists newLists

theorem priorTriple_source (B : Src) : priorTriple K B.outer =
    FirstColumnAssembly.firstTriple K S B.refs.1 B.refs.2 B.b₁ B.b₂ B.quotient := by
  apply OuterTriple.ext
  · exact (CanonicalCubeLabels.q0_val K S B.b₁ B.b₂ _ _).symm
  · rfl
  · rfl

/-- The displayed source column is exactly the column occurring inside
SecondPositiveChildren's Mellin energy, including its two genuine
divisor sector translations. -/
def sourceColumn (C : ColumnFamily K Sset σ Θ ψ) (G : HeckeCharacter K)
    (hG : G ∈ Θ) (J : Finset σ) (U t : ℝ) (B : Src) : ℂ :=
  column K Sset D
    (SecondCenteredFamily.family K S C
      (FirstColumnAssembly.firstTriple K S B.refs.1 B.refs.2 B.b₁ B.b₂ B.quotient)
      G hG J U t) (CanonicalSectors.sectorUnit K Sset Γ)
    (SecondCenteredFamily.appendResidual K
      (FirstColumnAssembly.firstTriple K S B.refs.1 B.refs.2 B.b₁ B.b₂ B.quotient)
      (SecondOverlapColumns.residual K S B.common B.d₂).val.val)
    (SecondCompleteColumns.finalLabel K S B.firstLabel B.d₂ B.overlap).val.val
    ((SecondSourceColumns.newRowIdeal K S B.frequency.1
        (sIntegerMaskGenerator K Sset B.firstDivisor)
        (sIntegerMaskGenerator K Sset B.secondDivisor)).val.val,
      SecondSourceColumns.newSector K S Γ D
        (sIntegerMaskGenerator K Sset B.firstDivisor)
        (sIntegerMaskGenerator K Sset B.secondDivisor) B.frequency.2)

theorem sourceColumn_eq (C : ColumnFamily K Sset σ Θ ψ) (G : HeckeCharacter K)
    (hG : G ∈ Θ) (J : Finset σ) (U t : ℝ) (B : Src) :
    sourceColumn K S D Γ C G hG J U t B =
      childValue K Sset D (family K S C G hG J U t)
        (CanonicalSectors.sectorUnit K Sset Γ) (B.outer,B.newLabel,B.newRow) := by
  unfold sourceColumn childValue
  rw [B.literal_outer, B.literal_label, B.literal_row,
    family_column K S D Γ, priorTriple_source K S D Γ B]

/-- The actual physical scalar has precisely the common norm cost and
the original retained zeros. This identity precedes all scalar bounds. -/
theorem physical_scalar_with_overlap (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (hX : 0 < C.base ^ C.columnLength γ)
    (r : {r : ℝ // 0 < r}) (B : Src) :
    ‖SecondParentRetained.sourceScalar K S C γ hX r B.secondDivisor
      B.common B.firstLabel (sIntegerMaskGenerator K Sset B.firstDivisor)‖ *
      ‖SecondColumnEnergy.overlapZero K S B.common B.firstLabel B.overlap‖ =
      (ActualPoissonScale.fieldConstant K * height K Sset B.commonResidual /
        (r.val * C.base ^ C.columnLength γ)) *
        ‖B.retainedZero (childPuncture C.originalPuncture γ)‖ := by
  have hpos : 0 ≤ SecondPoissonNormalization.outerFactor K S r
      (sIntegerMaskGenerator K Sset B.secondDivisor) /
        (C.base ^ C.columnLength γ / height K Sset B.common) :=
    div_nonneg (SecondPoissonNormalization.outerFactor_nonneg K S r _)
      (div_pos hX (height_pos K Sset B.common)).le
  unfold SecondParentRetained.sourceScalar SecondParentRetained.residualScale
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos]
  rw [SecondCommonEnvelope.scalar_cost_eq K S r
    (sIntegerMaskGenerator K Sset B.secondDivisor) B.common B.common_squarefree
    B.d₂_dvd _ hX]
  change (_ * ‖SecondSourceAssembly.sliceScalar K S C γ B.common B.firstLabel
    (sIntegerMaskGenerator K Sset B.firstDivisor)‖) * _ = _
  rw [mul_assoc, ← norm_mul]
  rfl

/-- The positive source enters a literal canonical child family. The
left side is the actual second complete column; no source-to-packet or
child-energy identity is a hypothesis. -/
theorem source_energy_le_children (C : ColumnFamily K Sset σ Θ ψ)
    (G : HeckeCharacter K) (hG : G ∈ Θ) (J : Finset σ) (U t : ℝ)
    (T : Finset Src) (R : Src → Ideal (𝓞 K)) (a : Src → ℂ)
    (ha : ∀ B ∈ T, ‖a B‖ ≤ 1) (slotCap : ℕ)
    (ho : Jo ≤ 2 * slotCap) (hn : Jn ≤ 2 * slotCap) :
    (∑ B ∈ T, ‖PositiveReconstructionPacket.sourceScalar R a B‖ *
      ‖sourceColumn K S D Γ C G hG J U t B‖ ^ 2) ≤
      ∑ γ ∈ (packet T R a ha slotCap ho hn).triples,
        tripleDivisorWeight slotCap γ *
          (packet T R a ha slotCap ho hn).energy
            (childValue K Sset D (family K S C G hG J U t)
              (CanonicalSectors.sectorUnit K Sset Γ)) γ := by
  simp_rw [sourceColumn_eq K S D Γ]
  exact source_energy_le_packet T R a ha slotCap ho hn _

/-- The child normalization contributes exactly N+V with one averaged
label normalization. The complete source and its original zeros remain
on the left of this production estimate. -/
theorem source_energy_le_normalized_children (C : ColumnFamily K Sset σ Θ ψ)
    (G : HeckeCharacter K) (hG : G ∈ Θ) (J : Finset σ) (U t V : ℝ)
    (hZ : 0 < C.base) (T : Finset Src) (R : Src → Ideal (𝓞 K)) (a : Src → ℂ)
    (ha : ∀ B ∈ T, ‖a B‖ ≤ 1) (slotCap : ℕ)
    (ho : Jo ≤ 2 * slotCap) (hn : Jn ≤ 2 * slotCap) :
    (∑ B ∈ T, ‖PositiveReconstructionPacket.sourceScalar R a B‖ *
      ‖sourceColumn K S D Γ C G hG J U t B‖ ^ 2) ≤
      C.base ^ (Real.log U / Real.log C.base + V) *
        ∑ γ ∈ (packet T R a ha slotCap ho hn).triples,
          tripleDivisorWeight slotCap γ * CanonicalChildren.energy K Sset D
            (family K S C G hG J U t) (CanonicalSectors.sectorUnit K Sset Γ) V slotCap
            (packet T R a ha slotCap ho hn).labels (packet T R a ha slotCap ho hn).rows γ := by
  apply (source_energy_le_children K S D Γ C G hG J U t T R a ha slotCap ho hn).trans_eq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [ReconstructionPacket.energy, CanonicalChildren.energy_restore K Sset D
    (family K S C G hG J U t) (CanonicalSectors.sectorUnit K Sset Γ) V slotCap _ _ γ hZ]
  change tripleDivisorWeight slotCap γ *
    (C.base ^ (Real.log U / Real.log C.base + V) * _) = _
  ring

end HeckeSkeleton.Moments.MOM_INV_STEP.PositiveLiteralChildren

end
