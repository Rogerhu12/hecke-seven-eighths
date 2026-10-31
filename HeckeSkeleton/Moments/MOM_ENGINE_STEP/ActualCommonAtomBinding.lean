import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonCoefficientExtraction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SourceCartesianAtlas

/-!
# Bind real occurrence branches to the reweighted common rows

The common atoms are constructed from the actual frozen plain ideals
and prime occurrences.  The source factors enter through their
single-factor dictionaries.  The exact per-column extraction supplies
the coupled pairing internally, before the exceptional split or Cauchy.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {k : ℕ}
variable {S₁ S₂ : Finset (Ideal (𝓞 F))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 F))}
variable {P : Finset (Ideal (𝓞 F))}

namespace SupportCartesianBranch

variable (b : SupportCartesianBranch S₁ S₂ S P)

/-- Pointwise windows for the actual frozen atoms. There is no bound
on a column, polynomial, transformed source or resulting child. -/
structure CommonAtomBounds (T : FixedChildCharacters F k)
    (Z : ℝ) (length : Fin k → ℝ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ) where
  base_pos : 0 < Z
  annulus : Fin k → ℝ
  profile : Fin k → ℝ
  annulus_nonneg : ∀ i, 0 ≤ annulus i
  profile_nonneg : ∀ i, 0 ≤ profile i
  plain₁ : ‖sourcePlainCoefficient T.plain T.plainTwist T.mask b.plainDivisor₁‖ ≤ 1
  plain₂ : ‖sourcePlainCoefficient T.plain T.plainTwist T.mask b.plainDivisor₂‖ ≤ 1
  prime : ∀ i ∈ Finset.univ \ b.keep,
    ‖sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask (b.witness.2 i)‖ ≤ 1
  prime_annulus : ∀ i ∈ Finset.univ \ b.keep,
    (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ) ≤ annulus i * Z ^ length i
  slot : ∀ i ∈ Finset.univ \ b.keep, ‖w i (b.witness.2 i)‖ ^ 2 ≤ profile i

namespace CommonAtomBounds

variable {b : SupportCartesianBranch S₁ S₂ S P}
variable {T : FixedChildCharacters F k} {Z : ℝ} {length : Fin k → ℝ}
variable {w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ}
variable (B : b.CommonAtomBounds T Z length w)

/-- Evaluation at one prevents double insertion of the common residue.
The full correlation still retains its genuine ramification zeros. -/
def atoms {H : Type*} (rows : Finset H) : FrozenSourceAtoms A σ H rows k where
  plain₁ := b.plainDivisor₁
  plain₂ := b.plainDivisor₂
  keep := b.keep
  primes := b.witness.2
  characters _ := T
  factor _ := 1
  residual _ := 1
  base := Z
  base_pos := B.base_pos
  length := length
  slotWeight _ := w
  annulus := B.annulus
  profile := B.profile
  annulus_nonneg := B.annulus_nonneg
  profile_nonneg := B.profile_nonneg
  plain₁_bound _ _ := B.plain₁
  plain₂_bound _ _ := B.plain₂
  prime_bound _ _ := B.prime
  prime_annulus := B.prime_annulus
  slot_bound _ _ := B.slot

theorem atoms_ideal {H : Type*} (rows : Finset H) :
    (B.atoms (A := A) (σ := σ) rows).ideal =
      b.plainExtract₁ * b.plainExtract₂ * ∏ i, b.slotExtract i :=
  b.frozenSourceIdeal_eq

theorem atoms_value {H : Type*} (rows : Finset H)
    (I : A.Exterior)
    (hI : b.plainExtract₁ * b.plainExtract₂ * (∏ i, b.slotExtract i) = I.val)
    (h : H) :
    (B.atoms (A := A) (σ := σ) rows).value h =
      b.bareCommonScalar T Z length w := by
  exact T.frozenScalar_one_eq_bare b.plainDivisor₁ b.plainDivisor₂
    Z length b.keep b.witness.2 w I (b.frozenSourceIdeal_eq.trans hI)

end CommonAtomBounds
end SupportCartesianBranch

namespace SourceCartesianAtlas

variable {I : Type*} {columns : Finset I} {ideal : I → A.Exterior}
variable (T : SourceCartesianAtlas columns ideal)
variable (P : Finset (Ideal (𝓞 F))) (D : A.Exterior)
variable (d : T.labels P D.val)
variable {chars : FixedChildCharacters F T.slotCount}
variable {Z : ℝ} {length : Fin T.slotCount → ℝ}
variable {w : Fin T.slotCount → HeightOneSpectrum (𝓞 F) → ℂ}

/-- An actual common-source label supplies the common-ideal identity;
it is not an extra calibration premise of the branch. -/
theorem common_atoms_ideal
    (B : (T.branch P D.val d).CommonAtomBounds chars Z length w)
    {H : Type*} (rows : Finset H) :
    (B.atoms (A := A) (σ := σ) rows).ideal = D.val := by
  exact (B.atoms_ideal rows).trans (T.branch_product P D.val d)

theorem common_atoms_value
    (B : (T.branch P D.val d).CommonAtomBounds chars Z length w)
    {H : Type*} (rows : Finset H) (h : H) :
    (B.atoms (A := A) (σ := σ) rows).value h =
      (T.branch P D.val d).bareCommonScalar chars Z length w :=
  B.atoms_value rows D (T.branch_product P D.val d) h

end SourceCartesianAtlas


section CenteredFactors

variable {Ray : Type*} [CommGroup Ray]
variable {T : FixedChildCharacters F k} {phase : Ray →* Circle}
variable (b : SupportCartesianBranch S₁ S₂ S P)
variable (DX DY : SecondCoefficientTermDictionary T phase S₁ S₂ S)
variable (PX PY : SecondColumnFactors F Ray k)

/-- Centering changes the two plain profiles, but the original common
prime factors and the original Gauss normalizers are the same.
These are checked at their individual fields. -/
theorem SupportCartesianBranch.identified_centered_residue_extract
    (hX : DX.FactorIdentification PX) (hY : DY.FactorIdentification PY)
    (hbase : DY.base = DX.base) (hlength : DY.length = DX.length)
    (hslots : DY.slotWeight = DX.slotWeight)
    (hN₁ : PY.leftNormalizer = PX.leftNormalizer)
    (hN₂ : PY.rightNormalizer = PX.rightNormalizer)
    (hNs : PY.slotNormalizer = PX.slotNormalizer)
    (i : AllocationColumn F b.keep.card) (hi : i ∈ b.residualColumns)
    (J : A.Exterior) (hJ : J.val = allocationColumnIdeal i) (frequency : A.R) :
    (PX.coefficient (b.reconstruct i) * (phase (PX.ray (b.reconstruct i)) : ℂ) -
      PY.coefficient (b.reconstruct i) * (phase (PY.ray (b.reconstruct i)) : ℂ)) *
        σ (A.sexticResidue J frequency) =
      b.bareCommonScalar T DX.base DX.length DX.slotWeight *
        (PX.normalizer *
          (b.residualCoefficient (σ := σ) T frequency DX.scale₁ DX.scale₂
              DX.base DX.length DX.leftWeight DX.rightWeight DX.slotWeight i -
            b.residualCoefficient (σ := σ) T frequency DY.scale₁ DY.scale₂
              DY.base DY.length DY.leftWeight DY.rightWeight DY.slotWeight i)) := by
  have hn : PY.normalizer = PX.normalizer := by
    unfold SecondColumnFactors.normalizer
    rw [hN₁, hN₂, hNs]
  have hs : b.bareCommonScalar T DY.base DY.length DY.slotWeight =
      b.bareCommonScalar T DX.base DX.length DX.slotWeight := by
    rw [hbase, hlength, hslots]
  have hx := b.identified_coefficient_residue_extract DX PX hX i hi J hJ frequency
  have hy := b.identified_coefficient_residue_extract DY PY hY i hi J hJ frequency
  rw [hs, hn] at hy
  rw [sub_mul, hx, hy]
  ring

end CenteredFactors

section CoupledSource

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ray : Type*} [CommGroup Ray]
variable {l : ℕ}
variable {T₁ T₂ : Finset (Ideal (𝓞 F))}
variable {Ts : Fin l → Finset (HeightOneSpectrum (𝓞 F))}

/-- Both original factor tables feed the exact same common-row weight
whose arithmetic calibration produces the actual capacity children.
The right residual frequency remains negative and its whole column is
conjugated by the original pairing exactly once. -/
theorem actual_common_atoms_identified_hybrid_bound
    (R : ActualSecondCorrelationRows A σ H ι) (kernel : 𝓢(V, ℂ))
    (left : SupportCartesianBranch S₁ S₂ S P)
    (right : SupportCartesianBranch T₁ T₂ Ts P)
    (leftCharacters : FixedChildCharacters F k)
    (rightCharacters : FixedChildCharacters F l)
    (phaseLeft phaseRight : Ray →* Circle)
    (DL : SecondCoefficientTermDictionary leftCharacters phaseLeft S₁ S₂ S)
    (DR : SecondCoefficientTermDictionary rightCharacters phaseRight T₁ T₂ Ts)
    (PL : SecondColumnFactors F Ray k) (PR : SecondColumnFactors F Ray l)
    (hL : DL.FactorIdentification PL) (hR : DR.FactorIdentification PR)
    (BL : left.CommonAtomBounds leftCharacters DL.base DL.length DL.slotWeight)
    (BR : right.CommonAtomBounds rightCharacters DR.base DR.length DR.slotWeight)
    (hcommonL : left.plainExtract₁ * left.plainExtract₂ * (∏ i, left.slotExtract i) =
      (primePowerProduct R.primes R.leftMultiplicity).val)
    (hcommonR : right.plainExtract₁ * right.plainExtract₂ * (∏ i, right.slotExtract i) =
      (primePowerProduct R.primes R.rightMultiplicity).val)
    (IL : AllocationColumn F left.keep.card → A.Exterior)
    (IR : AllocationColumn F right.keep.card → A.Exterior)
    (hIL : ∀ i ∈ left.residualColumns, (IL i).val = allocationColumnIdeal i)
    (hIR : ∀ i ∈ right.residualColumns, (IR i).val = allocationColumnIdeal i)
    (x : H → AllocationColumn F left.keep.card → V)
    (y : H → AllocationColumn F right.keep.card → V)
    (exceptional : H → Prop) :
    ‖jointKernelPairing kernel R.rows left.residualColumns right.residualColumns
      (fun h => R.weight h * R.correlation h)
      (fun h i => PL.coefficient (left.reconstruct i) *
        (phaseLeft (PL.ray (left.reconstruct i)) : ℂ) *
        σ (A.sexticResidue (IL i) (R.frequency h)))
      (fun h j => PR.coefficient (right.reconstruct j) *
        (phaseRight (PR.ray (right.reconstruct j)) : ℂ) *
        σ (A.sexticResidue (IR j) (-R.frequency h))) x y‖ ≤
      jointHybridKernelCost kernel R.rows left.residualColumns right.residualColumns
        (fun h => (R.withCommonAtoms (BL.atoms R.rows) (BR.atoms R.rows)).weight h *
          R.correlation h)
        (fun h i => PL.normalizer *
          left.residualCoefficient (σ := σ) leftCharacters (R.frequency h)
            DL.scale₁ DL.scale₂ DL.base DL.length DL.leftWeight DL.rightWeight DL.slotWeight i)
        (fun h j => PR.normalizer *
          right.residualCoefficient (σ := σ) rightCharacters (-R.frequency h)
            DR.scale₁ DR.scale₂ DR.base DR.length DR.leftWeight DR.rightWeight DR.slotWeight j)
        x y exceptional := by
  apply R.common_atoms_hybrid_bound kernel (BL.atoms R.rows) (BR.atoms R.rows)
  · intro h _ i hi
    rw [BL.atoms_value R.rows (primePowerProduct R.primes R.leftMultiplicity) hcommonL h]
    exact left.identified_coefficient_residue_extract DL PL hL i hi (IL i) (hIL i hi)
      (R.frequency h)
  · intro h _ j hj
    rw [BR.atoms_value R.rows (primePowerProduct R.primes R.rightMultiplicity) hcommonR h]
    exact right.identified_coefficient_residue_extract DR PR hR j hj (IR j) (hIR j hj)
      (-R.frequency h)


/-- The actual centered source reaches the same reweighted common
rows before the exceptional predicate is split.  Neither rectangle is
bounded separately here. -/
theorem actual_common_atoms_centered_hybrid_bound
    (R : ActualSecondCorrelationRows A σ H ι) (kernel : 𝓢(V, ℂ))
    (left : SupportCartesianBranch S₁ S₂ S P)
    (right : SupportCartesianBranch T₁ T₂ Ts P)
    (leftCharacters : FixedChildCharacters F k)
    (rightCharacters : FixedChildCharacters F l)
    (phaseLeft phaseRight : Ray →* Circle)
    (DL : Bool → SecondCoefficientTermDictionary leftCharacters phaseLeft S₁ S₂ S)
    (DR : Bool → SecondCoefficientTermDictionary rightCharacters phaseRight T₁ T₂ Ts)
    (PL : Bool → SecondColumnFactors F Ray k)
    (PR : Bool → SecondColumnFactors F Ray l)
    (hL : ∀ r, (DL r).FactorIdentification (PL r))
    (hR : ∀ r, (DR r).FactorIdentification (PR r))
    (hsL : (DL true).base = (DL false).base ∧
      (DL true).length = (DL false).length ∧
      (DL true).slotWeight = (DL false).slotWeight)
    (hsR : (DR true).base = (DR false).base ∧
      (DR true).length = (DR false).length ∧
      (DR true).slotWeight = (DR false).slotWeight)
    (hnL : (PL true).leftNormalizer = (PL false).leftNormalizer ∧
      (PL true).rightNormalizer = (PL false).rightNormalizer ∧
      (PL true).slotNormalizer = (PL false).slotNormalizer)
    (hnR : (PR true).leftNormalizer = (PR false).leftNormalizer ∧
      (PR true).rightNormalizer = (PR false).rightNormalizer ∧
      (PR true).slotNormalizer = (PR false).slotNormalizer)
    (BL : left.CommonAtomBounds leftCharacters
      (DL false).base (DL false).length (DL false).slotWeight)
    (BR : right.CommonAtomBounds rightCharacters
      (DR false).base (DR false).length (DR false).slotWeight)
    (hcommonL : left.plainExtract₁ * left.plainExtract₂ * (∏ i, left.slotExtract i) =
      (primePowerProduct R.primes R.leftMultiplicity).val)
    (hcommonR : right.plainExtract₁ * right.plainExtract₂ * (∏ i, right.slotExtract i) =
      (primePowerProduct R.primes R.rightMultiplicity).val)
    (IL : AllocationColumn F left.keep.card → A.Exterior)
    (IR : AllocationColumn F right.keep.card → A.Exterior)
    (hIL : ∀ i ∈ left.residualColumns, (IL i).val = allocationColumnIdeal i)
    (hIR : ∀ i ∈ right.residualColumns, (IR i).val = allocationColumnIdeal i)
    (x : H → AllocationColumn F left.keep.card → V)
    (y : H → AllocationColumn F right.keep.card → V)
    (exceptional : H → Prop) :
    ‖jointKernelPairing kernel R.rows left.residualColumns right.residualColumns
      (fun h => R.weight h * R.correlation h)
      (fun h i =>
        ((PL false).coefficient (left.reconstruct i) *
            (phaseLeft ((PL false).ray (left.reconstruct i)) : ℂ) -
          (PL true).coefficient (left.reconstruct i) *
            (phaseLeft ((PL true).ray (left.reconstruct i)) : ℂ)) *
          σ (A.sexticResidue (IL i) (R.frequency h)))
      (fun h j =>
        ((PR false).coefficient (right.reconstruct j) *
            (phaseRight ((PR false).ray (right.reconstruct j)) : ℂ) -
          (PR true).coefficient (right.reconstruct j) *
            (phaseRight ((PR true).ray (right.reconstruct j)) : ℂ)) *
          σ (A.sexticResidue (IR j) (-R.frequency h))) x y‖ ≤
      jointHybridKernelCost kernel R.rows left.residualColumns right.residualColumns
        (fun h => (R.withCommonAtoms (BL.atoms R.rows) (BR.atoms R.rows)).weight h *
          R.correlation h)
        (fun h i => (PL false).normalizer *
          (left.residualCoefficient (σ := σ) leftCharacters (R.frequency h)
              (DL false).scale₁ (DL false).scale₂ (DL false).base (DL false).length
              (DL false).leftWeight (DL false).rightWeight (DL false).slotWeight i -
            left.residualCoefficient (σ := σ) leftCharacters (R.frequency h)
              (DL true).scale₁ (DL true).scale₂ (DL true).base (DL true).length
              (DL true).leftWeight (DL true).rightWeight (DL true).slotWeight i))
        (fun h j => (PR false).normalizer *
          (right.residualCoefficient (σ := σ) rightCharacters (-R.frequency h)
              (DR false).scale₁ (DR false).scale₂ (DR false).base (DR false).length
              (DR false).leftWeight (DR false).rightWeight (DR false).slotWeight j -
            right.residualCoefficient (σ := σ) rightCharacters (-R.frequency h)
              (DR true).scale₁ (DR true).scale₂ (DR true).base (DR true).length
              (DR true).leftWeight (DR true).rightWeight (DR true).slotWeight j))
        x y exceptional := by
  apply R.common_atoms_hybrid_bound kernel (BL.atoms R.rows) (BR.atoms R.rows)
  · intro h _ i hi
    rw [BL.atoms_value R.rows (primePowerProduct R.primes R.leftMultiplicity) hcommonL h]
    exact left.identified_centered_residue_extract (DL false) (DL true) (PL false) (PL true)
      (hL false) (hL true) hsL.1 hsL.2.1 hsL.2.2 hnL.1 hnL.2.1 hnL.2.2
      i hi (IL i) (hIL i hi) (R.frequency h)
  · intro h _ j hj
    rw [BR.atoms_value R.rows (primePowerProduct R.primes R.rightMultiplicity) hcommonR h]
    exact right.identified_centered_residue_extract (DR false) (DR true) (PR false) (PR true)
      (hR false) (hR true) hsR.1 hsR.2.1 hsR.2.2 hnR.1 hnR.2.1 hnR.2.2
      j hj (IR j) (hIR j hj) (-R.frequency h)

end CoupledSource

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SourceCartesianAtlas.common_atoms_ideal
#print axioms HeckeSkeleton.Moments.EngineStep.actual_common_atoms_identified_hybrid_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_common_atoms_centered_hybrid_bound

