import HeckeSkeleton.Moments.MOM_INV_STEP.SexticEvenness
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualPacketEnergy

/-!
# The second inverse coefficient returns to the literal child column

An actual coprime factorization of the inverse source n=L·u leaves the
frozen scalar μ(L)ν(L). The fifth-digit finite Gauss factor changes the
remaining μ(u)ν(u) into the original a₀(u) with the genuine background
νG⁻¹. The original puncture, sector row, fourth-power label, surviving
marks and cutoff are copied unchanged into the actual canonical child.

The scalar is independent of the child row and averaged label. No
reconstruction equality, finite Gauss CRT formula or energy inequality
is an input of this coefficient conversion.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalInverseCalibration

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers FixedTripleEnergy CanonicalChildren ActualPacketEnergy
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- The actual common factor is extracted by multiplicativity of μ
and the same live Hecke character. The remaining coefficient uses the
fifth Gauss digit of the inverse source, not a renamed first transform. -/
theorem second_source_coefficient {Λ G : HeckeCharacter K}
    (hcal : ThetaCalibrationInput K S D Λ G) (ν : HeckeCharacter K)
    (L u : ExteriorIdeal K S) (hcop : IsCoprime L.val.val u.val.val)
    (hu : Squarefree u.val.val) :
    (moebius (exteriorMul K S L u).val.val : ℂ) *
        heckeIdealCoefficient K ν (exteriorMul K S L u).val *
        thetaGamma K S D u 5 =
      ((moebius L.val.val : ℂ) * heckeIdealCoefficient K ν L.val) *
        (CoefficientCycle.canonicalCoefficient K S D Λ u *
          heckeIdealCoefficient K (ν * G⁻¹) u.val) := by
  change (moebius (L.val.val * u.val.val) : ℂ) *
    heckeIdealCoefficient K ν (L.val * u.val) * thetaGamma K S D u 5 = _
  rw [hcop.isRelPrime.moebius_mul, Int.cast_mul, heckeIdealCoefficient_mul,
    SexticEvenness.thetaGamma_five_eq_conj]
  calc
    _ = ((moebius L.val.val : ℂ) * heckeIdealCoefficient K ν L.val) *
      ((moebius u.val.val : ℂ) * heckeIdealCoefficient K ν u.val *
        conj (thetaGamma K S D u 1)) := by ring
    _ = _ := by rw [BackgroundCycle.second_cycle_single_background K S D hcal ν u hu]

/-- This outer scalar has no moving-column, row or averaged-label
argument. On the actual squarefree common factor its norm is one. -/
theorem second_outer_scalar_norm (ν : HeckeCharacter K)
    (hν : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K ν p)
    (L : ExteriorIdeal K S) (hL : Squarefree L.val.val) :
    ‖(moebius L.val.val : ℂ) * heckeIdealCoefficient K ν L.val‖ = 1 := by
  rw [norm_mul, CoefficientCycle.squarefree_moebius_norm K S L hL,
    CoefficientCycle.exterior_heckeCoefficient_norm K S ν hν L, one_mul]

variable {σ Sector : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

/-- The actual second child has the same fixed family data and the
background νG⁻¹. Its admissibility follows in the original two classes. -/
def inverseChildFamily (C : ColumnFamily K S σ Θ ψ)
    (G : HeckeCharacter K) (hG : G ∈ Θ) : ColumnFamily K S σ Θ ψ :=
  { C with
    background := fun γ => C.background γ * G⁻¹
    background_admissible := fun γ => BackgroundCycle.admissible_mul_inv
      K Θ ψ (C.background γ) G (C.background_admissible γ) hG }

/-- The literal finite inverse column after its second primitive
transform. L is the common source factor, and every other factor is the
same concrete mark, puncture, label, sector and norm test as the child. -/
def inverseColumnSummand (C : ColumnFamily K S σ Θ ψ)
    (sectorUnit : Sector → S.unit K) (L : ExteriorIdeal K S)
    (c : SecondChild K Sector) (u : ExteriorIdeal K S) : ℂ :=
  ((moebius (exteriorMul K S L u).val.val : ℂ) *
    heckeIdealCoefficient K (C.background c.1) (exteriorMul K S L u).val *
    thetaGamma K S D u 5) *
    (if IsCoprime u.val.val (childPuncture C.originalPuncture c.1) then 1 else 0) *
    sectorRow K S D sectorUnit u c.2.2 * labelRow K S D u c.2.1 ^ 4 *
    divisorMark (C.survivors c.1) C.primeLists C.primeWeights u.val.val *
    C.cutoff c.1 ((u.val.val.absNorm : ℝ) / C.base ^ C.columnLength c.1)

/-- Pointwise equality with the exact column summand used by
`ActualPacketEnergy.literal_child_energy`. It retains every zero of the
original ideal characters and every original prime-mark coefficient. -/
theorem inverseColumnSummand_eq_child (C : ColumnFamily K S σ Θ ψ)
    {G : HeckeCharacter K} (hG : G ∈ Θ)
    (hcal : ThetaCalibrationInput K S D C.lambda G)
    (sectorUnit : Sector → S.unit K) (L : ExteriorIdeal K S)
    (c : SecondChild K Sector) (u : ExteriorIdeal K S)
    (hu : u ∈ C.columns c.1) (hcop : IsCoprime L.val.val u.val.val) :
    inverseColumnSummand K S D C sectorUnit L c u =
      ((moebius L.val.val : ℂ) * heckeIdealCoefficient K (C.background c.1) L.val) *
        columnSummand K S D (inverseChildFamily K S C G hG) sectorUnit c u := by
  dsimp only [inverseColumnSummand, columnSummand, inverseChildFamily]
  rw [second_source_coefficient K S D hcal (C.background c.1) L u hcop
    (C.columns_squarefree c.1 u hu)]
  ring

/-- The whole actual finite inverse column is the frozen common-factor
scalar times the literal canonical child value. This is a proved finite
sum identity, with no arbitrary residual coefficient on u. -/
theorem inverseColumn_eq_child (C : ColumnFamily K S σ Θ ψ)
    {G : HeckeCharacter K} (hG : G ∈ Θ)
    (hcal : ThetaCalibrationInput K S D C.lambda G)
    (sectorUnit : Sector → S.unit K) (L : ExteriorIdeal K S)
    (c : SecondChild K Sector)
    (hcop : ∀ u ∈ C.columns c.1, IsCoprime L.val.val u.val.val) :
    (∑ u ∈ C.columns c.1, inverseColumnSummand K S D C sectorUnit L c u) =
      ((moebius L.val.val : ℂ) * heckeIdealCoefficient K (C.background c.1) L.val) *
        childValue K S D (inverseChildFamily K S C G hG) sectorUnit c := by
  rw [childValue_eq_sum, Finset.mul_sum]
  change (∑ u ∈ C.columns c.1, inverseColumnSummand K S D C sectorUnit L c u) =
    ∑ u ∈ C.columns c.1,
      ((moebius L.val.val : ℂ) * heckeIdealCoefficient K (C.background c.1) L.val) *
        columnSummand K S D (inverseChildFamily K S C G hG) sectorUnit c u
  apply Finset.sum_congr rfl
  intro u hu
  exact inverseColumnSummand_eq_child K S D C hG hcal sectorUnit L c u hu (hcop u hu)

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalInverseCalibration

end
