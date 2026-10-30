import HeckeGeneral.Analysis.ActualMomentPolynomialBridges

/-!
Independent inverse and paired plain tests on the same complete-ideal row.
This is a data constructor and literal finite-sum identification only.
It does not construct detector witnesses, identify their exceptional rows,
instantiate canonical admissibility, or assert any moment inequality.

The arithmetic premise remains the existing RowCharacterInput. Its common
fixed-S/6 and complete-ideal coprimality mask, unit sector, row character,
row enumeration, slot geometry and slot coefficients are preserved.

Native checking and whole-library audit status are recorded separately.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.SquarefreeAmplification HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)

/-- V, W₁ and W₂ are independent actual IdealTests, each retaining its own
exact finite support. No change is made to the arithmetic row or its mask. -/
abbrev decomposedWitnessMomentData (ω η : HeckeCharacter K)
    (ξ : SixthUnitClasses K S) (V W₁ W₂ : IdealTest K) (g : SlotGeometry K) :
    MomentData K ω η :=
  { decomposedMomentDataWithSlots K S P R ω η ξ V g with
    plainTest₁ := W₁
    plainTest₂ := W₂ }

theorem decomposedWitnessMomentData_rowCharacter (ω η : HeckeCharacter K)
    (ξ : SixthUnitClasses K S) (V W₁ W₂ : IdealTest K) (g : SlotGeometry K) :
    (decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g).rowCharacter =
      completeIdealRowCharacter K S P R ξ := rfl

theorem decomposedWitnessMomentData_commonMask (ω η : HeckeCharacter K)
    (ξ : SixthUnitClasses K S) (V W₁ W₂ : IdealTest K) (g : SlotGeometry K) :
    (decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g).commonMask =
      completeIdealCommonMask K S := rfl

theorem decomposedWitnessMomentData_rows (ω η : HeckeCharacter K)
    (ξ : SixthUnitClasses K S) (V W₁ W₂ : IdealTest K) (g : SlotGeometry K) :
    (decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g).rows =
      completeExteriorIdealRows K S := rfl

theorem inversePolynomial_decomposedWitnessMomentData
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (V W₁ W₂ : IdealTest K) (g : SlotGeometry K)
    (I : ExteriorIdeal K S) (D t : ℝ) :
    inversePolynomial (decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g)
      I.val D t =
      sIntegerSexticInverseIdealPolynomial K S P.arithmetic.root6
        P.arithmetic.primitive6 P.arithmetic.embedding η (V.support I.val t D)
        (decomposedIdealSectorOrbit K S P (I, ξ)).out.val D (V.profile I.val t) :=
  inversePolynomial_decomposedMomentDataWithSlots K S P R ω η ξ V g I D t

/-- An arbitrary plain test is independent of the chosen inverse test V. -/
theorem plainPolynomial_decomposedWitnessMomentData
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (V W₁ W₂ W : IdealTest K) (g : SlotGeometry K)
    (I : ExteriorIdeal K S) (N t : ℝ) :
    plainPolynomial (decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g)
      W I.val N t = actualDecomposedPlainPolynomial K S P ξ W I N t :=
  plainPolynomial_decomposedMomentDataWithSlots K S P R ω η ξ V W g I N t

/-- The two stored plain tests have independent supports, scales and heights. -/
theorem pairedPlainPolynomials_decomposedWitnessMomentData
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (V W₁ W₂ : IdealTest K) (g : SlotGeometry K)
    (I : ExteriorIdeal K S) (N₁ N₂ t₁ t₂ : ℝ) :
    let d := decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g
    plainPolynomial d d.plainTest₁ I.val N₁ t₁ *
        plainPolynomial d d.plainTest₂ I.val N₂ t₂ =
      actualDecomposedPlainPolynomial K S P ξ W₁ I N₁ t₁ *
        actualDecomposedPlainPolynomial K S P ξ W₂ I N₂ t₂ :=
  congrArg₂ (fun x y : ℂ => x * y)
    (plainPolynomial_decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ W₁ g I N₁ t₁)
    (plainPolynomial_decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ W₂ g I N₂ t₂)

/-- Selecting slots only changes the geometry. In particular it leaves
both stored plain tests, V, the complete row mask and the sector unchanged. -/
theorem decomposedWitnessMomentData_restrictSlots
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (V W₁ W₂ : IdealTest K) (g : SlotGeometry K)
    (J : Finset (Fin g.slotCount)) :
    (decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g).restrictSlots J =
      decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ (g.restrictSlots J) := rfl

theorem inversePolynomial_decomposedWitnessMomentData_restrictSlots
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (V W₁ W₂ : IdealTest K) (g : SlotGeometry K)
    (J : Finset (Fin g.slotCount)) (I : ExteriorIdeal K S) (D t : ℝ) :
    inversePolynomial
      ((decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g).restrictSlots J) I.val D t =
      sIntegerSexticInverseIdealPolynomial K S P.arithmetic.root6
        P.arithmetic.primitive6 P.arithmetic.embedding η (V.support I.val t D)
        (decomposedIdealSectorOrbit K S P (I, ξ)).out.val D (V.profile I.val t) :=
  (inversePolynomial_restrictSlots
    (decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g) J I.val D t).trans
      (inversePolynomial_decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g I D t)

theorem plainPolynomial_decomposedWitnessMomentData_restrictSlots
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (V W₁ W₂ W : IdealTest K) (g : SlotGeometry K)
    (J : Finset (Fin g.slotCount)) (I : ExteriorIdeal K S) (N t : ℝ) :
    plainPolynomial
      ((decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g).restrictSlots J)
      W I.val N t = actualDecomposedPlainPolynomial K S P ξ W I N t :=
  (plainPolynomial_restrictSlots
    (decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ g) J W I.val N t).trans
      (plainPolynomial_decomposedWitnessMomentData K S P R ω η ξ V W₁ W₂ W g I N t)

end HeckeGeneral.ThetaSkeleton.Physical
