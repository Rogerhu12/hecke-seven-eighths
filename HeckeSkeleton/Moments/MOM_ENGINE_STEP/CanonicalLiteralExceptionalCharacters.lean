import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPaidRowCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocatedSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalThetaPartition

/-!
# The actual exceptional ideal character and its complete mask

The finite catalogue uses only the original theta set and the three
original plain backgrounds.  Each actual theta class selects its literal
character in that catalogue.  Both plain factors use this same entry.

The one-ideal source identity is deduced from the original appended
phase calibration.  Its mask is exactly the fixed bad-prime ideal times
the actual residual ideal times the full moving/remaining support.
The sixth root, including primes with zero active exponent, is retained.
Negative frequency has the same arithmetic identity; conjugation acts
on the entire coefficient, without an inverse-closure assumption on theta.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharacters

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open CanonicalOriginalPhaseCalibration

variable {K : Type} [Field K] [NumberField K]

/-- A finite index for the original choices `1`, `psi`, and `psi^-1`. -/
def background (ψ : HeckeCharacter K) : Option Bool → HeckeCharacter K
  | none => 1
  | some false => ψ
  | some true => ψ⁻¹

variable {ω ψ : HeckeCharacter K}

def backgroundIndex (parent : MomentData K ω ψ) : Option Bool :=
  if parent.plainBackground = 1 then none
  else if parent.plainBackground = ψ then some false else some true

theorem backgroundIndex_spec (parent : MomentData K ω ψ) :
    background ψ (backgroundIndex parent) = parent.plainBackground := by
  unfold backgroundIndex
  split_ifs with h₁ h₂
  · exact h₁.symm
  · exact h₂.symm
  · rcases parent.plain_background_spec with h | h | h
    · exact (h₁ h).elim
    · exact (h₂ h).elim
    · exact h.symm

/-- The real Euler coefficient, zero extended at the zero ideal. -/
def inducing (background θ : HeckeCharacter K) : Ideal (𝓞 K) →* ℂ :=
  (idealCoefficientHom (primeCoefficient K (background * θ))).toMonoidHom

@[simp] theorem inducing_apply (background θ : HeckeCharacter K)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    inducing background θ I.val = heckeIdealCoefficient K (background * θ) I := rfl

@[simp] theorem inducing_zero (background θ : HeckeCharacter K) :
    inducing background θ (⊥ : Ideal (𝓞 K)) = 0 :=
  idealCoefficient_zero _

theorem inducing_norm_le_one (background θ : HeckeCharacter K) (I : Ideal (𝓞 K)) :
    ‖inducing background θ I‖ ≤ 1 :=
  norm_idealCoefficient_le_one _ (norm_primeCoefficient_le_one K _) I

abbrev CatalogueIndex (theta : Finset (HeckeCharacter K)) := Option Bool × theta

/-- This family is fixed before any row, scale, extraction or Fourier mode. -/
def catalogue (ψ : HeckeCharacter K) (theta : Finset (HeckeCharacter K))
    (i : CatalogueIndex theta) : Ideal (𝓞 K) →* ℂ :=
  inducing (background ψ i.1) i.2.val

theorem catalogue_card (theta : Finset (HeckeCharacter K)) :
    Fintype.card (CatalogueIndex theta) = 3 * theta.card := by
  simp [CatalogueIndex]

def selectedIndex (parent : MomentData K ω ψ) (θ : parent.theta) :
    CatalogueIndex parent.theta := (backgroundIndex parent, θ)

@[simp] theorem catalogue_selected (parent : MomentData K ω ψ) (θ : parent.theta) :
    catalogue ψ parent.theta (selectedIndex parent θ) =
      inducing parent.plainBackground θ.val := by
  simp only [catalogue, selectedIndex, backgroundIndex_spec]

section CompleteMask

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- The exact complete mask, with the additional support charged only once. -/
def completeMask (moving : OriginalMovingFactors A P R)
    (remaining u : HeckeGeneral.Analysis.NonzeroIdeal K) : Ideal (𝓞 K) :=
  A.cS * u.val * (moving.fullMaskSupport remaining).val

theorem completeMask_ne_zero (moving : OriginalMovingFactors A P R)
    (remaining u : HeckeGeneral.Analysis.NonzeroIdeal K) : completeMask moving remaining u ≠ 0 :=
  mul_ne_zero (mul_ne_zero A.cS_ne_zero (nonZeroDivisors.coe_ne_zero u))
    (nonZeroDivisors.coe_ne_zero (moving.fullMaskSupport remaining))

theorem completeMask_coprime (moving : OriginalMovingFactors A P R)
    (remaining u I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    IsCoprime I.val (completeMask moving remaining u) ↔
      (IsCoprime I.val A.cS ∧ IsCoprime I.val u.val) ∧
        (IsCoprime I.val moving.support.val ∧ IsCoprime I.val remaining.val) := by
  rw [completeMask, IsCoprime.mul_right_iff, IsCoprime.mul_right_iff,
    moving.fullMaskSupport_coprime_iff]

theorem completeMask_norm (moving : OriginalMovingFactors A P R)
    (remaining u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (Ideal.absNorm (completeMask moving remaining u) : ℝ) =
      (Ideal.absNorm A.cS : ℝ) *
        (idealNorm K u * idealNorm K (moving.fullMaskSupport remaining)) := by
  change (Ideal.absNorm (completeMask moving remaining u) : ℝ) =
    (Ideal.absNorm A.cS : ℝ) *
      ((Ideal.absNorm u.val : ℝ) *
        (Ideal.absNorm (moving.fullMaskSupport remaining).val : ℝ))
  simp only [completeMask, map_mul, Nat.cast_mul]
  ring

/-- The already paid complete row budget is precisely the variable
part of this exceptional mask's norm. -/
theorem completeMask_norm_le (moving : OriginalMovingFactors A P R)
    (remaining u : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
    (hbudget : idealNorm K u * idealNorm K (moving.fullMaskSupport remaining) ≤ budget) :
    (Ideal.absNorm (completeMask moving remaining u) : ℝ) ≤
      (Ideal.absNorm A.cS : ℝ) * budget := by
  rw [completeMask_norm]
  exact mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)

theorem data_mask (parent : MomentData K ω ψ) (moving : OriginalMovingFactors A P R)
    (correction : HeckeCharacter K) (hcorr : correction = 1 ∨ correction ∈ parent.theta)
    (sector : HeckeGeneral.Analysis.NonzeroIdeal K → SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
    (inverse left right : IdealTest K) (geometry : SlotGeometry K)
    (index : Fin geometry.slotCount → Fin parent.geometry.slotCount)
    (u I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    maskValue (CanonicalOriginalChildData.data parent moving correction hcorr sector
      remaining budget inverse left right geometry index) u I.val =
        if IsCoprime I.val (completeMask moving remaining u) then (1 : ℂ) else 0 := by
  change (if ((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I.val &&
      decide (IsCoprime I.val moving.support.val)) &&
      decide (IsCoprime I.val remaining.val)) then (1 : ℂ) else 0) = _
  simp only [completeIdealCommonMask, Bool.and_eq_true, decide_eq_true_eq]
  congr 1
  apply propext
  rw [completeMask_coprime]
  change ((sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I ∧
    IsCoprime I.val u.val) ∧ IsCoprime I.val moving.support.val) ∧
    IsCoprime I.val remaining.val ↔ _
  rw [outside_iff_coprime I]
  tauto

end CompleteMask

section LiteralMask

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (oldMoving : OriginalMovingFactors A P R)
variable (C : A.GeneralArithmeticContext σ η hS)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool)

/-- The complete original literal mask after the second actual factorization. -/
def rowMask (remaining u : HeckeGeneral.Analysis.NonzeroIdeal K) : Ideal (𝓞 K) :=
  completeMask ((F.moving P R oldMoving).appendSecondFactor C p m n pattern)
    (remainingMaskIdeal A remaining * exteriorMomentIdeal (secondSixthRootIdeal p m n)) u

theorem rowMask_ne_zero (remaining u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    rowMask P R F oldMoving C p m n pattern remaining u ≠ 0 :=
  completeMask_ne_zero _ _ _

/-- Coprimality to the displayed complete mask recovers all original
deletions, including the raw remaining ideal behind the fixed-S gate. -/
theorem rowMask_consequences (remaining u I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : IsCoprime I.val (rowMask P R F oldMoving C p m n pattern remaining u)) :
    CanonicalLiteralMaskSupport.MaskConsequences (F.moving P R oldMoving)
      remaining p m n pattern u I := by
  have H := (completeMask_coprime
    ((F.moving P R oldMoving).appendSecondFactor C p m n pattern)
    (remainingMaskIdeal A remaining * exteriorMomentIdeal (secondSixthRootIdeal p m n))
    u I).mp hI
  have hmove := ((F.moving P R oldMoving).appendFactors_support_coprime_iff
    (secondOriginalMovingFactors P R C p m n pattern) I.val).mp H.2.1
  have hremaining : IsCoprime I.val remaining.val :=
    (remainingMaskRadical_coprime_iff A remaining I.val H.1.1).mpr
      H.2.2.of_mul_right_left
  have hactive : IsCoprime I.val (secondActiveFrequencyIdeal p m n pattern).val := by
    have h := ((secondOriginalMovingFactors P R C p m n pattern).coprime_support_iff_fullIdeal
      I.val).mp hmove.2
    have he : (secondOriginalMovingFactors P R C p m n pattern).fullIdeal =
        secondActiveFrequencyIdeal p m n pattern :=
      OriginalMovingFactors.singleton_fullIdeal (secondActiveFrequencyIdeal p m n pattern)
        (secondActiveFrequencyGenerator C p m n pattern)
        (secondActiveFrequencyGenerator_generates C p m n pattern) 1
    simpa only [he] using h
  exact ⟨H.1.1, H.1.2, hmove.1, hremaining, hactive, H.2.2.of_mul_right_right⟩

/-- The actual first deletion and positive common multiplicities imply
the support table's original exclusions. No support oracle is supplied. -/
theorem rowMask_avoids_original
    (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (firstSupport : Finset (Ideal (𝓞 K)))
    (hfirst : ∀ q ∈ firstSupport, Prime q)
    (hextra : extra = literalDeletionIdeal firstSupport hfirst)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (u I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : IsCoprime I.val
      (rowMask P R F oldMoving C p m n pattern (remaining * extra) u)) :
    CanonicalLiteralSupport.Avoids I.val ((primeSupport A.cS ∪ firstSupport) ∪
      primeSupport (primePowerProduct p m).val) := by
  apply CanonicalLiteralAllocatedSupport.avoids_of_maskConsequences
    (rowMask_consequences P R F oldMoving C p m n pattern (remaining * extra) u I hI)
    firstSupport (primeSupport (primePowerProduct p m).val) _ (fun _ h => h) hm hn
  intro q hq
  rw [hextra]
  exact CanonicalLiteralAllocatedSupport.dvd_literalDeletionIdeal firstSupport hfirst q hq

end LiteralMask

section ActualRows

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (C : A.GeneralArithmeticContext σ η hS)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (S : ActualSecondCorrelationRows A σ H ι) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) {k : ℕ}
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (row : CanonicalOriginalPhaseCalibration.PatternSector P S C pattern ν)
variable (θ : parent.theta)
variable (hθ : S.literalCharacter C P R F oldMoving correction pattern ν row.val.val.val = θ.val)

/-- An exceptional original row selects its own finite catalogue entry;
no inducing character is chosen independently of that row. -/
def rowIndex (he : S.literalCharacter C P R F oldMoving correction pattern ν
    row.val.val.val ∈ parent.theta) : CatalogueIndex parent.theta :=
  selectedIndex parent ⟨S.literalCharacter C P R F oldMoving correction pattern ν
    row.val.val.val, he⟩

include hcorr hone hroot hemb hθ

/-- The actual exceptional class fixes the one ideal character on
both plain factors. The existing raw constructor is used only through
its arithmetic fields, which are independent of profiles and budget. -/
theorem actual_plain (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    let T := CanonicalLiteralPhaseCalibration.sourceCharacters P R F parent oldMoving
      correction remaining extra index
    sourcePlainCoefficient T.plain T.plainTwist T.mask I *
        actualIdealResidue (A := A) (σ := σ) I.val
          (S.factor C row.val.val.val * (S.extractedRow C row.val.val).element) =
      (if IsCoprime I.val (rowMask P R F oldMoving C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern (remaining * extra)
          (S.extractedRow C row.val.val).momentIdeal) then (1 : ℂ) else 0) *
        catalogue ψ parent.theta (selectedIndex parent θ) I.val := by
  let d := CanonicalAppendedPhaseCalibration.childData P R parent (F.moving P R oldMoving)
    correction hcorr C S.primes S.leftMultiplicity S.rightMultiplicity pattern ν
    (remaining * extra) 1 parent.inverseTest parent.plainTest₁ parent.plainTest₂
    parent.geometry id
  have hcal := CanonicalLiteralPhaseCalibration.actualCalibration P R F parent oldMoving
    correction hcorr C pattern ν remaining extra 1 parent.inverseTest parent.plainTest₁
    parent.plainTest₂ parent.geometry id S hone hroot hemb row
  have hchar : d.rowCharacter (S.extractedRow C row.val.val).momentIdeal = θ.val := by
    change CanonicalLiteralAllocatedData.rowCharacter P R F oldMoving correction C
      S.primes S.leftMultiplicity S.rightMultiplicity pattern ν
        (S.extractedRow C row.val.val).momentIdeal = _
    simpa only [ActualSecondCorrelationRows.literalCharacter,
      dif_pos row.val.val.property] using hθ
  have hm := data_mask parent
    ((F.moving P R oldMoving).appendSecondFactor C S.primes
      S.leftMultiplicity S.rightMultiplicity pattern)
    correction (Or.inr hcorr) (fun _ => ν)
    (remainingMaskIdeal A (remaining * extra) *
      exteriorMomentIdeal (secondSixthRootIdeal S.primes S.leftMultiplicity S.rightMultiplicity))
    1 parent.inverseTest parent.plainTest₁ parent.plainTest₂ parent.geometry id
    (S.extractedRow C row.val.val).momentIdeal I
  have he := hcal.plain I
  change heckeIdealCoefficient K (parent.plainBackground *
    d.rowCharacter (S.extractedRow C row.val.val).momentIdeal) I *
    maskValue d (S.extractedRow C row.val.val).momentIdeal I.val = _ at he
  rw [hchar, hm] at he
  dsimp only
  rw [actualIdealResidue_frequency_mul, ← mul_assoc]
  rw [catalogue_selected, inducing_apply]
  exact he.symm.trans (mul_comm _ _)

/-- The right frame changes only the sign of the full frequency.
It does not invert the selected theta character. -/
theorem actual_negative_plain (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    let T := CanonicalLiteralPhaseCalibration.sourceCharacters P R F parent oldMoving
      correction remaining extra index
    sourcePlainCoefficient T.plain T.plainTwist T.mask I *
        actualIdealResidue (A := A) (σ := σ) I.val
          ((-S.factor C row.val.val.val) * (S.extractedRow C row.val.val).element) =
      (if IsCoprime I.val (rowMask P R F oldMoving C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern (remaining * extra)
          (S.extractedRow C row.val.val).momentIdeal) then (1 : ℂ) else 0) *
        catalogue ψ parent.theta (selectedIndex parent θ) I.val := by
  dsimp only
  rw [neg_mul, residue_neg]
  exact actual_plain P R F parent oldMoving correction hcorr C S pattern ν remaining extra
    index hone hroot hemb row θ hθ I

/-- The paid source has the same inducing character and the exact
smaller complete mask; the passive deletion remains a separate factor. -/
theorem actual_paid_plain (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    let T := CanonicalLiteralPaidCharacters.paidSourceCharacters P R F parent oldMoving
      correction remaining index
    sourcePlainCoefficient T.plain T.plainTwist T.mask I *
        actualIdealResidue (A := A) (σ := σ) I.val
          (S.factor C row.val.val.val * (S.extractedRow C row.val.val).element) =
      (if IsCoprime I.val (rowMask P R F oldMoving C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern remaining
          (S.extractedRow C row.val.val).momentIdeal) then (1 : ℂ) else 0) *
        catalogue ψ parent.theta (selectedIndex parent θ) I.val := by
  have he := actual_plain P R F parent oldMoving correction hcorr C S pattern ν remaining 1
    index hone hroot hemb row θ hθ I
  by_cases hI : IsCoprime I.val A.cS
  · have hc := CanonicalLiteralPaidCharacters.source_plain_delete
      P R F parent oldMoving correction remaining 1 index I hI
    simp only [CanonicalLiteralPaidCharacters.coprimeMask_one, mul_one] at hc
    simpa only [hc, mul_one] using he
  · have hz : actualIdealResidue (A := A) (σ := σ) I.val
        (S.factor C row.val.val.val * (S.extractedRow C row.val.val).element) = 0 :=
      dif_neg (fun h => hI h.2)
    have hn : ¬ IsCoprime I.val (rowMask P R F oldMoving C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern remaining
          (S.extractedRow C row.val.val).momentIdeal) := by
      intro h
      exact hI (rowMask_consequences P R F oldMoving C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern remaining _ I h).fixed
    simp only [hz, mul_zero, if_neg hn, zero_mul]

theorem actual_negative_paid_plain (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    let T := CanonicalLiteralPaidCharacters.paidSourceCharacters P R F parent oldMoving
      correction remaining index
    sourcePlainCoefficient T.plain T.plainTwist T.mask I *
        actualIdealResidue (A := A) (σ := σ) I.val
          ((-S.factor C row.val.val.val) * (S.extractedRow C row.val.val).element) =
      (if IsCoprime I.val (rowMask P R F oldMoving C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern remaining
          (S.extractedRow C row.val.val).momentIdeal) then (1 : ℂ) else 0) *
        catalogue ψ parent.theta (selectedIndex parent θ) I.val := by
  dsimp only
  rw [neg_mul, residue_neg]
  exact actual_paid_plain P R F parent oldMoving correction hcorr C S pattern ν remaining
    index hone hroot hemb row θ hθ I

/-- The reduced amplifier character equals the original one by the
actual sixth-power orbit identity. Its smaller mask is kept literal. -/
theorem actual_reduced_paid_plain (q : ExteriorPrime A) (e : AmplifierValuation)
    (hpool : F.poolElement = generator C q ^ (2 * e.multiplicity)) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    let Fred := CanonicalLiteralPaidCharacters.reducedPhases F C q e
    let T := CanonicalLiteralPaidCharacters.paidSourceCharacters P R Fred parent oldMoving
      correction remaining index
    sourcePlainCoefficient T.plain T.plainTwist T.mask I *
        actualIdealResidue (A := A) (σ := σ) I.val
          (S.factor C row.val.val.val * (S.extractedRow C row.val.val).element) =
      (if IsCoprime I.val (rowMask P R Fred oldMoving C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern remaining
          (S.extractedRow C row.val.val).momentIdeal) then (1 : ℂ) else 0) *
        catalogue ψ parent.theta (selectedIndex parent θ) I.val := by
  have hθ' : S.literalCharacter C P R
      (CanonicalLiteralPaidCharacters.reducedPhases F C q e)
      oldMoving correction pattern ν row.val.val.val = θ.val :=
    (CanonicalLiteralPaidRowCharacters.literalCharacter_eq P R S F C q e hpool
      oldMoving correction pattern ν row.val.val.val).symm.trans hθ
  exact actual_paid_plain P R (CanonicalLiteralPaidCharacters.reducedPhases F C q e)
    parent oldMoving correction hcorr C S pattern ν remaining index hone hroot hemb row θ hθ' I

omit hθ in
/-- Membership in the actual exceptional predicate is enough: its
literal row character supplies the finite catalogue index internally. -/
theorem actual_plain_of_exceptional
    (he : S.literalCharacter C P R F oldMoving correction pattern ν
      row.val.val.val ∈ parent.theta) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    let T := CanonicalLiteralPhaseCalibration.sourceCharacters P R F parent oldMoving
      correction remaining extra index
    sourcePlainCoefficient T.plain T.plainTwist T.mask I *
        actualIdealResidue (A := A) (σ := σ) I.val
          (S.factor C row.val.val.val * (S.extractedRow C row.val.val).element) =
      (if IsCoprime I.val (rowMask P R F oldMoving C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern (remaining * extra)
          (S.extractedRow C row.val.val).momentIdeal) then (1 : ℂ) else 0) *
        catalogue ψ parent.theta
          (rowIndex P R F parent oldMoving correction C S pattern ν row he) I.val :=
  actual_plain P R F parent oldMoving correction hcorr C S pattern ν remaining extra index
    hone hroot hemb row
    ⟨S.literalCharacter C P R F oldMoving correction pattern ν row.val.val.val, he⟩ rfl I

end ActualRows

/-- Whole conjugation retains the same finite catalogue entry.
There is no inverse-closure requirement on the original theta set. -/
theorem star_masked_inducing (Ψ : Ideal (𝓞 K) →* ℂ)
    (mask I : Ideal (𝓞 K)) :
    star ((if IsCoprime I mask then (1 : ℂ) else 0) * Ψ I) =
      (if IsCoprime I mask then (1 : ℂ) else 0) * star (Ψ I) := by
  by_cases h : IsCoprime I mask <;> simp only [h, if_true, if_false,
    one_mul, zero_mul, star_zero]

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharacters

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharacters.backgroundIndex_spec
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharacters.data_mask
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharacters.rowMask_avoids_original
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharacters.actual_plain
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharacters.actual_negative_plain
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharacters.actual_paid_plain
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharacters.actual_reduced_paid_plain
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharacters.actual_plain_of_exceptional
