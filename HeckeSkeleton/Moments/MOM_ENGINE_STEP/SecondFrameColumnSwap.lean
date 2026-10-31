import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCorrelationColumnSwap
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondBranchProduction

/-!
# The original second frames with their two roles exchanged

The right phase convention already contains an inverse. Exchanging its
role with the left therefore uses the inverse of the original phase
character composed with the product swap. The original single-factor
dictionary, all profiles, allocation, retained slots and Gauss scales
are preserved. Only the dictionary's phase proof is transported.

The complete joint locations are negated. Together with the actual
frequency negation, the new complete column coefficient is the star of
the old one. This is precisely the symmetry of its norm, at the same
Fourier parameter, needed for a terminal estimate on either side.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

def swappedSecondPhase (Ray : Type*) [CommGroup Ray]
    (χ : (Ray × Ray) →* Circle) : (Ray × Ray) →* Circle :=
  (χ.comp (MulEquiv.prodComm Ray Ray).toMonoidHom)⁻¹

@[simp] theorem fixedLeftPhase_swappedSecondPhase
    (Ray : Type*) [CommGroup Ray] [Fintype Ray] (χ : (Ray × Ray) →* Circle) :
    fixedLeftPhase Ray (swappedSecondPhase Ray χ) = fixedRightPhase Ray χ := by
  ext x
  rfl

@[simp] theorem fixedRightPhase_swappedSecondPhase
    (Ray : Type*) [CommGroup Ray] [Fintype Ray] (χ : (Ray × Ray) →* Circle) :
    fixedRightPhase Ray (swappedSecondPhase Ray χ) = fixedLeftPhase Ray χ := by
  ext x
  change ((χ (x, 1))⁻¹)⁻¹ = χ (x, 1)
  exact inv_inv _

variable {K : Type} [Field K] [NumberField K]

namespace SecondCoefficientTermDictionary

variable {k : ℕ} {Ray : Type*} [CommGroup Ray]
variable {T : FixedChildCharacters K k} {phase : Ray →* Circle}
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable (D : SecondCoefficientTermDictionary T phase S₁ S₂ S)

/-- Reexpress the same original atoms under an equal phase map. No
atom, scale, ray, profile or occurrence is selected again. -/
def rephase (phase' : Ray →* Circle) (hphase : phase' = phase) :
    SecondCoefficientTermDictionary T phase' S₁ S₂ S where
  leftAtom := D.leftAtom
  rightAtom := D.rightAtom
  slotAtom := D.slotAtom
  leftRay := D.leftRay
  rightRay := D.rightRay
  slotRay := D.slotRay
  scale₁ := D.scale₁
  scale₂ := D.scale₂
  base := D.base
  length := D.length
  leftWeight := D.leftWeight
  rightWeight := D.rightWeight
  slotWeight := D.slotWeight
  plain₁ I hI := by simpa only [hphase] using D.plain₁ I hI
  plain₂ I hI := by simpa only [hphase] using D.plain₂ I hI
  prime i p hp := by simpa only [hphase] using D.prime i p hp

@[simp] theorem rephase_coefficient (phase' : Ray →* Circle) (hphase : phase' = phase) :
    (D.rephase phase' hphase).coefficient = D.coefficient := rfl

@[simp] theorem rephase_normalizedCoefficient (phase' : Ray →* Circle)
    (hphase : phase' = phase) (u v : ℂ) (t : Fin k → ℂ) :
    (D.rephase phase' hphase).normalizedCoefficient u v t = D.normalizedCoefficient u v t := rfl

end SecondCoefficientTermDictionary

namespace SecondCoefficientComparison

variable {k : ℕ} {Ray : Type*} [CommGroup Ray]
variable {T : FixedChildCharacters K k} {phase : Ray →* Circle}
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {D : SecondCoefficientTermDictionary T phase S₁ S₂ S}
variable (E : SecondCoefficientComparison D)

/-- The original comparison rectangle follows the same phase transport;
its two original scales and individual profile values are unchanged. -/
def rephase (phase' : Ray →* Circle) (hphase : phase' = phase) :
    SecondCoefficientComparison (D.rephase phase' hphase) where
  leftAtom := E.leftAtom
  rightAtom := E.rightAtom
  scale₁ := E.scale₁
  scale₂ := E.scale₂
  leftWeight := E.leftWeight
  rightWeight := E.rightWeight
  plain₁ I hI := by
    simpa only [SecondCoefficientTermDictionary.rephase, hphase] using E.plain₁ I hI
  plain₂ I hI := by
    simpa only [SecondCoefficientTermDictionary.rephase, hphase] using E.plain₂ I hI

@[simp] theorem rephase_centeredCoefficient (phase' : Ray →* Circle)
    (hphase : phase' = phase) (u v : ℂ) (t : Fin k → ℂ) :
    (E.rephase phase' hphase).centeredCoefficient u v t = E.centeredCoefficient u v t := rfl

end SecondCoefficientComparison

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {C : A.GeneralArithmeticContext σ η hS}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {k : ℕ}

namespace SecondSideFrame

/-- The old right frame as a left frame of the actual swapped
correlation. All original allocation and profile data are retained. -/
def toLeft (f : SecondSideFrame (V := V) C R Ray .right k) :
    SecondSideFrame (V := V) C R.swapColumns Ray .left k where
  allocation := f.allocation
  characters := f.characters
  phaseCharacter := swappedSecondPhase Ray f.phaseCharacter
  dictionary := f.dictionary.rephase
    (fixedLeftPhase Ray (swappedSecondPhase Ray f.phaseCharacter))
    (fixedLeftPhase_swappedSecondPhase Ray f.phaseCharacter)
  base_gt_one := f.base_gt_one
  length_pos := f.length_pos
  ideal := f.ideal
  ideal_product := f.ideal_product
  gaussScale₁ := f.gaussScale₁
  gaussScale₂ := f.gaussScale₂
  gaussSlotScale := f.gaussSlotScale
  gaussScale₁_pos := f.gaussScale₁_pos
  gaussScale₂_pos := f.gaussScale₂_pos
  gaussSlotScale_pos := f.gaussSlotScale_pos
  leftLocation h I := -f.leftLocation h I
  rightLocation h I := -f.rightLocation h I
  slotLocation h i p := -f.slotLocation h i p

/-- The old left frame becomes the right frame with its original
comparison and the same actual second divisor and retained slots. -/
def toRight (f : SecondSideFrame (V := V) C R Ray .left k) :
    SecondSideFrame (V := V) C R.swapColumns Ray .right k where
  allocation := f.allocation
  characters := f.characters
  phaseCharacter := swappedSecondPhase Ray f.phaseCharacter
  dictionary := f.dictionary.rephase
    (fixedRightPhase Ray (swappedSecondPhase Ray f.phaseCharacter))
    (fixedRightPhase_swappedSecondPhase Ray f.phaseCharacter)
  base_gt_one := f.base_gt_one
  length_pos := f.length_pos
  ideal := f.ideal
  ideal_product := f.ideal_product
  gaussScale₁ := f.gaussScale₁
  gaussScale₂ := f.gaussScale₂
  gaussSlotScale := f.gaussSlotScale
  gaussScale₁_pos := f.gaussScale₁_pos
  gaussScale₂_pos := f.gaussScale₂_pos
  gaussSlotScale_pos := f.gaussSlotScale_pos
  leftLocation h I := -f.leftLocation h I
  rightLocation h I := -f.rightLocation h I
  slotLocation h i p := -f.slotLocation h i p

def toLeftComparison (f : SecondSideFrame (V := V) C R Ray .right k)
    (E : SecondCoefficientComparison f.dictionary) :
    SecondCoefficientComparison f.toLeft.dictionary :=
  E.rephase (fixedLeftPhase Ray (swappedSecondPhase Ray f.phaseCharacter))
    (fixedLeftPhase_swappedSecondPhase Ray f.phaseCharacter)

def toRightComparison (f : SecondSideFrame (V := V) C R Ray .left k)
    (E : SecondCoefficientComparison f.dictionary) :
    SecondCoefficientComparison f.toRight.dictionary :=
  E.rephase (fixedRightPhase Ray (swappedSecondPhase Ray f.phaseCharacter))
    (fixedRightPhase_swappedSecondPhase Ray f.phaseCharacter)

@[simp] theorem toLeft_allocation (f : SecondSideFrame (V := V) C R Ray .right k) :
    f.toLeft.allocation = f.allocation := rfl

@[simp] theorem toRight_allocation (f : SecondSideFrame (V := V) C R Ray .left k) :
    f.toRight.allocation = f.allocation := rfl

@[simp] theorem toLeft_normalizationScale (f : SecondSideFrame (V := V) C R Ray .right k) :
    f.toLeft.normalizationScale = f.normalizationScale := rfl

@[simp] theorem toRight_normalizationScale (f : SecondSideFrame (V := V) C R Ray .left k) :
    f.toRight.normalizationScale = f.normalizationScale := rfl

@[simp] theorem toLeft_coefficient (f : SecondSideFrame (V := V) C R Ray .right k)
    (h : H) (i : AllocationColumn K k) :
    f.toLeft.coefficient h i = star (f.coefficient h i) := by
  let c := f.dictionary.normalizedCoefficient (Real.sqrt f.gaussScale₁ : ℂ)⁻¹
    (Real.sqrt f.gaussScale₂ : ℂ)⁻¹ (fun j => (Real.sqrt (f.gaussSlotScale j) : ℂ)⁻¹)
  change c i * (fixedLeftPhase Ray (swappedSecondPhase Ray f.phaseCharacter)
      (f.dictionary.ray i) : ℂ) * σ (A.sexticResidue (f.ideal i) (-R.frequency h)) =
    star (star (c i * (fixedRightPhase Ray f.phaseCharacter (f.dictionary.ray i) : ℂ) *
      σ (A.sexticResidue (f.ideal i) (-R.frequency h))))
  rw [fixedLeftPhase_swappedSecondPhase, star_star]

@[simp] theorem toRight_coefficient (f : SecondSideFrame (V := V) C R Ray .left k)
    (h : H) (i : AllocationColumn K k) :
    f.toRight.coefficient h i = star (f.coefficient h i) := by
  let c := f.dictionary.normalizedCoefficient (Real.sqrt f.gaussScale₁ : ℂ)⁻¹
    (Real.sqrt f.gaussScale₂ : ℂ)⁻¹ (fun j => (Real.sqrt (f.gaussSlotScale j) : ℂ)⁻¹)
  change star (c i * (fixedRightPhase Ray (swappedSecondPhase Ray f.phaseCharacter)
      (f.dictionary.ray i) : ℂ) * σ (A.sexticResidue (f.ideal i) (- -R.frequency h))) =
    star (c i * (fixedLeftPhase Ray f.phaseCharacter (f.dictionary.ray i) : ℂ) *
      σ (A.sexticResidue (f.ideal i) (R.frequency h)))
  rw [fixedRightPhase_swappedSecondPhase, neg_neg]

@[simp] theorem toLeft_centeredCoefficient (f : SecondSideFrame (V := V) C R Ray .right k)
    (E : SecondCoefficientComparison f.dictionary) (h : H) (i : AllocationColumn K k) :
    f.toLeft.centeredCoefficient (f.toLeftComparison E) h i =
      star (f.centeredCoefficient E h i) := by
  let c := E.centeredCoefficient (Real.sqrt f.gaussScale₁ : ℂ)⁻¹
    (Real.sqrt f.gaussScale₂ : ℂ)⁻¹ (fun j => (Real.sqrt (f.gaussSlotScale j) : ℂ)⁻¹)
  change c i * (fixedLeftPhase Ray (swappedSecondPhase Ray f.phaseCharacter)
      (f.dictionary.ray i) : ℂ) * σ (A.sexticResidue (f.ideal i) (-R.frequency h)) =
    star (star (c i * (fixedRightPhase Ray f.phaseCharacter (f.dictionary.ray i) : ℂ) *
      σ (A.sexticResidue (f.ideal i) (-R.frequency h))))
  rw [fixedLeftPhase_swappedSecondPhase, star_star]

@[simp] theorem toRight_centeredCoefficient (f : SecondSideFrame (V := V) C R Ray .left k)
    (E : SecondCoefficientComparison f.dictionary) (h : H) (i : AllocationColumn K k) :
    f.toRight.centeredCoefficient (f.toRightComparison E) h i =
      star (f.centeredCoefficient E h i) := by
  let c := E.centeredCoefficient (Real.sqrt f.gaussScale₁ : ℂ)⁻¹
    (Real.sqrt f.gaussScale₂ : ℂ)⁻¹ (fun j => (Real.sqrt (f.gaussSlotScale j) : ℂ)⁻¹)
  change star (c i * (fixedRightPhase Ray (swappedSecondPhase Ray f.phaseCharacter)
      (f.dictionary.ray i) : ℂ) * σ (A.sexticResidue (f.ideal i) (- -R.frequency h))) =
    star (c i * (fixedLeftPhase Ray f.phaseCharacter (f.dictionary.ray i) : ℂ) *
      σ (A.sexticResidue (f.ideal i) (R.frequency h)))
  rw [fixedRightPhase_swappedSecondPhase, neg_neg]

@[simp] theorem toLeft_location (f : SecondSideFrame (V := V) C R Ray .right k)
    (h : H) (i : AllocationColumn K k) :
    rawSourceLocation (f.toLeft.leftLocation h) (f.toLeft.rightLocation h)
      (f.toLeft.slotLocation h) i =
        -rawSourceLocation (f.leftLocation h) (f.rightLocation h) (f.slotLocation h) i :=
  rawSourceLocation_neg _ _ _ _

@[simp] theorem toRight_location (f : SecondSideFrame (V := V) C R Ray .left k)
    (h : H) (i : AllocationColumn K k) :
    rawSourceLocation (f.toRight.leftLocation h) (f.toRight.rightLocation h)
      (f.toRight.slotLocation h) i =
        -rawSourceLocation (f.leftLocation h) (f.rightLocation h) (f.slotLocation h) i :=
  rawSourceLocation_neg _ _ _ _

end SecondSideFrame
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.fixedLeftPhase_swappedSecondPhase
#print axioms HeckeSkeleton.Moments.EngineStep.fixedRightPhase_swappedSecondPhase
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.toLeft_centeredCoefficient
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.toRight_centeredCoefficient
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.toLeft_location
