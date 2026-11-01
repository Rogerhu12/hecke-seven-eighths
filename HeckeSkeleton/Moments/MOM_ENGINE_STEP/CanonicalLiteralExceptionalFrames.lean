import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalCharts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFrameCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondExceptionalBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinarySecondExceptionalBinding

/-!
# Exceptional charts on the original literal side frames

The frame, its allocation and its actual residual row are unchanged.
The chart factory reads the original table and computed character
recipe. Both original plain profiles are preserved, up to their actual
constant divisor phases. The right source uses its negative frequency
and negative joint locations together.

The output is the existing source's `ExceptionalAt` or
`OrdinaryExceptionalAt`, so the terminal can read the complete literal
Fourier column without a supplied whole-polynomial identity. The
frame's Gauss normalizer remains outside this source exactly as in
`centered_column_norm_eq_source` and `ordinary_column_norm_eq_source`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFrames

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralExceptionalCharts

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable {ω ψ : HeckeCharacter K}
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (C : A.GeneralArithmeticContext σ η hS)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (S : ActualSecondCorrelationRows A σ H ι) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (row : CanonicalOriginalPhaseCalibration.PatternSector P S C pattern ν)
variable (he : S.literalCharacter C P R F oldMoving correction pattern ν
  row.val.val.val ∈ parent.theta)
variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (recipe : CanonicalLiteralActualCharacters.Recipe P R F parent oldMoving
  correction remaining extra d)
variable {W : d.ProfileData} {window : Set ℝ} (E : W.SchwartzModel window)
variable (firstSupport : Finset (Ideal (𝓞 K)))
variable (hfirst : ∀ q ∈ firstSupport, Prime q)
variable (hextra : extra = literalDeletionIdeal firstSupport hfirst)
variable (hm : ∀ i, 0 < S.leftMultiplicity i) (hn : ∀ i, 0 < S.rightMultiplicity i)
variable (support : d.SupportData ((primeSupport A.cS ∪ firstSupport) ∪
  primeSupport (primePowerProduct S.primes S.leftMultiplicity).val))
variable (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (L : Ideal (𝓞 K))
variable (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "Joint" => WithLp 2 (ℝ × ℝ)
local notation "frame" =>
  (d.factors S side χ ideal hideal firstSign false).frame C L selection hne
local notation "actualCharacter" => CanonicalLiteralExceptionalCharacters.catalogue
  ψ parent.theta (CanonicalLiteralExceptionalCharacters.rowIndex P R F parent
    oldMoving correction C S pattern ν row he)
local notation "leftProfile" => fun ξ : Joint =>
  profile firstSign (orientedMode side.literalNegative ξ)
    ((frame).allocation.plainDivisor 0) (E.left false)
local notation "rightProfile" => fun ξ : Joint =>
  profile firstSign (orientedMode side.literalNegative ξ)
    ((frame).allocation.plainDivisor (Fin.succ 0)) (E.right false)

include hcorr hone hroot hemb recipe hfirst hextra hm hn support in
/-- Four computed one-ideal charts on this very frame source. -/
def centered (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (ξ : Joint) :
    (frame).source.ExceptionalAt (σ := σ) (d.scale₁ true) (d.scale₂ true)
      (fun _ => d.rectangleLeftWeight true) (fun _ => d.rightWeight true)
      actualCharacter (leftProfile ξ) (rightProfile ξ) ξ row.val.val := by
  let T := actualCenteredSource P R F parent oldMoving correction hcorr C S pattern ν
    remaining extra hone hroot hemb row he recipe E firstSupport hfirst hextra hm hn
    support (frame).allocation rfl rfl hc hscale side.literalNegative firstSign ξ
  cases side <;> exact {
    mask := T.mask
    time := T.time
    product := T.product
    lower := T.lower
    lower_pos := T.lower_pos
    X₁_lower := T.X₁_lower
    X₂_lower := T.X₂_lower
    Y₁_lower := T.Y₁_lower
    Y₂_lower := T.Y₂_lower
    productX := T.productX
    productY := T.productY
    chartX₁ := T.chartX₁
    chartX₂ := T.chartX₂
    chartY₁ := T.chartY₁
    chartY₂ := T.chartY₂
  }

include hcorr hone hroot hemb recipe hfirst hextra hm hn support in
/-- The ordinary frame uses only the original first rectangle. -/
def ordinary (ξ : Joint) :
    (frame).source.OrdinaryExceptionalAt (σ := σ)
      actualCharacter (leftProfile ξ) (rightProfile ξ) ξ row.val.val := by
  let T := actualOrdinarySource P R F parent oldMoving correction hcorr C S pattern ν
    remaining extra hone hroot hemb row he recipe E firstSupport hfirst hextra hm hn
    support (frame).allocation rfl rfl side.literalNegative firstSign ξ
  cases side <;> exact {
    mask := T.mask
    time := T.time
    product := T.product
    lower := T.lower
    lower_pos := T.lower_pos
    X₁_lower := T.X₁_lower
    X₂_lower := T.X₂_lower
    productX := T.productX
    chartX₁ := T.chartX₁
    chartX₂ := T.chartX₂
  }

/-- A genuine theta class fixes the catalogue entry before the row
sum. The equality is on the literal original row character. -/
theorem rowIndex_eq_selectedIndex (θ : parent.theta)
    (hθ : S.literalCharacter C P R F oldMoving correction pattern ν
      row.val.val.val = θ.val) :
    CanonicalLiteralExceptionalCharacters.rowIndex P R F parent oldMoving correction
      C S pattern ν row he =
      CanonicalLiteralExceptionalCharacters.selectedIndex parent θ := by
  apply Prod.ext
  · rfl
  · exact Subtype.ext hθ

include hcorr hone hroot hemb recipe hfirst hextra hm hn support in
/-- The centered terminal receives one fixed catalogue entry on the
actual theta class; its membership is derived from that class. -/
def centeredAtTheta (θ : parent.theta)
    (hθ : S.literalCharacter C P R F oldMoving correction pattern ν
      row.val.val.val = θ.val)
    (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (ξ : Joint) :
    (frame).source.ExceptionalAt (σ := σ) (d.scale₁ true) (d.scale₂ true)
      (fun _ => d.rectangleLeftWeight true) (fun _ => d.rightWeight true)
      (CanonicalLiteralExceptionalCharacters.catalogue ψ parent.theta
        (CanonicalLiteralExceptionalCharacters.selectedIndex parent θ))
      (leftProfile ξ) (rightProfile ξ) ξ row.val.val := by
  have he' : S.literalCharacter C P R F oldMoving correction pattern ν
      row.val.val.val ∈ parent.theta := hθ.symm ▸ θ.property
  have hi := rowIndex_eq_selectedIndex P R F parent oldMoving correction C S pattern ν
    row he' θ hθ
  simpa only [hi] using centered P R F parent oldMoving correction hcorr C S pattern ν
    remaining extra hone hroot hemb row he' recipe E firstSupport hfirst hextra hm hn support
    side χ ideal hideal firstSign L selection hne hc hscale ξ

include hcorr hone hroot hemb recipe hfirst hextra hm hn support in
def ordinaryAtTheta (θ : parent.theta)
    (hθ : S.literalCharacter C P R F oldMoving correction pattern ν
      row.val.val.val = θ.val) (ξ : Joint) :
    (frame).source.OrdinaryExceptionalAt (σ := σ)
      (CanonicalLiteralExceptionalCharacters.catalogue ψ parent.theta
        (CanonicalLiteralExceptionalCharacters.selectedIndex parent θ))
      (leftProfile ξ) (rightProfile ξ) ξ row.val.val := by
  have he' : S.literalCharacter C P R F oldMoving correction pattern ν
      row.val.val.val ∈ parent.theta := hθ.symm ▸ θ.property
  have hi := rowIndex_eq_selectedIndex P R F parent oldMoving correction C S pattern ν
    row he' θ hθ
  simpa only [hi] using ordinary P R F parent oldMoving correction hcorr C S pattern ν
    remaining extra hone hroot hemb row he' recipe E firstSupport hfirst hextra hm hn support
    side χ ideal hideal firstSign L selection hne ξ

/-- The complete centered value is read from the existing literal
frame, including the source's whole negative-side orientation. -/
theorem centered_value (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (ξ : Joint) :
    (centered P R F parent oldMoving correction hcorr C S pattern ν remaining extra
      hone hroot hemb row he recipe E firstSupport hfirst hextra hm hn support
      side χ ideal hideal firstSign L selection hne hc hscale ξ).source.value =
      (frame).source.centeredColumn (σ := σ) (d.scale₁ true) (d.scale₂ true)
        (fun _ => d.rectangleLeftWeight true) (fun _ => d.rightWeight true) ξ row.val.val :=
  ActualAllocatedSource.ExceptionalAt.value_eq_centeredColumn _

theorem ordinary_value (ξ : Joint) :
    (ordinary P R F parent oldMoving correction hcorr C S pattern ν remaining extra
      hone hroot hemb row he recipe E firstSupport hfirst hextra hm hn support
      side χ ideal hideal firstSign L selection hne ξ).source.ordinaryValue =
      (frame).source.ordinaryColumn (σ := σ) ξ row.val.val :=
  ActualAllocatedSource.OrdinaryExceptionalAt.value_eq_ordinaryColumn _

/-- The actual divisor phase is a unit for every row and Fourier
mode, so only the original model's displayed seminorm is paid. -/
theorem leftProfile_seminorm (ξ : Joint) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (leftProfile ξ) =
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.left false) :=
  profile_seminorm _ _ _ _ _

theorem rightProfile_seminorm (ξ : Joint) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (rightProfile ξ) =
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.right false) :=
  profile_seminorm _ _ _ _ _

theorem leftProfile_support (ξ : Joint) : tsupport (leftProfile ξ) ⊆ window :=
  (profile_support _ _ _ _).trans (E.left_support false)

theorem rightProfile_support (ξ : Joint) : tsupport (rightProfile ξ) ⊆ window :=
  (profile_support _ _ _ _).trans (E.right_support false)

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFrames

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFrames.centered
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFrames.ordinary
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFrames.centeredAtTheta
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFrames.ordinaryAtTheta
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFrames.centered_value
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFrames.ordinary_value
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFrames.leftProfile_seminorm
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFrames.rightProfile_seminorm
