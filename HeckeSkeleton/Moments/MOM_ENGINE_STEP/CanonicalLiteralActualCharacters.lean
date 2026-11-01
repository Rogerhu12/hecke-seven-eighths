import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SlotMeshPreservation

/-!
# Actual character recipes and original slot embeddings

The original atom table has the parent's literal slot dictionary.
First extraction, the original atlas cast, second extraction and the
second atlas cast compose their actual injections.  Norm powers,
Gauss factors, scalar multiplication and deletion do not change a slot
length.  The source characters follow exactly the same index.

The certificates below are constructed outputs.  No whole coefficient
identity, arbitrary slot dictionary, or completed calibration is an
input to their actual-source constructors.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum MeasureTheory

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralActualCharacters

def keepEmbedding {k : ℕ} (keep : Finset (Fin k)) : Fin keep.card ↪ Fin k where
  toFun := SlotRestriction.index keep
  inj' := by
    intro i j hij
    apply keep.equivFin.symm.injective
    apply Subtype.ext
    exact hij

def inverseCastEmbedding {k n : ℕ} (count : k = n) : Fin n ↪ Fin k where
  toFun := Fin.cast count.symm
  inj' := by
    intro i j hij
    apply Fin.ext
    exact congrArg Fin.val hij

variable {A : SArithmeticData K}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}

/-- The character equality and length dictionary share one explicitly
constructed injective original-slot map. -/
structure Recipe (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
    (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
    (correction : HeckeCharacter K) (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
    {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k) where
  slots : OriginalSlotDictionary parent d.length
  characters : d.characters = CanonicalLiteralPhaseCalibration.sourceCharacters
    P R F parent oldMoving correction remaining extra slots.index

namespace Recipe

variable {P R}
variable {F : CanonicalLiteralPhaseCalibration.FixedPhases A}
variable {parent : MomentData K ω ψ} {oldMoving : OriginalMovingFactors A P R}
variable {correction : HeckeCharacter K}
variable {remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K}
variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (E : Recipe P R F parent oldMoving correction remaining extra d)

def onAtlas {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount) :
    Recipe P R F parent oldMoving correction remaining extra (d.onAtlas T count) where
  slots :=
    { index := (inverseCastEmbedding count).trans E.slots.index
      length_eq := by
        intro i
        cases count
        exact E.slots.length_eq i }
  characters := by
    change (d.onAtlas T count).characters =
      CanonicalLiteralPhaseCalibration.sourceCharacters P R F parent oldMoving correction
        remaining extra (fun i => E.slots.index (Fin.cast count.symm i))
    rw [CanonicalLiteralRectangles.Atoms.onAtlas_characters, E.characters,
      CanonicalLiteralPhaseCalibration.sourceCharacters_selectSlots]

@[simp] theorem onAtlas_index {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount)
    (i : Fin T.slotCount) :
    (E.onAtlas T count).slots.index i = E.slots.index (Fin.cast count.symm i) := rfl

def extract {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    Recipe P R F parent oldMoving correction remaining extra (d.extract b) where
  slots :=
    { index := (keepEmbedding b.keep).trans E.slots.index
      length_eq i := E.slots.length_eq (SlotRestriction.index b.keep i) }
  characters := by
    change d.characters.restrictSlots b.keep =
      CanonicalLiteralPhaseCalibration.sourceCharacters P R F parent oldMoving correction
        remaining extra (fun i => E.slots.index (SlotRestriction.index b.keep i))
    rw [E.characters, CanonicalLiteralPhaseCalibration.sourceCharacters_restrictSlots]

@[simp] theorem extract_index {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (i : Fin b.keep.card) :
    (E.extract b).slots.index i = E.slots.index (SlotRestriction.index b.keep i) := rfl

end Recipe

section FixedPhases

variable [IsPrincipalIdealRing A.R]

/-- Direct and main sources retain the actual chosen empty-mask unit,
and their pool factor is the original unit ideal. -/
def unamplifiedPhases (firstIdeal : A.Exterior) (firstElement : A.R)
    (hfirst : A.Generates firstIdeal firstElement) :
    CanonicalLiteralPhaseCalibration.FixedPhases A where
  firstIdeal := firstIdeal
  poolIdeal := unitExterior A
  unitIdeal := unitExterior A
  firstElement := firstElement
  poolElement := 1
  unitElement := CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)
  first_generates := hfirst
  pool_generates := unitExterior_generates A
  unit_generates := CanonicalLiteralFixedPhases.emptyDivisorInverse_generates

def amplifiedPhases {σ : K →+* ℂ}
    {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
    (C : A.GeneralArithmeticContext σ η htrace)
    (firstIdeal : A.Exterior) (firstElement : A.R)
    (hfirst : A.Generates firstIdeal firstElement) (p : ExteriorPrime A) (n : ℕ) :
    CanonicalLiteralPhaseCalibration.FixedPhases A where
  firstIdeal := firstIdeal
  poolIdeal := powerIdeal p (2 * n)
  unitIdeal := unitExterior A
  firstElement := firstElement
  poolElement := generator C p ^ (2 * n)
  unitElement := CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)
  first_generates := hfirst
  pool_generates := generator_power_generates C p (2 * n)
  unit_generates := CanonicalLiteralFixedPhases.emptyDivisorInverse_generates

end FixedPhases
end CanonicalLiteralActualCharacters

namespace CanonicalLiteralRectangles.Atoms

/-- The actual mask update commutes with the atlas's slot cast. -/
theorem deleteMask_onAtlas {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
    {A : SArithmeticData K} {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.deleteMask extra).onAtlas T count = (d.onAtlas T count).deleteMask extra := by
  cases count
  rfl

end CanonicalLiteralRectangles.Atoms

namespace CompleteMovingRowRecipe

open CanonicalLiteralActualCharacters

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}

/-- The first occurrence extraction is the literal injection into the
original parent. All scalar, Gauss and norm-power operations leave its
lengths unchanged, and the original phase theorem computes its source. -/
def literalSecondInputRecipe (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₁
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₂
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots support)
    (F : CanonicalLiteralPhaseCalibration.FixedPhases A) (power : A.Exterior)
    (δ₁ δ₂ : ℝ) (extra : HeckeGeneral.Analysis.NonzeroIdeal K) :
    Recipe P R F (data ξ) Q.moving Q.correction Q.remaining extra
      (((Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).secondInput
        (σ := σ) b P R power F.firstIdeal F.poolIdeal F.unitIdeal F.firstElement
        F.poolElement F.unitElement F.first_generates F.pool_generates F.unit_generates
        δ₁ δ₂).deleteMask extra) where
  slots :=
    { index := keepEmbedding b.keep
      length_eq _ := rfl }
  characters :=
    (CanonicalLiteralPhaseCalibration.secondInput_characters (σ := σ) P R F
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂) b power δ₁ δ₂ extra).trans
      (CanonicalLiteralPhaseCalibration.apply_literalSourceCharacters_restricted
        P R Q F ξ extra b.keep)

end CompleteMovingRowRecipe

section CoveredLeaves

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}

local instance canonicalLiteralActualCharactersCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.CoveredClassKey

open CanonicalLiteralActualCharacters

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : s.CoveredClassKey LC RC)
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {F : CanonicalLiteralPhaseCalibration.FixedPhases A} {ω ψ : HeckeCharacter K}
variable {parent : MomentData K ω ψ} {oldMoving : OriginalMovingFactors A P R}
variable {correction : HeckeCharacter K}
variable {remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K}

/-- The second actual left extraction composes its own keep map with
the already calculated first map. No whole-source equality is needed. -/
def literalLeftRecipe
    (d : CanonicalLiteralRectangles.Atoms (K := K) (LC.branch v.2.2.1).slotCount)
    (E : Recipe P R F parent oldMoving correction remaining extra d) :
    Recipe P R F parent oldMoving correction remaining extra (v.literalLeftAtoms d) :=
  (((E.onAtlas v.literalLeftParent rfl).extract v.literalLeftBranch)
    .onAtlas v.literalLeftResidualAtlas rfl)

def literalRightRecipe
    (d : CanonicalLiteralRectangles.Atoms (K := K) (RC.branch v.2.2.2.1).slotCount)
    (E : Recipe P R F parent oldMoving correction remaining extra d) :
    Recipe P R F parent oldMoving correction remaining extra (v.literalRightAtoms d) :=
  (((E.onAtlas v.literalRightParent rfl).extract v.literalRightBranch)
    .onAtlas v.literalRightResidualAtlas rfl)

end ActualGaussStage.CoveredClassKey
end CoveredLeaves

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralActualCharacters.Recipe.onAtlas
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralActualCharacters.Recipe.extract
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.deleteMask_onAtlas
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalSecondInputRecipe
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalLeftRecipe
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalRightRecipe
