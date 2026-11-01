import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualFirstSecondSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualDirectSecondStages
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualPoolTerminalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSupportedLeaves

/-!
# Pure-dual windows on the original supported stages

The existing engine support operations only change the physical fibre
bound and the chart coefficients. The original source, test profile,
mask, radius, and cutoff are retained. Consequently the individual
pure-dual terminal windows and the signed-origin conditions transport
directly to those same supported stages.

The pool and parent constructions below follow the existing four tags,
two sides, and common-label indices. The direct preparation is the
already defined `supported.gated` stage. No leaf carrier is constructed
here and no equality of the old and supported total costs is asserted.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
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
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

namespace DualTerminalCalibration

def supported (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay) :
    s.supported.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay := { T with }

def gated (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay) :
    s.gated.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay := { T with }

end DualTerminalCalibration

namespace DualResidualTerminalWindows

variable {S : Ideal (𝓞 K)} {slots : ℕ} {B : ℝ}
variable {atoms : FirstDivisorCoefficientAtoms (A := A) (σ := σ)
  G.columns G.coefficient S slots B}

def supported (T : s.DualResidualTerminalWindows atoms sTail sZero k Z Lmax Nsave decay) :
    s.supported.DualResidualTerminalWindows atoms sTail sZero k Z Lmax Nsave decay :=
  { T with }

def gated (T : s.DualResidualTerminalWindows atoms sTail sZero k Z Lmax Nsave decay) :
    s.gated.DualResidualTerminalWindows atoms sTail sZero k Z Lmax Nsave decay :=
  { T with }

@[simp] theorem supported_calibration
    (T : s.DualResidualTerminalWindows atoms sTail sZero k Z Lmax Nsave decay) :
    T.supported.calibration = T.calibration.supported := rfl

@[simp] theorem gated_calibration
    (T : s.DualResidualTerminalWindows atoms sTail sZero k Z Lmax Nsave decay) :
    T.gated.calibration = T.calibration.gated := rfl

end DualResidualTerminalWindows
end ActualGaussStage

section PoolTransport

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
variable {dpool : FirstGaussPoolData C P ι} {c : ι → ℂ}

namespace ActualPoolStages

variable (s : ActualPoolStages (E := E) hΓ μv hDiff dpool c finiteTest)

@[simp] theorem supported_tag (b : PoolSourceTag P) :
    s.supported.tag b = (s.tag b).supported := by
  rcases b with u | p | p | p <;> rfl

@[simp] theorem gated_tag (b : PoolSourceTag P) :
    s.gated.tag b = (s.tag b).gated := by
  rcases b with u | p | p | p <;> rfl

variable {s}

namespace DualSourceConditions

def supported (hs : s.DualSourceConditions) : s.supported.DualSourceConditions where
  mask b := by rw [supported_tag]; exact hs.mask b
  origin_nonneg b := by rw [supported_tag]; exact hs.origin_nonneg b

def gated (hs : s.DualSourceConditions) : s.gated.DualSourceConditions where
  mask b := by rw [gated_tag]; exact hs.mask b
  origin_nonneg b := by rw [gated_tag]; exact hs.origin_nonneg b

end DualSourceConditions

variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

namespace DualTerminalCalibration

def supported (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay) :
    s.supported.DualTerminalCalibration sTail sZero k Lmax Nsave decay where
  main := T.main.supported
  one p := (T.one p).supported
  six p := (T.six p).supported
  seven p := (T.seven p).supported

def gated (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay) :
    s.gated.DualTerminalCalibration sTail sZero k Lmax Nsave decay where
  main := T.main.gated
  one p := (T.one p).gated
  six p := (T.six p).gated
  seven p := (T.seven p).gated

end DualTerminalCalibration

namespace DualFirstDivisorWindows

variable {S : Ideal (𝓞 K)} {slots : ℕ} {B : ℝ}

/-- The frozen atoms remain the same functions on the original tag
source; only the supported stage indexing the residual window changes. -/
def supported (T : s.DualFirstDivisorWindows S slots B sTail sZero k Lmax Nsave decay) :
    s.supported.DualFirstDivisorWindows S slots B sTail sZero k Lmax Nsave decay where
  atoms := T.atoms
  profile b := by
    simpa only [supported_tag] using (T.profile b).supported

def gated (T : s.DualFirstDivisorWindows S slots B sTail sZero k Lmax Nsave decay) :
    s.gated.DualFirstDivisorWindows S slots B sTail sZero k Lmax Nsave decay where
  atoms := T.atoms
  profile b := by
    simpa only [gated_tag] using (T.profile b).gated

end DualFirstDivisorWindows
end ActualPoolStages

namespace FirstBlockPoolData.SecondStages

variable {κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockPoolData chart P M X hX}
variable {s : p.SecondStages (E := E) (hDiff := hDiff)}

namespace DualSourceConditions

def supported (hs : s.DualSourceConditions) : s.supported.DualSourceConditions where
  left S χ := (hs.left S χ).supported
  right S χ := (hs.right S χ).supported

def gated (hs : s.DualSourceConditions) : s.gated.DualSourceConditions where
  left S χ := (hs.left S χ).gated
  right S χ := (hs.right S χ).gated

end DualSourceConditions

namespace DualTerminalCalibration

variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def supported (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay) :
    s.supported.DualTerminalCalibration sTail sZero k Lmax Nsave decay where
  left S χ := (T.left S χ).supported
  right S χ := (T.right S χ).supported

def gated (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay) :
    s.gated.DualTerminalCalibration sTail sZero k Lmax Nsave decay where
  left S χ := (T.left S χ).gated
  right S χ := (T.right S χ).gated

end DualTerminalCalibration
end FirstBlockPoolData.SecondStages

namespace ActualFirstSource.SecondStages

variable {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}
variable {R : s.SecondStages (E := E) (hDiff := hDiff)}

namespace DualSourceConditions

def supported (hs : R.DualSourceConditions) : R.supported.DualSourceConditions :=
  fun v D => (hs v D).supported

def gated (hs : R.DualSourceConditions) : R.gated.DualSourceConditions :=
  fun v D => (hs v D).gated

end DualSourceConditions

namespace DualTerminalCalibration

variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def supported (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay) :
    R.supported.DualTerminalCalibration sTail sZero k Lmax Nsave decay :=
  fun v D => (T v D).supported

def gated (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay) :
    R.gated.DualTerminalCalibration sTail sZero k Lmax Nsave decay :=
  fun v D => (T v D).gated

end DualTerminalCalibration
end ActualFirstSource.SecondStages

end PoolTransport

namespace FirstBlockDirectData.SecondStages

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart M X hX}
variable {s : p.SecondStages (E := E) (hDiff := hDiff)}

namespace DualSourceConditions

def prepared (hs : s.DualSourceConditions) : s.prepared.DualSourceConditions where
  left_mask := hs.left_mask
  right_mask := hs.right_mask
  left_origin_nonneg := hs.left_origin_nonneg
  right_origin_nonneg := hs.right_origin_nonneg

end DualSourceConditions

namespace DualTerminalCalibration

variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

def prepared (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay) :
    s.prepared.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay where
  left S χ := (T.left S χ).supported.gated
  right S χ := (T.right S χ).supported.gated

end DualTerminalCalibration
end FirstBlockDirectData.SecondStages

namespace ActualDirectFirstSource.SecondStages

variable {Z : ℝ} {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}
variable {R : s.SecondStages (E := E) (hDiff := hDiff)}

namespace DualSourceConditions

def prepared (hs : R.DualSourceConditions) : R.prepared.DualSourceConditions :=
  fun v D => (hs v D).prepared

end DualSourceConditions

namespace DualTerminalCalibration

variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def prepared (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay) :
    R.prepared.DualTerminalCalibration sTail sZero k Lmax Nsave decay :=
  fun v D => (T v D).prepared

end DualTerminalCalibration
end ActualDirectFirstSource.SecondStages

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualResidualTerminalWindows.supported_calibration
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualSourceConditions.supported
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualFirstDivisorWindows.gated
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.DualTerminalCalibration.supported
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.DualSourceConditions.gated
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.DualTerminalCalibration.prepared
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.DualSourceConditions.prepared
