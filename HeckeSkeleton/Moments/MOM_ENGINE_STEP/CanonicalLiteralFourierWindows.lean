import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSchwartzProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocatedData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalClippedProfileBounds

set_option linter.unusedSectionVars false

/-!
# The actual Fourier profiles and their computed windows

The representatives below refer to the literal allocated data, with
the actual original scales inside every Fourier phase. Those scales
contribute only constant phases: their logarithms do not enter the
seminorm coefficient. Bounds on the representatives before Fourier
transformation are supplied by the original-profile constructors in
`CanonicalLiteralSchwartzProfiles`, including their displayed scalar
costs. The final raw or clipped window is a return value.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralFourierWindows

def coefficient (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (firstSign : ℝ) (s : Finset (ℕ × ℕ)) : ℝ :=
  CanonicalLogProfiles.shapeCoefficient window hcompact hpositive 0 s *
    (1 + 2 * Real.pi * ‖CanonicalLiteralLocations.direction firstSign‖) ^ (s.sup Prod.snd)

theorem coefficient_nonneg (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (firstSign : ℝ) (s : Finset (ℕ × ℕ)) :
    0 ≤ coefficient window hcompact hpositive firstSign s := by
  sorry

theorem atom_coefficient (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (scale : ℝ) (hscale : 0 < scale)
    (firstSign : ℝ) (negative : Bool) (s : Finset (ℕ × ℕ)) :
    (CanonicalLiteralProfileData.fourierAtom scale hscale firstSign negative)
        .profileCoefficient window hcompact hpositive s =
      coefficient window hcompact hpositive firstSign s := by
  sorry

theorem atom_tsupport {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (p : CanonicalLogProfiles.Atom V) (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (ξ : V) (φ : 𝓢(ℝ, ℂ))
    (hsupport : tsupport φ ⊆ window) :
    tsupport (p.schwartz window hcompact hpositive ξ φ hsupport) ⊆ tsupport φ := by
  sorry

theorem fourier_bound {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (J : ℕ) (ξ : WithLp 2 (ℝ × ℝ)) :
    C * (1 + ‖ξ‖) ^ J * B ≤
      polynomialProfileRadius (B * (1 + C)) J J (WithLp.ofLp ξ) := by
  sorry

theorem bound_le_radius {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (J : ℕ) (ξ : WithLp 2 (ℝ × ℝ)) :
    B ≤ polynomialProfileRadius (B * (1 + C)) J J (WithLp.ofLp ξ) := by
  sorry

end CanonicalLiteralFourierWindows

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
variable {window : Set ℝ} (E : W.SchwartzModel window)
variable (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
variable (firstSign : ℝ) (negative : Bool)

def leftFourierRep (r : Bool) (ξ : WithLp 2 (ℝ × ℝ)) : 𝓢(ℝ, ℂ) :=
  (CanonicalLiteralProfileData.fourierAtom (d.scale₁ r) (d.scale₁_pos r) firstSign negative)
    .schwartz window hcompact hpositive ξ (E.left r) (E.left_support r)

def rightFourierRep (r : Bool) (ξ : WithLp 2 (ℝ × ℝ)) : 𝓢(ℝ, ℂ) :=
  (CanonicalLiteralProfileData.fourierAtom (d.scale₂ r) (d.scale₂_pos r) firstSign negative)
    .schwartz window hcompact hpositive ξ (E.right r) (E.right_support r)

def slotFourierRep (j : Fin k) (ξ : WithLp 2 (ℝ × ℝ)) : 𝓢(ℝ, ℂ) :=
  (CanonicalLiteralProfileData.fourierAtom (d.base ^ d.length j)
    (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _) firstSign negative)
    .schwartz window hcompact hpositive ξ (E.slot j) (E.slot_support j)

theorem leftFourierRep_eq (r : Bool) (ξ : WithLp 2 (ℝ × ℝ))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t y : ℝ) :
    (W.fourierLeft r firstSign negative ξ).profile u t y =
      E.leftFourierRep hcompact hpositive firstSign negative r ξ y := by
  sorry

theorem rightFourierRep_eq (r : Bool) (ξ : WithLp 2 (ℝ × ℝ))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t y : ℝ) :
    (W.fourierRight r firstSign negative ξ).profile u t y =
      E.rightFourierRep hcompact hpositive firstSign negative r ξ y := by
  sorry

theorem slotFourierRep_eq (j : Fin k) (ξ : WithLp 2 (ℝ × ℝ)) (t y : ℝ) :
    (W.fourierSlot j firstSign negative ξ).profile t y =
      E.slotFourierRep hcompact hpositive firstSign negative j ξ y := by
  sorry

theorem leftFourierRep_support (r : Bool) (ξ : WithLp 2 (ℝ × ℝ)) :
    tsupport (E.leftFourierRep hcompact hpositive firstSign negative r ξ) ⊆ window := by
  sorry

theorem rightFourierRep_support (r : Bool) (ξ : WithLp 2 (ℝ × ℝ)) :
    tsupport (E.rightFourierRep hcompact hpositive firstSign negative r ξ) ⊆ window := by
  sorry

theorem slotFourierRep_support (j : Fin k) (ξ : WithLp 2 (ℝ × ℝ)) :
    tsupport (E.slotFourierRep hcompact hpositive firstSign negative j ξ) ⊆ window := by
  sorry

theorem leftFourierRep_bound (r : Bool) (ξ : WithLp 2 (ℝ × ℝ)) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (E.leftFourierRep hcompact hpositive firstSign negative r ξ) ≤
      CanonicalLiteralFourierWindows.coefficient window hcompact hpositive firstSign s *
        (1 + ‖ξ‖) ^ (s.sup Prod.snd) *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) := by
  sorry

theorem rightFourierRep_bound (r : Bool) (ξ : WithLp 2 (ℝ × ℝ)) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (E.rightFourierRep hcompact hpositive firstSign negative r ξ) ≤
      CanonicalLiteralFourierWindows.coefficient window hcompact hpositive firstSign s *
        (1 + ‖ξ‖) ^ (s.sup Prod.snd) *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) := by
  sorry

theorem slotFourierRep_bound (j : Fin k) (ξ : WithLp 2 (ℝ × ℝ)) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (E.slotFourierRep hcompact hpositive firstSign negative j ξ) ≤
      CanonicalLiteralFourierWindows.coefficient window hcompact hpositive firstSign s *
        (1 + ‖ξ‖) ^ (s.sup Prod.snd) *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) := by
  sorry

end CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFourierWindows.atom_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.leftFourierRep_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.rightFourierRep_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.slotFourierRep_bound
