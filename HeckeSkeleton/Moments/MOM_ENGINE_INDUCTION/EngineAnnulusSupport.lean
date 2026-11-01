import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.SideAnnulusSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PairedEngineAdmissibilityTransport

/-!
# Support proofs on the same numerical engine conclusion

This record refers only to the already selected public child data. Its
transport changes admissibility proofs and copies the original branch
carrier, child parameters, kernels, terminal terms and energy estimate.
The actual source constructors prove the record in the subsequent files.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField DedekindZetaZeroFree HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.Moments.EngineStep

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ step ε terminalExponent C control : ℝ}
variable {admissible : MomentData K ω ψ → RealParameters → Prop}

/-- Tight support properties of the exact output data, with no new
child, radius, scalar estimate or source choice. -/
structure EngineAnnulusSupport
    (out : PairedEngineConclusion (Ω := Ω) centered d a
      Z t Y₁ Y₂ step ε terminalExponent C control admissible)
    (lo hi : ℝ) (orders : Finset (ℕ × ℕ)) : Prop where
  window : ∀ (b : Fin out.branches) (ξ : Ω),
    InFixedProfileWindow Set.univ Set.univ (Set.Icc (lo / hi) hi) orders
        (out.leftData b ξ) ∧
      InFixedProfileWindow Set.univ Set.univ (Set.Icc (lo / hi) hi) orders
        (out.rightData b ξ)
  prime : ∀ (b : Fin out.branches) (ξ : Ω),
    (∀ i t, Function.support (((out.leftData b ξ).geometry.slots i).profile t) ⊆
        Set.Ioo (1 : ℝ) 2) ∧
      (∀ i t, Function.support (((out.rightData b ξ).geometry.slots i).profile t) ⊆
        Set.Ioo (1 : ℝ) 2)

namespace EngineAnnulusSupport

variable {out : PairedEngineConclusion (Ω := Ω) centered d a
  Z t Y₁ Y₂ step ε terminalExponent C control admissible}
variable {lo hi : ℝ} {orders : Finset (ℕ × ℕ)}

theorem of_zero_branches (h : out.branches = 0) :
    EngineAnnulusSupport out lo hi orders where
  window b _ := Fin.elim0 (Fin.cast h b)
  prime b _ := Fin.elim0 (Fin.cast h b)

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {Q : Type*} {broad : Set ℝ}
variable (out : PairedEngineConclusion (Ω := Ω) centered d a
  Z t Y₁ Y₂ step ε terminalExponent C control
  (MovingEngineChildAdmissible A P R Q d Set.univ broad orders Z))

/-- The owner's admissibility transport keeps all numerical fields and
makes the actual stronger support available to the recursive caller. -/
def withProfileSupports (h : EngineAnnulusSupport out lo hi orders) :
    PairedEngineConclusion (Ω := Ω) centered d a
      Z t Y₁ Y₂ step ε terminalExponent C control
      (fun child parameters =>
        MovingEngineChildAdmissible A P R Q d Set.univ
          (Set.Icc (lo / hi) hi) orders Z child parameters ∧
        ∀ i t, Function.support ((child.geometry.slots i).profile t) ⊆ Set.Ioo (1 : ℝ) 2) :=
  out.withAdmissible _
    (fun b ξ => ⟨movingChild_withWindow (out.left_admissible b ξ) (h.window b ξ).1,
      (h.prime b ξ).1⟩)
    (fun b ξ => ⟨movingChild_withWindow (out.right_admissible b ξ) (h.window b ξ).2,
      (h.prime b ξ).2⟩)

@[simp] theorem withProfileSupports_leftData (h : EngineAnnulusSupport out lo hi orders) :
    (withProfileSupports out h).leftData = out.leftData := rfl

@[simp] theorem withProfileSupports_rightData (h : EngineAnnulusSupport out lo hi orders) :
    (withProfileSupports out h).rightData = out.rightData := rfl

@[simp] theorem withProfileSupports_kernel (h : EngineAnnulusSupport out lo hi orders) :
    (withProfileSupports out h).kernel = out.kernel := rfl

end EngineAnnulusSupport
end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.EngineAnnulusSupport.withProfileSupports
