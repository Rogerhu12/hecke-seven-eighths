import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteNormalizedChildren

/-!
# A dependent family factory retains its individual analytic inputs

Different original source cases have different finite passive labels
and different individual zero-free certificates. This package records
those types before the certificates are supplied. Applying it preserves
the original normalized family and every child choice literally.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable (A : SArithmeticData K) (σ : K →+* ℂ)
variable (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable (ω ψ : HeckeCharacter K) (Z : ℝ)

structure CurriedNormalizedFamily where
  Label : Type
  labelFintype : Fintype Label
  LeftAnalytic : Type
  RightAnalytic : Type
  leftHeight : LeftAnalytic → Prop
  rightHeight : RightAnalytic → Prop
  make : ∀ l r, leftHeight l → rightHeight r →
    ActualNormalizedPairFamily A σ V Label ω ψ Z

attribute [instance] CurriedNormalizedFamily.labelFintype

namespace CurriedNormalizedFamily

variable {A σ V ω ψ Z}

def ofCurried {Λ L R : Type} [Fintype Λ]
    {hl : L → Prop} {hr : R → Prop}
    (make : ∀ l r, hl l → hr r → ActualNormalizedPairFamily A σ V Λ ω ψ Z) :
    CurriedNormalizedFamily A σ V ω ψ Z where
  Label := Λ
  labelFintype := inferInstance
  LeftAnalytic := L
  RightAnalytic := R
  leftHeight := hl
  rightHeight := hr
  make := make

variable (f : CurriedNormalizedFamily A σ V ω ψ Z)

def Input := {l : f.LeftAnalytic // f.leftHeight l} ×
  {r : f.RightAnalytic // f.rightHeight r}

def family (input : f.Input) : ActualNormalizedPairFamily A σ V f.Label ω ψ Z :=
  f.make input.1.val input.2.val input.1.property input.2.property

def input (l : f.LeftAnalytic) (r : f.RightAnalytic)
    (hl : f.leftHeight l) (hr : f.rightHeight r) : f.Input :=
  (⟨l, hl⟩, ⟨r, hr⟩)

@[simp] theorem family_input (l : f.LeftAnalytic) (r : f.RightAnalytic)
    (hl : f.leftHeight l) (hr : f.rightHeight r) :
    f.family (f.input l r hl hr) = f.make l r hl hr := rfl

@[simp] theorem ofCurried_make {Λ L R : Type} [Fintype Λ]
    {hl : L → Prop} {hr : R → Prop}
    (make : ∀ l r, hl l → hr r → ActualNormalizedPairFamily A σ V Λ ω ψ Z)
    (l : L) (r : R) (hleft : hl l) (hright : hr r) :
    (ofCurried make).make l r hleft hright = make l r hleft hright := rfl

end CurriedNormalizedFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CurriedNormalizedFamily.ofCurried
#print axioms HeckeSkeleton.Moments.EngineStep.CurriedNormalizedFamily.family_input
