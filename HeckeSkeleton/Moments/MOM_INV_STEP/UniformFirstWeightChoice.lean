import HeckeSkeleton.Moments.MOM_INV_STEP.FirstActualErrorPowers

/-!
# One source-independent first radial and row-count choice

The production and error terms share these exact exponents and this
constant. The choice precedes the parent, all source ideals, both
frequencies and every center or norm-box assignment.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.UniformFirstWeightChoice

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open FirstParentRows

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

structure Choice (lengthCap Hcap pi : ℝ) where
  epsilon : ℝ
  massExponent : ℝ
  constant : ℝ
  epsilon_pos : 0 < epsilon
  mass_pos : 0 < massExponent
  one_le_constant : 1 ≤ constant
  bound : ∀ {σ : Type*} (T : FirstParentEnergy.Data K S (σ := σ)),
    T.mask = ∅ → ∀ Z R B L H : ℝ, 1 ≤ Z →
    R ≤ lengthCap → B ≤ lengthCap → L ≤ lengthCap → H ≤ Hcap →
    T.radius.val ≤ Z ^ R →
    (∀ b ∈ T.cubes, (b.val.val.absNorm : ℝ) ≤ Z ^ B) →
    T.scale.val ≤ Z ^ L →
    ∀ o : OuterIndex K S D T,
      FirstLocalizedEnergy.radialScale K S D T o ^ epsilon *
        (Z ^ H) ^ massExponent ≤ constant * Z ^ pi

theorem exists_choice (lengthCap Hcap pi : ℝ)
    (hcap : 0 ≤ lengthCap) (hHcap : 0 ≤ Hcap) (hpi : 0 < pi) :
    Nonempty (Choice K S D lengthCap Hcap pi) := by
  obtain ⟨epsilon, massExponent, he, hm, A, hA, hb⟩ :=
    FirstActualErrorPowers.exists_uniform_weight_cost K S D
      lengthCap Hcap pi hcap hHcap hpi
  exact ⟨⟨epsilon, massExponent, A, he, hm, hA, hb⟩⟩

def choose (lengthCap Hcap pi : ℝ)
    (hcap : 0 ≤ lengthCap) (hHcap : 0 ≤ Hcap) (hpi : 0 < pi) :
    Choice K S D lengthCap Hcap pi :=
  Classical.choice (exists_choice K S D lengthCap Hcap pi hcap hHcap hpi)

end HeckeSkeleton.Moments.MOM_INV_STEP.UniformFirstWeightChoice

end
