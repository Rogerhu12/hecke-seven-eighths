import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodes

/-!
# Restrict the actual uniform canonical class

The fixed annular partition changes the declared column length by a
small, explicitly retained amount.  Its generated children can therefore
have stronger margins and smaller total/row caps than the common next
stage.  This file supplies that direction of restriction on the literal
node predicate, without altering its arithmetic data or radial test.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodes

open NumberField IsDedekindDomain
open HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
variable {D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K)))}
variable {Λ G : HeckeCharacter K} {slotCap : ℕ}
variable {Z A A' c c' z lo hi : ℝ} {σ : Type*}

theorem Node.Admissible.weaken (x : Node K S Γ Θ ψ σ)
    (hx : x.Admissible D Λ G slotCap Z A c z lo hi)
    (hA : A ≤ A') (hc : c' ≤ c) :
    x.Admissible D Λ G slotCap Z A' c' z lo hi :=
  { hx with
    total_le := hx.total_le.trans hA
    margins := ⟨hc.trans hx.margins.1, hc.trans hx.margins.2⟩ }

/-- A bound on the larger, weaker-margin class controls the original
class with the original energy, test, sectors, labels and puncture. -/
theorem uniformBound_restrict {eps R R' C : ℝ} {t : Finset (ℕ × ℕ)}
    (hA : A ≤ A') (hc : c' ≤ c) (hR : R ≤ R')
    (h : UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap
      Z A' c' z lo hi eps R' C t) :
    UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap
      Z A c z lo hi eps R C t := by
  intro σ x hx hr
  exact h x (Node.Admissible.weaken x hx hA hc) (hr.trans hR)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodes

end
