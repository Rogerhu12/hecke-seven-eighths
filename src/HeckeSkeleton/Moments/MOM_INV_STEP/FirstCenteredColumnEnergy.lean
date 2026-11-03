import HeckeSkeleton.Moments.MOM_INV_STEP.FirstColumnEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredMellinEnergy

/-!
# The literal first source column at a fixed production center

The source still has its actual quotient scale. Its positive bound uses
one family whose complete pool, norm length and test are fixed throughout
the extracted-product box. The two scale equations below are geometric
identities and the box is an ordinary norm annulus.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredColumnEnergy

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalBlock CanonicalNormPools
  FirstOverlapColumns FirstColumnAssembly FirstColumnEnergy FirstCenteredMellinEnergy
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "E" => CanonicalIdealRow.exteriorMonoid K S
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ : Type*}

include hallowed hΓ in
theorem sourceColumn_sq_le_centered_energy (C : ColumnData K S σ)
    (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
    (hGunramified : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K G p)
    (X : {r : ℝ // 0 < r}) (hCX : C.base ^ C.length = X.val)
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (f z : E) (d : OS) (ξ : Sector)
    (e : Ext) (he : Squarefree e.val.val) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (hCW : C.cutoff = W) (τ : ℝ)
    (hprime : ∀ i ∈ C.slots, ∀ p ∈ C.primeLists i, Prime p)
    (vcenter U : ℝ) (hZ : 1 < C.base) (hc : 0 < vcenter) (hU : 0 < U)
    (hvlo : vcenter ≤ extractedHeight K S r₁ r₂ b₁ b₂ side e)
    (hvhi : extractedHeight K S r₁ r₂ b₁ b₂ side e ≤ 2 * vcenter)
    (hcenter : X.val = vcenter * U) :
    ‖sourceColumn K S D Γ C G X r₁ r₂ b₁ b₂ side f z d ξ e τ‖ ^ 2 ≤
      ((height K Sset e)⁻¹ * (C.slots.powerset.card : ℝ)) *
        ((U ^ (-(1 / 2 : ℝ))) ^ 2 * (∫ t : ℝ, ‖MellinSeparation.density W hW t‖)) *
        ∑ J ∈ C.slots.powerset, ‖assignedMark K S C r₁ r₂ b₁ b₂ side e J‖ ^ 2 *
          ∫ t : ℝ, ‖MellinSeparation.density W hW t‖ *
            ‖DivisorInverseColumn.column K S Γ D
              (FirstCenteredFamily.family K S C Θ ψ G hν hG J U (-(1 / 2 : ℝ)) (t + τ))
              (firstTriple K S r₁ r₂ b₁ b₂ e) (retainedLabel K S r₁ r₂ b₁ b₂).val.val d
              ((firstRow K S r₁ r₂ b₁ b₂ f z).val.val,ξ)‖ ^ 2 := by
  have hs := sourceColumn_sq_le_branches K S D Γ hallowed C G hGunramified X hCX
    r₁ r₂ b₁ b₂ side f z d ξ e he W hCW τ hprime
  have hcost : 0 ≤ (height K Sset e)⁻¹ * (C.slots.powerset.card : ℝ) :=
    mul_nonneg (inv_nonneg.mpr (height_pos K Sset e).le) (Nat.cast_nonneg _)
  apply hs.trans
  calc
    _ ≤ ((height K Sset e)⁻¹ * (C.slots.powerset.card : ℝ)) *
        ∑ J ∈ C.slots.powerset, ‖assignedMark K S C r₁ r₂ b₁ b₂ side e J‖ ^ 2 *
          ((U ^ (-(1 / 2 : ℝ))) ^ 2 * ((∫ t : ℝ, ‖MellinSeparation.density W hW t‖) *
            ∫ t : ℝ, ‖MellinSeparation.density W hW t‖ *
              ‖DivisorInverseColumn.column K S Γ D
                (FirstCenteredFamily.family K S C Θ ψ G hν hG J U (-(1 / 2 : ℝ)) (t + τ))
                (firstTriple K S r₁ r₂ b₁ b₂ e) (retainedLabel K S r₁ r₂ b₁ b₂).val.val d
                ((firstRow K S r₁ r₂ b₁ b₂ f z).val.val,ξ)‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hcost
      apply Finset.sum_le_sum
      intro J hJ
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact residual_branch_sq_le K S Γ D C Θ ψ G hν hG J U (-(1 / 2 : ℝ))
        (firstTriple K S r₁ r₂ b₁ b₂ e) (retainedLabel K S r₁ r₂ b₁ b₂).val.val d hΓ
        W hW (CanonicalIdealRow.toExterior K S (firstRow K S r₁ r₂ b₁ b₂ f z),ξ)
        τ vcenter (extractedHeight K S r₁ r₂ b₁ b₂ side e) X.val
        (quotientScale K S X r₁ r₂ b₁ b₂ side e) hZ hc
        (quotientScale_pos K S X r₁ r₂ b₁ b₂ side e) hU hvlo hvhi
        (exact_source_scale K S X r₁ r₂ b₁ b₂ side e) hcenter
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J hJ
      ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredColumnEnergy

end

