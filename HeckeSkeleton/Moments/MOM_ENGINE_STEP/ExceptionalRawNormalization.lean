import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalContribution
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationScalarNorm

/-!
# Exceptional raw normalization from actual frozen denominators

The raw mass in the exceptional contribution theorem is bounded here
using only individual coefficient/profile windows.  The frozen scalar
is estimated by its proved inverse ideal norm, and every live prime is
counted by the ordinary ideal ball.  This is a constructor for the raw
normalization premise, not an assumed exceptional energy estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.CenteredMomentCounting

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- A live slot pays its actual central square-root scale. -/
theorem sourcePrimeTerm_norm_le_profile
    (C : A.GeneralArithmeticContext σ η hS)
    (χ θ : HeckeCharacter F) (M : Ideal (𝓞 F) →* ℂ)
    (g h' : A.R) (w : HeightOneSpectrum (𝓞 F) → ℂ) (N B : ℝ)
    (p : HeightOneSpectrum (𝓞 F))
    (hcoefficient : ‖sourcePrimeCoefficient χ θ M p‖ ≤ 1) (hw : ‖w p‖ ≤ B) :
    ‖sourcePrimeTerm (σ := σ) χ θ M g h' w N p‖ ≤ B / Real.sqrt N := by
  have hc : ‖sourcePrimeCoefficient χ θ M p *
      actualIdealResidue (A := A) (σ := σ) p.asIdeal (g * h')‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul hcoefficient (actualIdealResidue_norm_le_one C _ _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hp : ‖sourcePrimeCoefficient χ θ M p *
      actualIdealResidue (A := A) (σ := σ) p.asIdeal (g * h') * w p‖ ≤ B := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by simpa using hw)
  calc
    _ = (Real.sqrt N)⁻¹ * ‖sourcePrimeCoefficient χ θ M p *
        actualIdealResidue (A := A) (σ := σ) p.asIdeal (g * h') * w p‖ := by
      simp only [sourcePrimeTerm, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ (Real.sqrt N)⁻¹ * B :=
      mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = _ := by ring

namespace AllocatedExceptionalSource

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Ψ : Ideal (𝓞 F) →* ℂ} {W₁ W₂ : ℝ → ℂ} {g h' : A.R} {k : ℕ}

/-- Each factor on the right is an original scalar, an actual selected
ideal norm, or an individual compact-profile envelope. No frozen-scalar,
slot-polynomial, raw-mass or row-energy bound is an input. -/
theorem rawMass_le_annular_profile_windows
    (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k)
    (C : A.GeneralArithmeticContext σ η hS) (hZ : 0 < s.Zslot)
    (annulus profile : Fin k → ℝ)
    (hannulus : ∀ i, 0 ≤ annulus i) (hprofile : ∀ i, 0 ≤ profile i)
    (hplain₁ : ‖sourcePlainCoefficient s.characters.plain s.characters.plainTwist
      s.characters.mask (s.allocation.plainDivisor 0)‖ ≤ 1)
    (hplain₂ : ‖sourcePlainCoefficient s.characters.plain s.characters.plainTwist
      s.characters.mask (s.allocation.plainDivisor (Fin.succ 0))‖ ≤ 1)
    (hfrozenCoefficient : ∀ i ∈ Finset.univ \ s.allocation.keep,
      ‖sourcePrimeCoefficient (s.characters.slot i) (s.characters.slotTwist i)
        s.characters.mask (s.allocation.witness.2 i)‖ ≤ 1)
    (hfrozenAnnulus : ∀ i ∈ Finset.univ \ s.allocation.keep,
      (Ideal.absNorm (s.allocation.witness.2 i).asIdeal : ℝ) ≤
        annulus i * s.Zslot ^ s.length i)
    (hfrozenProfile : ∀ i ∈ Finset.univ \ s.allocation.keep,
      ‖s.w i (s.allocation.witness.2 i)‖ ≤ profile i)
    (hliveCutoff : ∀ j : Fin s.allocation.keep.card,
      1 ≤ annulus (SlotRestriction.index s.allocation.keep j) *
        s.Zslot ^ s.length (SlotRestriction.index s.allocation.keep j))
    (hliveAnnulus : ∀ j, ∀ p ∈ s.allocation.childSlots j,
      (Ideal.absNorm p.asIdeal : ℝ) ≤ annulus (SlotRestriction.index s.allocation.keep j) *
        s.Zslot ^ s.length (SlotRestriction.index s.allocation.keep j))
    (hliveCoefficient : ∀ j, ∀ p ∈ s.allocation.childSlots j,
      ‖sourcePrimeCoefficient ((s.characters.restrictSlots s.allocation.keep).slot j)
        ((s.characters.restrictSlots s.allocation.keep).slotTwist j)
        (s.characters.restrictSlots s.allocation.keep).mask p‖ ≤ 1)
    (hliveProfile : ∀ j, ∀ p ∈ s.allocation.childSlots j,
      ‖s.w (SlotRestriction.index s.allocation.keep j) p‖ ≤
        profile (SlotRestriction.index s.allocation.keep j)) :
    s.rawMass ≤
      Real.sqrt ((∏ i ∈ Finset.univ \ s.allocation.keep, annulus i * (profile i) ^ 2) /
        (Ideal.absNorm s.allocation.frozenIdeal : ℝ)) * Real.sqrt s.product *
      ∏ j : Fin s.allocation.keep.card,
        (idealCountConstant F *
          (annulus (SlotRestriction.index s.allocation.keep j) *
            s.Zslot ^ s.length (SlotRestriction.index s.allocation.keep j))) *
          (profile (SlotRestriction.index s.allocation.keep j) /
            Real.sqrt (s.Zslot ^ s.length (SlotRestriction.index s.allocation.keep j))) := by
  have hs := s.allocation.scalar_norm_sq_le_frozen_norm C s.characters g h' s.Zslot hZ
    s.length s.w annulus (fun i => (profile i) ^ 2) hplain₁ hplain₂ hfrozenCoefficient
    hfrozenAnnulus
    (fun i hi => pow_le_pow_left₀ (norm_nonneg _) (hfrozenProfile i hi) 2)
    hannulus (fun i => sq_nonneg _)
  have hscalar : ‖s.allocation.scalar (σ := σ) s.characters g h' s.Zslot s.length s.w‖ ≤
      Real.sqrt ((∏ i ∈ Finset.univ \ s.allocation.keep, annulus i * (profile i) ^ 2) /
        (Ideal.absNorm s.allocation.frozenIdeal : ℝ)) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (div_nonneg
      (Finset.prod_nonneg (fun i _ => mul_nonneg (hannulus i) (sq_nonneg _)))
      (Nat.cast_nonneg _))]
    exact hs
  apply s.rawMass_le_prime_windows _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hscalar le_rfl
    (fun j => annulus (SlotRestriction.index s.allocation.keep j) *
      s.Zslot ^ s.length (SlotRestriction.index s.allocation.keep j))
    (fun j => profile (SlotRestriction.index s.allocation.keep j) /
      Real.sqrt (s.Zslot ^ s.length (SlotRestriction.index s.allocation.keep j)))
    hliveCutoff
    (fun j => div_nonneg (hprofile _) (Real.sqrt_nonneg _)) hliveAnnulus
  intro j p hp
  exact sourcePrimeTerm_norm_le_profile C _ _ _ _ _ _ _ _ _
    (hliveCoefficient j p hp) (hliveProfile j p hp)

end AllocatedExceptionalSource
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.sourcePrimeTerm_norm_le_profile
#print axioms HeckeSkeleton.Moments.EngineStep.AllocatedExceptionalSource.rawMass_le_annular_profile_windows
