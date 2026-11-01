import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EffectiveChildSupport

/-!
# Finite effective supports of the same complete arithmetic summands

The original quotient-support constructions use a concrete finite set.
The calibrated-source interface states the equivalent nonzero-summand
property. Both views retain the complete arithmetic coefficient, smooth
profile and mask. The equivalences below transport the existing finite
support proofs without changing a profile, carrier, character or norm.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {ω ψ : HeckeCharacter F}

/-- Nonzero unnormalized plain summands of the original child. -/
def effectivePlainSupport (d : MomentData F ω ψ) (W : IdealTest F)
    (u : NonzeroIdeal F) (N t : ℝ) : Finset (NonzeroIdeal F) :=
  (W.support u t N).filter fun I =>
    heckeIdealCoefficient F (d.plainBackground * d.rowCharacter u) I *
      maskValue d u I.val ≠ 0

/-- Nonzero unnormalized prime summands of one original child slot. -/
def effectivePrimeSupport (d : MomentData F ω ψ) (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal F) (Z t : ℝ) : Finset (HeightOneSpectrum (𝓞 F)) :=
  ((d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length)).filter fun p =>
    primeCoefficient F (d.rowCharacter u * d.slotCoefficient i) p *
      maskValue d u p.asIdeal ≠ 0

@[simp] theorem mem_effectivePlainSupport (d : MomentData F ω ψ) (W : IdealTest F)
    (u I : NonzeroIdeal F) (N t : ℝ) :
    I ∈ effectivePlainSupport d W u N t ↔
      W.profile u t (idealNorm F I / N) ≠ 0 ∧
        heckeIdealCoefficient F (d.plainBackground * d.rowCharacter u) I *
          maskValue d u I.val ≠ 0 := by
  simp only [effectivePlainSupport, Finset.mem_filter, W.support_spec]

@[simp] theorem mem_effectivePrimeSupport (d : MomentData F ω ψ)
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal F) (Z t : ℝ)
    (p : HeightOneSpectrum (𝓞 F)) :
    p ∈ effectivePrimeSupport d i u Z t ↔
      (d.geometry.slots i).profile t
          ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) ≠ 0 ∧
        primeCoefficient F (d.rowCharacter u * d.slotCoefficient i) p *
          maskValue d u p.asIdeal ≠ 0 := by
  simp only [effectivePrimeSupport, Finset.mem_filter, (d.geometry.slots i).support_spec]

theorem effectivePlainSupport_subset_profile (d : MomentData F ω ψ) (W : IdealTest F)
    (u : NonzeroIdeal F) (N t : ℝ) :
    effectivePlainSupport d W u N t ⊆ W.support u t N :=
  Finset.filter_subset _ _

theorem effectivePrimeSupport_subset_profile (d : MomentData F ω ψ)
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal F) (Z t : ℝ) :
    effectivePrimeSupport d i u Z t ⊆
      (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length) :=
  Finset.filter_subset _ _

theorem effectivePlainSupport_commonMask (d : MomentData F ω ψ) (W : IdealTest F)
    (u I : NonzeroIdeal F) (N t : ℝ)
    (hI : I ∈ effectivePlainSupport d W u N t) :
    d.commonMask u I.val = true := by
  have hm : maskValue d u I.val ≠ 0 :=
    (mul_ne_zero_iff.mp ((mem_effectivePlainSupport d W u I N t).mp hI).2).2
  by_contra h
  exact hm (by simp [maskValue, h])

theorem effectivePrimeSupport_commonMask (d : MomentData F ω ψ)
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal F) (Z t : ℝ)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p ∈ effectivePrimeSupport d i u Z t) :
    d.commonMask u p.asIdeal = true := by
  have hm : maskValue d u p.asIdeal ≠ 0 :=
    (mul_ne_zero_iff.mp ((mem_effectivePrimeSupport d i u Z t p).mp hp).2).2
  by_contra h
  exact hm (by simp [maskValue, h])


/-- The concrete finite support and the nonzero-summand property have
exactly the same coverage requirement. -/
theorem effectivePlainSupport_subset_iff (d : MomentData F ω ψ) (W : IdealTest F)
    (u : NonzeroIdeal F) (N t : ℝ) (S : Finset (NonzeroIdeal F)) :
    effectivePlainSupport d W u N t ⊆ S ↔ EffectivePlainSupport d W u N t S := by
  constructor
  · intro hs I hi
    have hab := (mul_ne_zero_iff.mp hi).1
    have hm := (mul_ne_zero_iff.mp hi).2
    exact hs ((mem_effectivePlainSupport d W u I N t).mpr
      ⟨(mul_ne_zero_iff.mp hab).2, mul_ne_zero (mul_ne_zero_iff.mp hab).1 hm⟩)
  · intro hs I hi
    obtain ⟨hw, ha⟩ := (mem_effectivePlainSupport d W u I N t).mp hi
    exact hs I (mul_ne_zero (mul_ne_zero (mul_ne_zero_iff.mp ha).1 hw)
      (mul_ne_zero_iff.mp ha).2)

/-- The same equivalence keeps the actual row-dependent prime
coefficient and the original complete common mask. -/
theorem effectivePrimeSupport_subset_iff (d : MomentData F ω ψ)
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal F) (Z t : ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    effectivePrimeSupport d i u Z t ⊆ S ↔ EffectivePrimeSupport d i u Z t S := by
  constructor
  · intro hs p hp
    have hab := (mul_ne_zero_iff.mp hp).1
    have hm := (mul_ne_zero_iff.mp hp).2
    exact hs ((mem_effectivePrimeSupport d i u Z t p).mpr
      ⟨(mul_ne_zero_iff.mp hab).2, mul_ne_zero (mul_ne_zero_iff.mp hab).1 hm⟩)
  · intro hs p hp
    obtain ⟨hw, ha⟩ := (mem_effectivePrimeSupport d i u Z t p).mp hp
    exact hs p (mul_ne_zero (mul_ne_zero (mul_ne_zero_iff.mp ha).1 hw)
      (mul_ne_zero_iff.mp ha).2)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.effectivePlainSupport_subset_iff
#print axioms HeckeSkeleton.Moments.EngineStep.effectivePrimeSupport_subset_iff
