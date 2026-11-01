import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralBalancedSchwartz
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSelectedRawWindow
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllSideClipping

/-!
# The original prime window through the literal construction

The prime profiles retain their original function support. Real-power
multipliers and Fourier phases cannot create a nonzero value where the
original profile vanishes. The actual extraction and atlas operations
select the original occurrences; plain balancing and clipping leave
the prime profiles unchanged. In particular the original open prime
window `(1, 2)` is available to the full-kappa single-slot estimate,
even though the common plain-profile window is enlarged by clipping.
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

namespace CanonicalLiteralSchwartzProfiles

theorem powerSchwartz_support_subset (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (c : ℂ) (exponent : ℝ)
    (φ : 𝓢(ℝ, ℂ)) (hsupport : tsupport φ ⊆ window) :
    Function.support (powerSchwartz window hcompact hpositive c exponent φ hsupport) ⊆
      Function.support φ := by
  intro y hy
  change φ y ≠ 0
  intro hz
  apply hy
  rw [powerSchwartz_apply, hz, zero_mul, mul_zero]

end CanonicalLiteralSchwartzProfiles

namespace CanonicalLiteralFourierWindows

theorem atom_support {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (p : CanonicalLogProfiles.Atom V) (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (ξ : V) (φ : 𝓢(ℝ, ℂ))
    (hsupport : tsupport φ ⊆ window) :
    Function.support (p.schwartz window hcompact hpositive ξ φ hsupport) ⊆
      Function.support φ := by
  intro y hy
  change φ y ≠ 0
  intro hz
  apply hy
  rw [CanonicalLogProfiles.Atom.schwartz_apply, hz, zero_mul]

end CanonicalLiteralFourierWindows

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
variable {window target : Set ℝ} (E : W.SchwartzModel window)

theorem extract_prime_support {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target) :
    ∀ j, Function.support ((E.extract b).slot j) ⊆ target :=
  fun j => hprime (SlotRestriction.index b.keep j)

theorem onAtlas_prime_support {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target) :
    ∀ j, Function.support ((E.onAtlas T count).slot j) ⊆ target := by
  cases count
  exact hprime

theorem deleteMask_prime_support (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target) :
    ∀ j, Function.support ((E.deleteMask M).slot j) ⊆ target := hprime

theorem scale_prime_support (c : ℂ)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target) :
    ∀ j, Function.support ((E.scale c).slot j) ⊆ target := hprime

theorem balancePlain_prime_support (c : Bool → ℝ)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target) :
    ∀ j, Function.support ((E.balancePlain c).slot j) ⊆ target := hprime

theorem slotFourierRep_support_subset (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (firstSign : ℝ) (negative : Bool)
    (j : Fin k) (ξ : WithLp 2 (ℝ × ℝ)) :
    Function.support (E.slotFourierRep hcompact hpositive firstSign negative j ξ) ⊆
      Function.support (E.slot j) :=
  CanonicalLiteralFourierWindows.atom_support _ window hcompact hpositive ξ _
    (E.slot_support j)

variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement)
variable (δ₁ δ₂ : ℝ)

theorem secondInput_prime_support (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target) :
    ∀ j, Function.support
      ((E.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).slot j)
      ⊆ target := by
  intro j
  exact (CanonicalLiteralSchwartzProfiles.powerSchwartz_support_subset
    window hcompact hpositive _ _ (E.slot (SlotRestriction.index b.keep j))
      (E.slot_support (SlotRestriction.index b.keep j))).trans
    (hprime (SlotRestriction.index b.keep j))

/-- This is the representative used after moving the actual scalar
to the row weight and balancing the two original plain factors. Its
prime profile is the same real-power transform as before. -/
theorem scalarFreeBalancedSecondInput_prime_support (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target) :
    ∀ j, Function.support
      ((E.scalarFreeBalancedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).slot j)
      ⊆ target :=
  E.secondInput_prime_support (σ := σ) b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive hprime

end CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel

namespace CanonicalLiteralAllocatedData

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (allocation : ActualColumnAllocation K k)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (leftMultiplicity rightMultiplicity : ι → ℕ) (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window target : Set ℝ}
variable (E : W.SchwartzModel window)
variable (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
variable (s : Finset (ℕ × ℕ)) {bound : ℝ}

/-- The returned raw window uses the Fourier transform of the same
retained slot. Taking `target = Set.Ioo 1 2` supplies precisely the
prime-support field of `FullKappaProfileInput`. -/
theorem selectedRawWindow_prime_support
    (original : RawProfileWindow rowDomain heightDomain window s parent bound)
    (hbound : 0 ≤ bound)
    (hleft : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.left rectangle) ≤ bound)
    (hright : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.right rectangle) ≤ bound)
    (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ bound)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target)
    (ξ : WithLp 2 (ℝ × ℝ)) (j : Fin allocation.keep.card) (t : ℝ) :
    Function.support
      ((selectedRawWindow P R W allocation F parent oldMoving correction hcorr C p
        leftMultiplicity rightMultiplicity pattern sector remaining extra m q index
        rectangle firstSign negative E hcompact hpositive s original hbound hleft hright hslot ξ)
        .primeRep j t) ⊆ target :=
  (E.slotFourierRep_support_subset hcompact hpositive firstSign negative
    (SlotRestriction.index allocation.keep j) ξ).trans
    (hprime (SlotRestriction.index allocation.keep j))

end CanonicalLiteralAllocatedData

namespace CanonicalLiteralAllSideClipping

variable {ω ψ : HeckeCharacter K}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain target : Set ℝ}

/-- Neither the broad window nor either clipping dilation changes
the returned prime representative. This applies to every rectangle,
including identically zero rectangles. -/
theorem familyWindows_prime_support
    (family : WithLp 2 (ℝ × ℝ) → MomentData K ω ψ) (parameters : RealParameters)
    (Z : ℝ) (hZ : 1 ≤ Z) (lo hi : ℝ) (hlo : 0 < lo)
    (s : Finset (ℕ × ℕ)) (B : ℝ) (hB : 0 ≤ B) (J : ℕ)
    (raw : ∀ ξ, RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s (family ξ)
      (polynomialProfileRadius B J J (WithLp.ofLp ξ)))
    (hprime : ∀ ξ j t, Function.support ((raw ξ).primeRep j t) ⊆ target)
    (ξ : WithLp 2 (ℝ × ℝ)) (j : Fin (family ξ).geometry.slotCount) (t : ℝ) :
    Function.support
      ((familyWindows family parameters Z hZ lo hi hlo s B hB J raw ξ).1.primeRep j t) ⊆ target ∧
    Function.support
      ((familyWindows family parameters Z hZ lo hi hlo s B hB J raw ξ).2.primeRep j t) ⊆ target :=
  ⟨hprime ξ j t, hprime ξ j t⟩

end CanonicalLiteralAllSideClipping
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.scalarFreeBalancedSecondInput_prime_support
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.selectedRawWindow_prime_support
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllSideClipping.familyWindows_prime_support
