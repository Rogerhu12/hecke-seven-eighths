import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFourierWindows

/-!
# Raw and clipped windows on the same actual allocated data

The raw constructor uses the computed original Schwartz representatives
and their individual estimates. It fills the profile-window fields of
the literal `CanonicalLiteralAllocatedData.data`; no calibrated data
or finished child window is an input. The unchanged inverse test is
read from the original parent's window.

Clipping is justified by one genuinely nonzero member of this same
family. If the family is zero at every Fourier parameter the existing
zero branch applies instead. The annular dilation constant is explicit
and is put into the common radius before any slot removal.
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

namespace CanonicalLiteralAllocatedData

variable {K : Type} [Field K] [NumberField K] {k : ℕ}
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

local notation "originalData" =>
  data P R W allocation F parent oldMoving correction hcorr C p
    leftMultiplicity rightMultiplicity pattern sector remaining extra m q
    parent.inverseTest index rectangle firstSign negative

variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ}
variable (E : W.SchwartzModel window)
variable (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
variable (s : Finset (ℕ × ℕ)) {bound : ℝ}

/-- The displayed estimates are on the computed original
representatives. `SchwartzModel.secondInput_*_seminorm_le`, its seed
bound, and its exact atlas/balance transports construct them. -/
def originalRawWindow
    (original : RawProfileWindow rowDomain heightDomain window s parent bound)
    (hbound : 0 ≤ bound)
    (hleft : ∀ r, (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) ≤ bound)
    (hright : ∀ r, (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) ≤ bound)
    (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ bound)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    RawProfileWindow rowDomain heightDomain window s (originalData ξ)
      (polynomialProfileRadius
        (bound * (1 + CanonicalLiteralFourierWindows.coefficient
          window hcompact hpositive firstSign s)) (s.sup Prod.snd) (s.sup Prod.snd)
        (WithLp.ofLp ξ)) := by
  have hcoefficient := CanonicalLiteralFourierWindows.coefficient_nonneg
    window hcompact hpositive firstSign s
  have hsize := CanonicalLiteralFourierWindows.bound_le_radius
    hcoefficient hbound (s.sup Prod.snd) ξ
  have hfourier := CanonicalLiteralFourierWindows.fourier_bound
    hcoefficient hbound (s.sup Prod.snd) ξ
  have hnonneg : 0 ≤ CanonicalLiteralFourierWindows.coefficient
      window hcompact hpositive firstSign s * (1 + ‖ξ‖) ^ (s.sup Prod.snd) :=
    mul_nonneg hcoefficient (pow_nonneg (by positivity) _)
  refine
    { inverseRep := original.inverseRep
      leftRep := fun _ _ => E.leftFourierRep hcompact hpositive firstSign negative rectangle ξ
      rightRep := fun _ _ => E.rightFourierRep hcompact hpositive firstSign negative rectangle ξ
      primeRep := fun j _ => E.slotFourierRep hcompact hpositive firstSign negative
        (SlotRestriction.index allocation.keep j) ξ
      inverse_eq := original.inverse_eq
      left_eq := fun u t y => E.leftFourierRep_eq
        hcompact hpositive firstSign negative rectangle ξ u t y
      right_eq := fun u t y => E.rightFourierRep_eq
        hcompact hpositive firstSign negative rectangle ξ u t y
      prime_eq := fun j t y => E.slotFourierRep_eq
        hcompact hpositive firstSign negative (SlotRestriction.index allocation.keep j) ξ t y
      inverse_support := original.inverse_support
      left_support := fun _ _ _ _ _ hy =>
        E.leftFourierRep_support hcompact hpositive firstSign negative rectangle ξ
          (subset_tsupport _ hy)
      right_support := fun _ _ _ _ _ hy =>
        E.rightFourierRep_support hcompact hpositive firstSign negative rectangle ξ
          (subset_tsupport _ hy)
      prime_support := fun j _ _ _ hy => E.slotFourierRep_support
        hcompact hpositive firstSign negative (SlotRestriction.index allocation.keep j) ξ
          (subset_tsupport _ hy)
      inverse_bound := fun u hu t ht => (original.inverse_bound u hu t ht).trans hsize
      left_bound := fun _ _ _ _ =>
        (E.leftFourierRep_bound hcompact hpositive firstSign negative rectangle ξ s).trans
          ((mul_le_mul_of_nonneg_left (hleft rectangle) hnonneg).trans hfourier)
      right_bound := fun _ _ _ _ =>
        (E.rightFourierRep_bound hcompact hpositive firstSign negative rectangle ξ s).trans
          ((mul_le_mul_of_nonneg_left (hright rectangle) hnonneg).trans hfourier)
      prime_bound := fun j _ _ =>
        (E.slotFourierRep_bound hcompact hpositive firstSign negative
          (SlotRestriction.index allocation.keep j) ξ s).trans
            ((mul_le_mul_of_nonneg_left
              (hslot (SlotRestriction.index allocation.keep j)) hnonneg).trans hfourier) }

end CanonicalLiteralAllocatedData

namespace CanonicalLiteralFourierWindows

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window window' : Set ℝ} {s : Finset (ℕ × ℕ)}

def enlargeWindow {d : MomentData K ω ψ} {bound : ℝ}
    (w : RawProfileWindow rowDomain heightDomain window s d bound)
    (hwindow : window ⊆ window') :
    RawProfileWindow rowDomain heightDomain window' s d bound :=
  { w with
    inverse_support := fun u hu t ht => (w.inverse_support u hu t ht).trans hwindow
    left_support := fun u hu t ht => (w.left_support u hu t ht).trans hwindow
    right_support := fun u hu t ht => (w.right_support u hu t ht).trans hwindow
    prime_support := fun j t ht => (w.prime_support j t ht).trans hwindow }

/-- A family of already constructed raw representatives is clipped
with one actual nonzero member. The radius and both support windows
are enlarged by explicit constants independent of the Fourier point. -/
def rawClippedWindows
    (family : WithLp 2 (ℝ × ℝ) → MomentData K ω ψ) (parameters : RealParameters)
    (Z time : ℝ) (hZ : 1 < Z) (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (s : Finset (ℕ × ℕ)) (B : ℝ) (hB : 0 ≤ B) (J : ℕ)
    (raw : ∀ ξ, RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s (family ξ)
      (polynomialProfileRadius B J J (WithLp.ofLp ξ)))
    (ξ₀ : WithLp 2 (ℝ × ℝ))
    (hrows : ∀ u ∈ pairedRows (family ξ₀) parameters Z, u ∈ rowDomain)
    (ht : time ∈ heightDomain) (hne : pairedEnergy (family ξ₀) parameters Z time ≠ 0)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    RawProfileWindow rowDomain heightDomain (Set.Icc (lo / hi) hi) s (family ξ)
      (polynomialProfileRadius (CanonicalLogProfiles.clippingCoefficient hi s * (1 + B))
        J J (WithLp.ofLp ξ)) ×
    RawProfileWindow rowDomain heightDomain (Set.Icc (lo / hi) hi) s
      (clipPlainData (family ξ) parameters Z (zero_lt_one.trans hZ))
      (polynomialProfileRadius (CanonicalLogProfiles.clippingCoefficient hi s * (1 + B))
        J J (WithLp.ofLp ξ)) := by
  let Cclip := CanonicalLogProfiles.clippingCoefficient hi s
  have hC : 1 ≤ Cclip := CanonicalLogProfiles.clippingCoefficient_one_le hi hhi s
  have hclip := CanonicalLogProfiles.clipping_factors_le_of_window_nonzero
    (family ξ₀) parameters Z time lo hi hZ hhi s
    (polynomialProfileRadius B J J (WithLp.ofLp ξ₀)) (raw ξ₀) hrows ht hne
  have hrawpos : 0 ≤ polynomialProfileRadius B J J (WithLp.ofLp ξ) :=
    (polynomialProfileRadius_pos B hB J J (WithLp.ofLp ξ)).le
  let clipped := CanonicalLogProfiles.clipRawWindow (family ξ) parameters Z hZ.le lo hi
    hlo hhi s hrawpos (raw ξ) hclip.1 hclip.2
  have henvelope : Cclip * polynomialProfileRadius B J J (WithLp.ofLp ξ) ≤
      polynomialProfileRadius (Cclip * (1 + B)) J J (WithLp.ofLp ξ) := by
    have h := mul_le_mul_of_nonneg_left
      (polynomialProfileRadius_le B J J (WithLp.ofLp ξ)) (zero_le_one.trans hC)
    unfold polynomialProfileRadius at h ⊢
    nlinarith
  have hraw : polynomialProfileRadius B J J (WithLp.ofLp ξ) ≤
      polynomialProfileRadius (Cclip * (1 + B)) J J (WithLp.ofLp ξ) :=
    (le_mul_of_one_le_left hrawpos hC).trans henvelope
  exact ⟨(enlargeWindow (raw ξ)
    (CanonicalLogProfiles.originalAnnulus_subset_clipped lo hi hlo hhi)).mono hraw,
    clipped.mono henvelope⟩

end CanonicalLiteralFourierWindows
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.originalRawWindow
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFourierWindows.rawClippedWindows
