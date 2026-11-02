import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFactorFreeSchwartz
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFullKappaInput

/-!
# The full-kappa profile input after the complete scalar extraction

This constructs the quantitative profile object from the original
parent representatives for the redistributed actual table.  The
chosen coefficient has the same explicit form as the existing literal
mass interface.  Its positive residual-factor term is an allowed
overestimate; the transformed representatives themselves satisfy the
stronger factor-free bound.

The original inverse profile, raw and clipped Fourier windows and
single-prime analytic input are then handled by the existing `ofLiteral`
constructor.  No finished child profile window is an input here.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralFullKappaInput

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace ComputedProfiles

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
variable {window : Set ℝ} {s : Finset (ℕ × ℕ)} {B : ℝ}

/-- These transports keep the same combined scalar through the second
extraction, instead of recomputing it from the second quotient scales. -/
def extractThenScale (c : ℂ) (T : ComputedProfiles (W.scale c) window s B)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    ComputedProfiles ((W.extract b).scale c) window s B :=
  (T.extract b).reprofile ((W.extract b).scale c)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

def onAtlasThenScale (c : ℂ) (T : ComputedProfiles (W.scale c) window s B)
    {A : SArithmeticData K} {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (atlas : SourceCartesianAtlas columns ideal) (count : k = atlas.slotCount) :
    ComputedProfiles ((W.onAtlas atlas count).scale c) window s B := by
  cases count
  exact (T.onAtlas atlas rfl).reprofile ((W.onAtlas atlas rfl).scale c)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

def deleteMaskThenScale (c : ℂ) (T : ComputedProfiles (W.scale c) window s B)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ComputedProfiles ((W.deleteMask M).scale c) window s B :=
  (T.deleteMask M).reprofile ((W.deleteMask M).scale c)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

/-- The existing normalization interface permits the identity plain
balance, with every representative and chosen coefficient unchanged. -/
def balanceOne (T : ComputedProfiles W window s B) :
    ComputedProfiles (W.balancePlain (fun _ => 1)) window s B :=
  T.reprofile (W.balancePlain (fun _ => 1))
    (fun r u t y => by change (W.left r).profile u t y * (1 : ℂ) = _; simp)
    (fun r u t y => by change (W.right r).profile u t y * (1 : ℂ)⁻¹ = _; simp)
    (fun _ _ _ => rfl)

end ComputedProfiles

section OriginalConstruction

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
variable {window : Set ℝ} (E : W.SchwartzModel window)
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

local notation "combinedScalar" =>
  d.secondInputScalar (σ := σ) b power firstElement δ₁ *
    (d.twoStageProfileFactor b δ₁ δ₂ : ℂ)
local notation "actualProfiles" =>
  (W.redistributedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale combinedScalar⁻¹

/-- The fixed original seminorms produce all three profile bounds.
The explicit larger coefficient preserves the existing same-family
mass interface while the complete scalar decay is paid separately. -/
def factorFree (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (s : Finset (ℕ × ℕ)) (B : ℝ) (hB : 0 ≤ B)
    (hleft : ∀ r, (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders s)).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) ≤ B)
    (hright : ∀ r, (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders s)).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) ≤ B)
    (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders s)).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ B)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ Set.Ioo (1 : ℝ) 2) :
    ComputedProfiles actualProfiles window s B := by
  let Cshape := CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
    (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders s)
  have hC : 0 ≤ Cshape := CanonicalLogProfiles.shapeCoefficient_nonneg
    window hcompact hpositive _ _
  have hboost (r : Bool) : Cshape * B ≤ B + B * Cshape *
      (1 + CanonicalLiteralBalancedSchwartz.factor d b δ₁ δ₂ r) := by
    calc
      _ = B * Cshape := mul_comm _ _
      _ ≤ B * Cshape * (1 + CanonicalLiteralBalancedSchwartz.factor d b δ₁ δ₂ r) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (mul_nonneg hB hC)
      _ ≤ _ := le_add_of_nonneg_left hB
  refine
    { model := E.factorFreeSecondInput (σ := σ) b P R
        power firstFixed poolFixed unitFixed firstElement poolElement unitElement
        hfirst hpool hunit δ₁ δ₂ hcompact hpositive
      bound := fun r => B + B * Cshape *
        (1 + CanonicalLiteralBalancedSchwartz.factor d b δ₁ δ₂ r)
      bound_nonneg := ?_
      original_bound := ?_
      left_bound := ?_
      right_bound := ?_
      slot_bound := ?_
      prime_window := E.factorFreeSecondInput_prime_support (σ := σ) b P R
        power firstFixed poolFixed unitFixed firstElement poolElement unitElement
        hfirst hpool hunit δ₁ δ₂ hcompact hpositive hprime }
  · intro r
    exact add_nonneg hB (mul_nonneg (mul_nonneg hB hC)
      (add_nonneg zero_le_one (Real.sqrt_nonneg _)))
  · intro r
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hB hC)
      (add_nonneg zero_le_one (Real.sqrt_nonneg _)))
  · intro r
    exact (E.factorFree_left_bound (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive
      r (CanonicalLogProfiles.sourceOrders s)).trans
      ((mul_le_mul_of_nonneg_left (hleft r) hC).trans (hboost r))
  · intro r
    exact (E.factorFree_right_bound (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive
      r (CanonicalLogProfiles.sourceOrders s)).trans
      ((mul_le_mul_of_nonneg_left (hright r) hC).trans (hboost r))
  · intro r j
    exact (E.factorFree_slot_bound (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive
      j (CanonicalLogProfiles.sourceOrders s)).trans
      ((mul_le_mul_of_nonneg_left (hslot (SlotRestriction.index b.keep j)) hC).trans (hboost r))

end OriginalConstruction
end CanonicalLiteralFullKappaInput

namespace CompleteMovingRowRecipe

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}

/-- Original-profile entrance for the exact redistributed table.
All representatives, finite-seminorm bounds and open prime support
are constructed from the original parent window. -/
def literalFactorFreeComputedProfiles
    (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
    (recipe : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
    (href : (data ξ).allowedRow reference)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ}
    (s : Finset (ℕ × ℕ)) (B : ℝ) (hB : 0 ≤ B)
    (original : RawProfileWindow rowDomain heightDomain window
      (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders s)) (data ξ) B)
    (hreference : reference ∈ rowDomain) (ht : t ∈ heightDomain)
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (hprime : ∀ j, Function.support (original.primeRep j t) ⊆ Set.Ioo (1 : ℝ) 2)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch
      (Q.literalOriginalAtoms ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₁
      (Q.literalOriginalAtoms ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₂
      (Q.literalOriginalAtoms ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots support)
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ) :
    let W := Q.literalOriginalProfileDataOfWindow ξ recipe a Z t Y₁ Y₂ centered
      hZ hY₁ hY₂ reference href original hreference ht hpositive
    let d := Q.literalOriginalAtoms ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    let combinedScalar := d.secondInputScalar (σ := σ) b power firstElement δ₁ *
      (d.twoStageProfileFactor b δ₁ δ₂ : ℂ)
    CanonicalLiteralFullKappaInput.ComputedProfiles
      ((W.redistributedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale combinedScalar⁻¹)
      window s B := by
  let E := Q.literalOriginalSchwartzModel ξ recipe a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ reference href original hreference ht hpositive hcompact.isClosed
  have hb := Q.literalOriginalSchwartzModel_bound ξ recipe a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ reference href original hreference ht hpositive hcompact.isClosed hB
  exact CanonicalLiteralFullKappaInput.factorFree (σ := σ) E b P R power firstFixed
    poolFixed unitFixed firstElement poolElement unitElement hfirst hpool hunit
    δ₁ δ₂ hcompact hpositive s B hB hb.1 hb.2.1 hb.2.2 hprime

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFullKappaInput.factorFree
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalFactorFreeComputedProfiles
