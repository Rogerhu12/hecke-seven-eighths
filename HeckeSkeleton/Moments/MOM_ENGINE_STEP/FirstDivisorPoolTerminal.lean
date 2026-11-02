import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorTerminalCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalTerminalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMaskCardinality

set_option linter.unusedSectionVars false

/-!
# Actual pooled terminal sums from the first-divisor profile atoms

The four genuine source tags are calibrated from their original
coefficient atoms and residual profile windows.  The canonical finite
zero and tail budgets are then estimated internally.  Their one pool
density, their first-divisor denominator, and their support-extraction
tuple multiplicity are all retained.

In particular the factor `τ(D²)^k` belonging to first common extraction
is not discarded when the three amplifier valuations contribute
`3^k`, `13^k` and `15^k`.  Its small-power bound follows from the original
norm window on `D`.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.CenteredMomentCounting MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

private theorem actual_terminal_pool_sum
    (d : FirstGaussPoolData C P ι) (f : PoolSourceTag P → ℝ)
    (H budget Mmax : ℝ) (hH : 0 ≤ H) (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hterm : ∀ b, f b ≤ H * poolTagNormCharge P b * Z ^ budget) :
    (4 / d.density) * (∑ b, d.tagWeight b * f b) ≤
      poolTerminalConstant K ell Mmax * H * Z ^ (budget + eps) := by
  sorry

variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

namespace ActualPoolStages

variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)

/-- Only original per-tag coefficient atoms and residual-profile
windows occur here.  Each window concerns the literal source at that
tag, including its original amplifier quotient and its original gate. -/
structure FirstDivisorWindows (S : Ideal (𝓞 K)) (slots : ℕ) (B : ℝ)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Lmax Nsave decay : ℝ) where
  atoms : ∀ b : PoolSourceTag P,
    FirstDivisorCoefficientAtoms (A := A) (σ := σ)
      (d.tagSource c b).columns (d.tagSource c b).coefficient S slots B
  profile : ∀ b : PoolSourceTag P,
    (s.tag b).ResidualTerminalWindows (atoms b) sTail sZero k Z Lmax Nsave decay

namespace FirstDivisorWindows

variable {s} {S : Ideal (𝓞 K)} {slots : ℕ} {B : ℝ}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}
variable (T : s.FirstDivisorWindows S slots B sTail sZero k Lmax Nsave decay)

def calibration : s.TerminalCalibration sTail sZero k Lmax Nsave decay where
  main := (T.profile (.inl ())).calibration
  one p := (T.profile (.inr (.inl p))).calibration
  six p := (T.profile (.inr (.inr (.inl p)))).calibration
  seven p := (T.profile (.inr (.inr (.inr p)))).calibration

@[simp] theorem calibration_tag (b : PoolSourceTag P) :
    T.calibration.tag b = (T.profile b).calibration := by
  sorry

/-- These are the exact multiplicities produced by
`SecondTailWindows.ofSupportResidual` and `ofSupportAmplifier`.
The common ideal is the one extracted from the original occurrences. -/
structure OriginalTupleMultiplicities (D : Ideal (𝓞 K)) : Prop where
  main : (T.profile (.inl ())).windows.multiplicity = idealDivisorCount (D ^ 2) ^ k
  one : ∀ p : P.primes, (T.profile (.inr (.inl p))).windows.multiplicity =
    idealDivisorCount (D ^ 2) ^ k * 3 ^ k
  six : ∀ p : P.primes, (T.profile (.inr (.inr (.inl p)))).windows.multiplicity =
    idealDivisorCount (D ^ 2) ^ k * 13 ^ k
  seven : ∀ p : P.primes, (T.profile (.inr (.inr (.inr p)))).windows.multiplicity =
    idealDivisorCount (D ^ 2) ^ k * 15 ^ k

theorem OriginalTupleMultiplicities.tag_le {D : Ideal (𝓞 K)}
    (Q : T.OriginalTupleMultiplicities D) (b : PoolSourceTag P) :
    (T.profile b).windows.multiplicity ≤ idealDivisorCount (D ^ 2) ^ k * 15 ^ k := by
  sorry

def zeroExponent (b : PoolSourceTag P) : ℝ :=
  (T.profile b).zeroProfileExponent + (T.profile b).zeroColumnExponent +
    (T.profile b).inverseRadiusExponent + (T.profile b).productExponent / 2

private theorem zeroAmplitude_le_raw
    (b : PoolSourceTag P) (profileConstant : ℝ) (hprofile : 0 ≤ profileConstant)
    (maskCap : ℕ) (hmask : (s.tag b).mask.card ≤ maskCap)
    (hraw : (T.profile b).zeroProfileConstant ≤ profileConstant * poolTagNormCharge P b) :
    (T.calibration.tag b).zeroAmplitude ≤
      ((B ^ slots * profileConstant * (2 : ℝ) ^ maskCap / (Ideal.absNorm S : ℝ)) *
        poolTagNormCharge P b) * Z ^ T.zeroExponent b := by
  sorry

/-- The full canonical zero budget, derived from original per-profile
windows, with the true common-extraction and amplifier tuple fibres. -/
theorem zeroBudget_le_original_profiles
    (D : Ideal (𝓞 K)) (Q : T.OriginalTupleMultiplicities D)
    (ε Czero profileConstant budget Mmax : ℝ) (fiberCap maskCap : ℕ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profileConstant)
    (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hfiber : ∀ b, (s.tag b).fiber ≤ fiberCap)
    (hmask : ∀ b, (s.tag b).mask.card ≤ maskCap)
    (hraw : ∀ b, (T.profile b).zeroProfileConstant ≤ profileConstant * poolTagNormCharge P b)
    (hbudget : ∀ b, T.zeroExponent b + (T.profile b).productExponent * ε ≤ budget) :
    T.calibration.zeroBudget ε Czero ≤
      poolTerminalConstant K ell Mmax *
        ((fiberCap : ℝ) * (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) * Czero *
          (B ^ slots * profileConstant * (2 : ℝ) ^ maskCap / (Ideal.absNorm S : ℝ))) *
        Z ^ (budget + eps) := by
  sorry

/-- The tail uses the same actual first-divisor atoms and tuple fibres.
Only the original residual-profile constant and numerical decay window
are used, not a bound on the resulting tail amplitude. -/
theorem tailBudget_le_original_profiles
    (D : Ideal (𝓞 K)) (Q : T.OriginalTupleMultiplicities D)
    (Cerror profileConstant budget Mmax : ℝ) (fiberCap : ℕ)
    (profileExponent : PoolSourceTag P → ℝ)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profileConstant)
    (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hfiber : ∀ b, (s.tag b).fiber ≤ fiberCap)
    (hraw : ∀ b, (T.profile b).tailProfileConstant ≤
      profileConstant * poolTagNormCharge P b * Z ^ profileExponent b)
    (hbudget : ∀ b, profileExponent b - Nsave ≤ budget) :
    T.calibration.tailBudget Cerror ≤
      poolTerminalConstant K ell Mmax *
        ((fiberCap : ℝ) * (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) * Cerror *
          (B ^ slots * profileConstant / (Ideal.absNorm S : ℝ))) * Z ^ (budget + eps) := by
  sorry

end FirstDivisorWindows
end ActualPoolStages

/-- The actual common-support factor, with its original squared ideal,
has a uniform small-power cost.  Constants precede every source and
scale; the only window is the original norm of the common ideal. -/
theorem first_terminal_tuple_multiplicity_subpower (k : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Ccount : ℝ, 0 < Ccount ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ D : Ideal (𝓞 K), (Ideal.absNorm D : ℝ) ≤ Z ^ B →
        (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) ≤
          (Ccount * (15 ^ k : ℕ)) * Z ^ ε := by
  sorry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.FirstDivisorWindows.zeroBudget_le_original_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.FirstDivisorWindows.tailBudget_le_original_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.first_terminal_tuple_multiplicity_subpower
