import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSecondCoveredSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridOrdinaryProduction

/-!
# The exact finite labels of the covered two-transform source

The main source and the three valuation sources form one finite tagged
family. Each tag retains its literal column type, coefficient, profile
chart, cover, original first Fourier location and local pool weight.
The downstream finite leaf carrier is the canonical carrier constructed
in `ActualGaussFiniteLeaves`; this file only supplies its pool tags.

These are definitions and exact finite sum identities on the original
source. No new branch cost or aggregate comparison is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

/-- One tag for the actual main source and one for each original prime
in each of the three genuine exceptional valuations. -/
abbrev PoolSourceTag (P : PowerScaleExteriorPool A bad Z ell eps) :=
  Unit ⊕ (P.primes ⊕ (P.primes ⊕ P.primes))

namespace FirstGaussPoolData

variable (d : FirstGaussPoolData C P ι)

def tagColumn : PoolSourceTag P → Type _
  | .inl _ => ι
  | .inr (.inl p) => d.valuationColumns p.val 1
  | .inr (.inr (.inl p)) => d.valuationColumns p.val 6
  | .inr (.inr (.inr p)) => d.valuationColumns p.val 7

def tagSource (c : ι → ℂ) : ∀ b : PoolSourceTag P, ActualGaussSource C (d.tagColumn b)
  | .inl _ => d.mainSource c
  | .inr (.inl p) => d.residualSource p.val 1 c
  | .inr (.inr (.inl p)) => d.residualSource p.val 6 c
  | .inr (.inr (.inr p)) => d.residualSource p.val 7 c

def tagWeight : PoolSourceTag P → ℝ
  | .inl _ => d.multiplicity
  | .inr (.inl p) => localErrorWeight p.val 1
  | .inr (.inr (.inl p)) => localErrorWeight p.val 6
  | .inr (.inr (.inr p)) => localErrorWeight p.val 7

theorem tagWeight_nonneg (b : PoolSourceTag P) : 0 ≤ d.tagWeight b := by
  rcases b with u | p | p | p
  · exact d.multiplicity_nonneg
  · exact localErrorWeight_nonneg p.val 1
  · exact localErrorWeight_nonneg p.val 6
  · exact localErrorWeight_nonneg p.val 7

def tagPoint {W : Type*} (x : ι → W) : ∀ b : PoolSourceTag P, d.tagColumn b → W
  | .inl _, i => x i
  | .inr (.inl _), i => x i.val
  | .inr (.inr (.inl _)), i => x i.val
  | .inr (.inr (.inr _)), i => x i.val

variable {d} in
def SourceCovers.tag {c : ι → ℂ} (B : d.SourceCovers c) :
    ∀ b : PoolSourceTag P,
      SourceCartesianCover (d.tagSource c b).columns (d.tagSource c b).ideal
  | .inl _ => B.main
  | .inr (.inl p) => B.residual p 1
  | .inr (.inr (.inl p)) => B.residual p 6
  | .inr (.inr (.inr p)) => B.residual p 7

end FirstGaussPoolData

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
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

namespace ActualPoolStages

variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}

def tag (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest) :
    ∀ b : PoolSourceTag P,
      ActualGaussStage (E := E) hΓ μv hDiff (d.tagSource c b) finiteTest
  | .inl _ => s.main
  | .inr (.inl p) => s.one p
  | .inr (.inr (.inl p)) => s.six p
  | .inr (.inr (.inr p)) => s.seven p

variable {s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest}
variable {B : d.SourceCovers c}

def CoverHybridPredicates.tag (r : s.CoverHybridPredicates B) :
    ∀ b : PoolSourceTag P, (s.tag b).CoverHybridPredicates (B.tag b) (B.tag b)
  | .inl _ => r.main
  | .inr (.inl p) => r.one p
  | .inr (.inr (.inl p)) => r.six p
  | .inr (.inr (.inr p)) => r.seven p

namespace TerminalCalibration

variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def tag (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay) :
    ∀ b : PoolSourceTag P, (s.tag b).TerminalCalibration sTail sZero k Z Lmax Nsave decay
  | .inl _ => T.main
  | .inr (.inl p) => T.one p
  | .inr (.inr (.inl p)) => T.six p
  | .inr (.inr (.inr p)) => T.seven p

theorem coverHybridPhaseCost_eq_sum
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (B : d.SourceCovers c) (r : s.CoverHybridPredicates B)
    (x : ι → W) (ξ : W) (ε Cerror Czero : ℝ) :
    T.coverHybridPhaseCost B r x ξ ε Cerror Czero =
      (4 / d.density) * ∑ b : PoolSourceTag P, d.tagWeight b *
        ((T.tag b).fourierPhase (d.tagPoint x b) ξ).coverHybridCost
          (B.tag b) (B.tag b) (r.tag b) ε Cerror Czero := by
  simp only [PoolSourceTag, Fintype.sum_sum_type, Fintype.sum_unique,
    coverHybridPhaseCost, FirstGaussPoolData.tagWeight, tag,
    FirstGaussPoolData.tagPoint, FirstGaussPoolData.SourceCovers.tag,
    CoverHybridPredicates.tag]
  ring_nf
  rfl

theorem integral_coverHybridPhaseCost_eq_sum
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (B : d.SourceCovers c) (r : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    (∫ ξ, T.coverHybridPhaseCost B r x ξ ε Cerror Czero ∂actualFourierMeasure F) =
      (4 / d.density) * ∑ b : PoolSourceTag P, d.tagWeight b *
        ∫ ξ, ((T.tag b).fourierPhase (d.tagPoint x b) ξ).coverHybridCost
          (B.tag b) (B.tag b) (r.tag b) ε Cerror Czero ∂actualFourierMeasure F := by
  simp_rw [T.coverHybridPhaseCost_eq_sum B r x]
  rw [integral_const_mul, integral_finsetSum _ (fun b _ =>
    ((T.tag b).coverHybridPhaseCost_integrable (B.tag b) (B.tag b) (r.tag b)
      F (d.tagPoint x b) ε Cerror Czero).const_mul (d.tagWeight b))]
  simp_rw [integral_const_mul]

end TerminalCalibration
end ActualPoolStages

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.TerminalCalibration.coverHybridPhaseCost_eq_sum
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.TerminalCalibration.integral_coverHybridPhaseCost_eq_sum
