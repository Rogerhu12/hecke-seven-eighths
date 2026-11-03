import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCharacterSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussPoolDictionary
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCorrelationSource

/-!
# Actual generator transport before the second Poisson operation

Common-support extraction changes the presentation of a column modulus.
The source equality below uses the genuine allowed-generator identity
at each frequency before applying Poisson.  Consequently the common
supports and residual generators can be chosen independently while the
same whole coefficient and actual original profile are retained.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

theorem generatedColumn_orbit_eq_gauss (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) (q : Q) :
    (generatedOriginalColumn (σ := σ) hΓ I a ha).orbit hS q =
      actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hS a ha.1
        (generatedIdealCharacter (σ := σ) I a ha) q.out.val := by
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

theorem generatedColumn_correlation (I J : A.Exterior) (a b : A.R)
    (ha : A.Generates I a) (hb : A.Generates J b) (j : A.R) :
    (generatedOriginalColumn (σ := σ) hΓ I a ha).correlation
        (generatedOriginalColumn (σ := σ) hΓ J b hb) j =
      generatedIdealCorrelation (σ := σ) I J a b ha hb j := rfl

theorem generatedColumn_orbit_generator_change
    (C : A.GeneralArithmeticContext σ η htrace)
    (D : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ htrace C.correction.B D)
    (I : A.Exterior) (a b : A.R) (ha : A.Generates I a) (hb : A.Generates I b)
    (haa : A.IsAllowed C.correction.B (Units.mk0 (a : K) (by exact_mod_cast ha.1)))
    (hbb : A.IsAllowed C.correction.B (Units.mk0 (b : K) (by exact_mod_cast hb.1)))
    (q : Q) :
    (generatedOriginalColumn (σ := σ) hΓ I b hb).orbit hS q =
      (generatedOriginalColumn (σ := σ) hΓ I a ha).orbit hS q := by
  rw [generatedColumn_orbit_eq_gauss, generatedColumn_orbit_eq_gauss]
  exact actual_gauss_generator_replacement hS C D hD I a b q.out.val ha hb haa hbb

variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]

/-- Exact equality of the original second source after both genuine
generator replacements.  No transformed or summed identity is assumed. -/
theorem generated_gauss_pair_source_generator_change
    (C : A.GeneralArithmeticContext σ η htrace)
    (D : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ htrace C.correction.B D)
    (I J : A.Exterior) (a b a' b' : A.R)
    (ha : A.Generates I a) (hb : A.Generates J b)
    (ha' : A.Generates I a') (hb' : A.Generates J b')
    (haa : A.IsAllowed C.correction.B (Units.mk0 (a : K) (by exact_mod_cast ha.1)))
    (hbb : A.IsAllowed C.correction.B (Units.mk0 (b : K) (by exact_mod_cast hb.1)))
    (haa' : A.IsAllowed C.correction.B (Units.mk0 (a' : K) (by exact_mod_cast ha'.1)))
    (hbb' : A.IsAllowed C.correction.B (Units.mk0 (b' : K) (by exact_mod_cast hb'.1)))
    (φ : SchwartzMap V ℂ)
    (ψ : ((v : (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (r : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R)) :
    ((generatedOriginalColumn (σ := σ) hΓ I a' ha').pair hS
      (generatedOriginalColumn (σ := σ) hΓ J b' hb') φ).maskedSeries ψ r M =
    ((generatedOriginalColumn (σ := σ) hΓ I a ha).pair hS
      (generatedOriginalColumn (σ := σ) hΓ J b hb) φ).maskedSeries ψ r M := by
  change (∑' q : Q, ((generatedOriginalColumn (σ := σ) hΓ I a' ha').pair hS
    (generatedOriginalColumn (σ := σ) hΓ J b' hb') φ).maskedTerm ψ r M q) =
      ∑' q : Q, ((generatedOriginalColumn (σ := σ) hΓ I a ha).pair hS
        (generatedOriginalColumn (σ := σ) hΓ J b hb) φ).maskedTerm ψ r M q
  apply tsum_congr
  intro q
  unfold ParentPeriodicPair.maskedTerm
  rw [OrbitalGaussColumn.pair_orbitWeight, OrbitalGaussColumn.pair_orbitWeight,
    generatedColumn_orbit_generator_change hΓ hS C D hD I a a' ha ha' haa haa' q,
    generatedColumn_orbit_generator_change hΓ hS C D hD J b b' hb hb' hbb hbb' q]
  rfl

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.generated_gauss_pair_source_generator_change
