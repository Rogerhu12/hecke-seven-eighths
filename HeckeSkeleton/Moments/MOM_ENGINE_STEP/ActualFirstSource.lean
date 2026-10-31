import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstLinearizedSource

/-!
# The original parent and all actual first-stage sources

This record contains raw column generators, original profiles, individual
profile charts, and the original parent expansion/Gram calibration. Its
common-support blocks, mask-divisor carriers, and linearized pooled costs
are computed. The theorem derives the parent inequality internally and
chooses its original-profile seminorms before every moving source.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {ω ψ : HeckeCharacter K}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

/-- Only primitive original source data occur here. In particular,
there is no parent inequality or common-kernel mass field. -/
structure ActualFirstSource
    (C : A.GeneralArithmeticContext σ η hS)
    (P : PowerScaleExteriorPool A bad Z ell eps)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
    (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X) where
  Column : Type
  columns : Finset Column
  ideal : Column → A.Exterior
  generator : Column → A.R
  generates : ∀ i, A.Generates (ideal i) (generator i)
  profiles : Column → Column → SchwartzMap V ℂ
  radius : {r : ℝ // 0 < r}
  mask : Finset (HeightOneSpectrum A.R)
  fiber : ℕ
  charts : ∀ DE : commonSupportPool columns columns (fun i => (ideal i).val)
      (fun j => (ideal j).val),
    ∀ D : ((canonicalFirstCommonBlock C columns columns ideal ideal DE.val DE.property).mask mask).powerset,
      FirstBlockProfileChart (E := E) hΓ μv
        (canonicalFirstCommonBlock C columns columns ideal ideal DE.val DE.property)
        C columns columns profiles finiteTest radius D.val
  pools : ∀ DE : commonSupportPool columns columns (fun i => (ideal i).val)
      (fun j => (ideal j).val),
    ∀ D : ((canonicalFirstCommonBlock C columns columns ideal ideal DE.val DE.property).mask mask).powerset,
      FirstBlockPoolData (charts DE D) P mask X hX
  calibration : ParentSourceCalibration centered d a Z t Y₁ Y₂ columns
    (fun i j => (generatedOriginalColumn (σ := σ) hΓ (ideal i) (generator i) (generates i)).originalPair
      (generatedOriginalColumn (σ := σ) hΓ (ideal j) (generator j) (generates j)) (profiles i j))
    (sIntegerFiniteTestFunction K A.Sf finiteTest) radius mask fiber

variable {hΓ μv}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}

namespace ActualFirstSource

variable (s : ActualFirstSource (E := E) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX)

abbrev CommonLabel := commonSupportPool s.columns s.columns
  (fun i => (s.ideal i).val) (fun j => (s.ideal j).val)

def block (v : s.CommonLabel) :=
  canonicalFirstCommonBlock C s.columns s.columns s.ideal s.ideal v.val v.property

def source (v : s.CommonLabel) :=
  (s.block v).finiteSource hΓ C s.columns s.columns s.profiles s.mask s.radius X hX

/-- Two positive original scales for each actual internal divisor and
finite phase, fixed before the continuous Fourier parameter. -/
structure Normalization where
  left : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    (divisorPool (s.pools v D).rightData.columns
      (fun j => ((s.pools v D).rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ
  right : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    (divisorPool (s.pools v D).rightData.columns
      (fun j => ((s.pools v D).rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ
  left_pos : ∀ v D S χ, 0 < left v D S χ
  right_pos : ∀ v D S χ, 0 < right v D S χ

def linearizedCost (N : s.Normalization) : ℝ :=
  ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (s.pools v D).linearizedCost (N.left v D) (N.right v D)

def zeroCost
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0) : ℝ :=
  ∑ v : s.CommonLabel, ‖(s.source v).zeroTerm μv hDiff finiteTest‖

def tailCost (seminorms : Finset (ℕ × ℕ)) : ℝ :=
  ∑ v : s.CommonLabel,
    ∑ i ∈ (s.source v).leftColumns, ∑ j ∈ (s.source v).rightColumns,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((s.source v).pairs i j).profile *
        ((s.source v).pairs i j).truncationMass (s.source v).mask s.radius

end ActualFirstSource

variable (hΓ μv)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

include ν μ in
/-- The actual original parent reaches the normalized first Fourier
integrals. All finite carriers and whole coefficients are computed from
the primitive source record, and the constants precede that record. -/
theorem actual_parent_first_linearized
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ Lattice < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Ctail : ℝ, 0 ≤ Ctail ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualFirstSource (E := E) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ N : s.Normalization,
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * (s.zeroCost hDiff + s.linearizedCost N +
          Ctail * X ^ (1 - decay) * s.tailCost seminorms) := by
  obtain ⟨seminorms, Ctail, hCtail, hbound⟩ :=
    parent_first_stage_pool_bound (E := E) (ν := ν) (μ := μ) hΓ μv
      C hDiff finiteTest hlc hcs decay hdecay order horder hdegree
  refine ⟨seminorms, Ctail, hCtail, ?_⟩
  intro Z ell eps bad P ω ψ centered d a t Y₁ Y₂ X hX s N
  have hb := hbound Z ell eps bad P s.columns s.ideal s.generator s.generates
    s.profiles s.radius s.mask X hX s.charts s.pools centered d a t Y₁ Y₂
    s.fiber s.calibration
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
  simp only [ActualFirstSource.zeroCost, ActualFirstSource.linearizedCost,
    ActualFirstSource.tailCost, Finset.sum_add_distrib, ← Finset.mul_sum]
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro D _
  exact (s.pools v D).pooledCost_le_linearized (N.left v D) (N.right v D)
    (N.left_pos v D) (N.right_pos v D)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_first_linearized
