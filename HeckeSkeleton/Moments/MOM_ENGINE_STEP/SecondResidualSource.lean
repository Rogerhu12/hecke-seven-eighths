import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondGeneratorSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonSupportSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildren
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FinitePhase

/-!
# The actual second source is bounded by complete divisor children

The input is the genuine pair source produced from the whole Gauss
polynomial, with its own product modulus and original Schwartz test.
The actual Poisson coefficient, full finite correlation, common-support
factorization, residual Möbius sum and fixed-ray Fourier expansion are
all applied internally.  Only the individual original profile chart and
the finite reciprocity phase dictionary remain as source inputs.

The output retains one common Fourier parameter and the literal residual
divisor columns.  Their exact allocation and conversion to actual child
MomentData are the subsequent arithmetic steps.
-/

noncomputable section
open scoped NumberField Classical BigOperators FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open UniqueFactorizationMonoid MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _

/-- The actual divisor and phase labels, with the same complete common
correlation as row weight in both Cauchy halves. -/
def secondResidualKernelCost {H ι κ : Type*}
    (F : 𝓢(E, ℂ)) (rows : Finset H) (frequency : H → A.R)
    (leftColumns : Finset ι) (rightColumns : Finset κ)
    (ID IE : A.Exterior) (IA : ι → A.Exterior) (IB : κ → A.Exterior)
    (d e : A.R) (hd : A.Generates ID d) (he : A.Generates IE e)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (q : H → ℂ) (c : ι → ℂ) (f : κ → ℂ) (x : H → ι → E) (y : H → κ → E) : ℝ :=
  ∑ L ∈ divisorPool rightColumns (fun j => (IB j).val), ‖(moebius L : ℂ)‖ *
    ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
      ∫ ξ : E, ‖(𝓕 F) ξ‖ *
        (Real.sqrt (jointColumnEnergy rows leftColumns
          (fun h => q h * generatedIdealCorrelation (σ := σ) ID IE d e hd he (frequency h))
          (kernelDivisorCoefficient (fun i => (IA i).val) L c
            (fun i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
            (fun i h => σ (A.sexticResidue (IA i) (frequency h)))) x ξ) *
         Real.sqrt (jointColumnEnergy rows rightColumns
          (fun h => q h * generatedIdealCorrelation (σ := σ) ID IE d e hd he (frequency h))
          (fun h j => star (kernelDivisorCoefficient (fun j => (IB j).val) L f
            (fun j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
            (fun j h => σ (A.sexticResidue (IB j) (-frequency h))) h j)) y ξ))

/-- The complete arithmetic second kernel estimate on any actual row
carrier, so in particular no subgroup sector is dropped. -/
theorem actual_second_residual_kernel_bound {H ι κ : Type*}
    (F : 𝓢(E, ℂ)) (rows : Finset H) (frequency : H → A.R)
    (leftColumns : Finset ι) (rightColumns : Finset κ)
    (ID IE : A.Exterior) (IA : ι → A.Exterior) (IB : κ → A.Exterior)
    (IDA : ι → A.Exterior) (IEB : κ → A.Exterior)
    (hIDA : ∀ i, (IDA i).val = ID.val * (IA i).val)
    (hIEB : ∀ j, (IEB j).val = IE.val * (IB j).val)
    (d e : A.R) (a : ι → A.R) (b : κ → A.R)
    (hd : A.Generates ID d) (he : A.Generates IE e)
    (ha : ∀ i, A.Generates (IA i) (a i)) (hb : ∀ j, A.Generates (IB j) (b j))
    (hda : ∀ i, A.Generates (IDA i) (d * a i))
    (heb : ∀ j, A.Generates (IEB j) (e * b j))
    (hDa : ∀ i, IsCoprime ID.val (IA i).val)
    (hEa : ∀ i, IsCoprime IE.val (IA i).val)
    (hDb : ∀ j, IsCoprime ID.val (IB j).val)
    (hEb : ∀ j, IsCoprime IE.val (IB j).val)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (hphase : ∀ i j, IsCoprime (IA i).val (IB j).val →
      actualCommonPhase (σ := σ) ID IE (IA i) (IB j) d e (a i) (b j) =
        (phaseTable (rayLeft i, rayRight j) : ℂ))
    (q : H → ℂ) (c : ι → ℂ) (f : κ → ℂ) (x : H → ι → E) (y : H → κ → E) :
    ‖∑ h ∈ rows, q h * ∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
      (if IsCoprime (IA i).val (IB j).val then
        generatedIdealCorrelation (σ := σ) (IDA i) (IEB j)
          (d * a i) (e * b j) (hda i) (heb j) (frequency h) else 0) *
        (c i * star (f j)) * F (x h i + y h j)‖ ≤
      secondResidualKernelCost (σ := σ) Ray F rows frequency leftColumns rightColumns
        ID IE IA IB d e hd he rayLeft rayRight phaseTable q c f x y := by
  apply full_correlation_kernel_bound F rows leftColumns rightColumns
    (fun i => (IA i).val) (fun j => (IB j).val) (fun j _ => (IB j).property.1)
    (fun i j h => generatedIdealCorrelation (σ := σ) (IDA i) (IEB j)
      (d * a i) (e * b j) (hda i) (heb j) (frequency h))
    (fun h => generatedIdealCorrelation (σ := σ) ID IE d e hd he (frequency h)) q
    (fixedPhaseCoefficient Ray phaseTable)
    (fun χ i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
    (fun χ j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
    (fun i h => σ (A.sexticResidue (IA i) (frequency h)))
    (fun j h => σ (A.sexticResidue (IB j) (-frequency h)))
  intro i j h hij
  rw [generated_correlation_common_support ID IE (IA i) (IB j) (IDA i) (IEB j)
    (hIDA i) (hIEB j) d e (a i) (b j) hd he (ha i) (hb j) (hda i) (heb j)
    (hDa i) (hEa i) (hDb j) (hEb j) hij (frequency h), hphase i j hij,
    fixed_phase_expansion Ray phaseTable]

variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The actual second orbital source, with its precise Poisson scalar,
is bounded by genuine residual divisor columns under one Fourier
measure.  The analytic input is only the individual profile chart. -/
theorem actual_second_source_kernel_bound {ι κ : Type*}
    (F : 𝓢(E, ℂ)) (rows : Finset Q)
    (leftColumns : Finset ι) (rightColumns : Finset κ)
    (ID IE : A.Exterior) (IA : ι → A.Exterior) (IB : κ → A.Exterior)
    (IDA : ι → A.Exterior) (IEB : κ → A.Exterior)
    (hIDA : ∀ i, (IDA i).val = ID.val * (IA i).val)
    (hIEB : ∀ j, (IEB j).val = IE.val * (IB j).val)
    (d e : A.R) (a : ι → A.R) (b : κ → A.R)
    (hd : A.Generates ID d) (he : A.Generates IE e)
    (ha : ∀ i, A.Generates (IA i) (a i)) (hb : ∀ j, A.Generates (IB j) (b j))
    (hda : ∀ i, A.Generates (IDA i) (d * a i))
    (heb : ∀ j, A.Generates (IEB j) (e * b j))
    (hDa : ∀ i, IsCoprime ID.val (IA i).val)
    (hEa : ∀ i, IsCoprime IE.val (IA i).val)
    (hDb : ∀ j, IsCoprime ID.val (IB j).val)
    (hEb : ∀ j, IsCoprime IE.val (IB j).val)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (hphase : ∀ i j, IsCoprime (IA i).val (IB j).val →
      actualCommonPhase (σ := σ) ID IE (IA i) (IB j) d e (a i) (b j) =
        (phaseTable (rayLeft i, rayRight j) : ℂ))
    (profiles : ι → κ → SchwartzMap V ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (hleftMask : ∀ i ∈ leftColumns, IsCoprime (d * a i) (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hrightMask : ∀ j ∈ rightColumns, IsCoprime (e * b j) (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (q : Q → ℂ) (c : ι → ℂ) (f : κ → ℂ) (x : Q → ι → E) (y : Q → κ → E)
    (hprofile : ∀ t ∈ rows, ∀ i ∈ leftColumns, ∀ j ∈ rightColumns,
      IsCoprime (IA i).val (IB j).val →
      (generatedOriginalColumn (σ := σ) hΓ (IDA i) (d * a i) (hda i)).secondProfile μv hS
        (generatedOriginalColumn (σ := σ) hΓ (IEB j) (e * b j) (heb j))
        (profiles i j) finiteTest radius D t =
          q t * (c i * star (f j)) * F (x t i + y t j)) :
    let L := fun i => generatedOriginalColumn (σ := σ) hΓ (IDA i) (d * a i) (hda i)
    let R := fun j => generatedOriginalColumn (σ := σ) hΓ (IEB j) (e * b j) (heb j)
    let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
    ‖∑ t ∈ rows, ∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
      (((L i).pair hS (R j) (profiles i j)).gated
        (IsCoprime (IA i).val (IB j).val)).transformedRow μv hS finiteTest radius D t‖ ≤
      secondResidualKernelCost (σ := σ) Ray F rows (fun t => -t.out.val)
        leftColumns rightColumns ID IE IA IB d e hd he rayLeft rayRight phaseTable
        (fun t => secondOrbitalScalar radius D * q t)
        (fun i => c i * (L i).divisorPhase δ) (fun j => f j * (R j).divisorPhase δ) x y := by
  dsimp only
  let L := fun i => generatedOriginalColumn (σ := σ) hΓ (IDA i) (d * a i) (hda i)
  let R := fun j => generatedOriginalColumn (σ := σ) hΓ (IEB j) (e * b j) (heb j)
  let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
  have hbnd := actual_second_residual_kernel_bound Ray F rows (fun t => -t.out.val)
    leftColumns rightColumns ID IE IA IB IDA IEB hIDA hIEB d e a b hd he ha hb hda heb
    hDa hEa hDb hEb rayLeft rayRight phaseTable hphase
    (fun t => secondOrbitalScalar radius D * q t)
    (fun i => c i * (L i).divisorPhase δ) (fun j => f j * (R j).divisorPhase δ) x y
  have heq :
      (∑ t ∈ rows, ∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
        (((L i).pair hS (R j) (profiles i j)).gated
          (IsCoprime (IA i).val (IB j).val)).transformedRow μv hS finiteTest radius D t) =
      ∑ t ∈ rows, (secondOrbitalScalar radius D * q t) *
        ∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
          (if IsCoprime (IA i).val (IB j).val then
            generatedIdealCorrelation (σ := σ) (IDA i) (IEB j)
              (d * a i) (e * b j) (hda i) (heb j) (-t.out.val) else 0) *
          ((c i * (L i).divisorPhase δ) * star (f j * (R j).divisorPhase δ)) *
            F (x t i + y t j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [ParentPeriodicPair.gated_transformedRow]
    by_cases hij : IsCoprime (IA i).val (IB j).val
    · rw [if_pos hij, if_pos hij,
        (L i).transformedRow_out μv hS (R j) (profiles i j) finiteTest radius D
          (hleftMask i hi) (hrightMask j hj) t]
      rw [hprofile t ht i hi j hj hij, generatedColumn_correlation]
      simp only [star_mul, δ]
      ring
    · simp only [if_neg hij, zero_mul, mul_zero]
  rw [heq]
  exact hbnd

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_residual_kernel_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_source_kernel_bound
