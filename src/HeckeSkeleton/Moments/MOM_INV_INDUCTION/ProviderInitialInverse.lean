import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceReductionPoisson
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveProduction

/-!
# The original inverse source enters actual one-pass production

The initial inverse polynomial is represented as the genuine retained-
divisor inverse parent with unit old label and unit divisor. The unit
label identity uses the allowed-generator reciprocity theorem; it does
not identify the chosen generator of the unit ideal with `1`.

The original square-root normalization is retained exactly. After the
source identity, the existing actual second-Poisson and positive-source
theorems apply to this constructed parent. No initial moment bound or
canonical-child reconstruction is supplied as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialInverse

open NumberField IsDedekindDomain MeasureTheory UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open FixedTripleFibers CanonicalChildren CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K
local notation "Varch" => mixedEmbedding.euclidean.mixedSpace K

def unitTriple : OuterTriple K := ⟨1, 1, 1⟩

theorem childPuncture_unitTriple (ρ : Ideal (𝓞 K)) :
    childPuncture ρ (unitTriple K) = ρ := by
  simp [childPuncture, unitTriple, Ideal.radical_top]

variable {σ : Type*}
variable (C : CanonicalBlock.ColumnData K S σ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ C.background)
variable (W : SchwartzMap ℝ ℂ)

/-- The actual original marks and puncture are retained in one
complete family; the original background is unchanged. -/
def family : ColumnFamily K Sset σ Θ ψ where
  lambda := C.lambda
  background := fun _ => C.background
  background_admissible := fun _ => hν
  originalPuncture := C.puncture
  originalSlots := C.slots
  primeLists := C.primeLists
  primeWeights := C.primeWeights
  survivors := fun _ => C.slots
  survivors_subset := fun _ => Finset.Subset.refl _
  columns := fun _ => squarefreePool K Sset (2 * C.base ^ C.length)
  columns_squarefree := fun _ _ hn => squarefreePool_squarefree K Sset hn
  cutoff := fun _ => W
  base := C.base
  columnLength := fun _ => C.length

def sourceMark (n : Ext) : ℂ :=
  (if IsCoprime n.val.val C.puncture then 1 else 0) *
    divisorMark C.slots C.primeLists C.primeWeights n.val.val

variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hallowed in
/-- The chosen unit-ideal generator is handled by actual reciprocity. -/
theorem unit_label (n : Ext) :
    labelRow K Sset D n (FirstInversePoisson.unitIdeal K S).val.val = 1 := by
  rw [labelRow_exterior, hallowed.reciprocity, FirstInversePoisson.idealSymbol_unit]

include hallowed in
theorem inverse_coefficient (n : Ext) :
    DivisorInverseColumn.coefficient K S D (family K S C Θ ψ hν W)
      (unitTriple K) (FirstInversePoisson.unitIdeal K S).val.val 1 n =
      (moebius n.val.val : ℂ) * heckeIdealCoefficient K C.background n.val *
        sourceMark K S C n * W ((n.val.val.absNorm : ℝ) / C.base ^ C.length) := by
  unfold DivisorInverseColumn.coefficient FirstCanonicalLabel.inverseCoefficient
  simp only [family, childPuncture_unitTriple, unit_label K S D hallowed,
    one_pow, mul_one, idealSymbol, sIntegerSexticIdealEvaluation_one]
  unfold sourceMark
  ring

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [Γ.FiniteIndex]
local notation "Orbit" => SIntegerOrbits K Sset Γ

include hallowed in
/-- The larger complete provider pool changes no inverse source term:
all extra columns are killed by the original supported profile. -/
theorem sourceColumn_eq_scaled_orbitColumn (hbase : 0 < C.base)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (q : Orbit) :
    SourceReductionPoisson.sourceColumn K S D C.background (sourceMark K S C) W
        (C.base ^ C.length) q.out.val =
      (Real.sqrt (C.base ^ C.length) : ℂ)⁻¹ *
        DivisorInverseColumn.orbitColumn K S Γ D (family K S C Θ ψ hν W)
          (unitTriple K) (FirstInversePoisson.unitIdeal K S).val.val 1 q := by
  have hX : 0 < C.base ^ C.length := Real.rpow_pos_of_pos hbase _
  let a : Ext → ℂ := fun n =>
    (moebius n.val.val : ℂ) * heckeIdealCoefficient K C.background n.val *
      sourceMark K S C n * W ((n.val.val.absNorm : ℝ) / C.base ^ C.length) *
        star (idealSymbol K Sset D n q.out.val)
  have hpool : (∑ n ∈ squarefreePool K Sset (C.base ^ C.length), a n) =
      ∑ n ∈ squarefreePool K Sset (2 * C.base ^ C.length), a n := by
    apply Finset.sum_subset
    · intro n hn
      obtain ⟨hsf, hnorm⟩ := (mem_squarefreePool K Sset _ n).mp hn
      exact (mem_squarefreePool K Sset _ n).mpr ⟨hsf, by linarith⟩
    · intro n hn hnot
      have hzero : W ((n.val.val.absNorm : ℝ) / C.base ^ C.length) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hs
        have hw := hW hs
        apply hnot
        apply (mem_squarefreePool K Sset _ n).mpr
        exact ⟨((mem_squarefreePool K Sset _ n).mp hn).1,
          by simpa only [height] using (div_le_iff₀ hX).mp hw.2⟩
      simp only [a, hzero, mul_zero, zero_mul]
  unfold SourceReductionPoisson.sourceColumn DivisorInverseColumn.orbitColumn
  simp_rw [inverse_coefficient K S D C Θ ψ hν W hallowed]
  dsimp only [family]
  rw [Finset.mul_sum]
  calc
    _ = (Real.sqrt (C.base ^ C.length) : ℂ)⁻¹ *
        ∑ n ∈ squarefreePool K Sset (C.base ^ C.length), a n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      dsimp only [SourceReductionPoisson.coefficient, a, height]
      ring
    _ = _ := by rw [hpool, Finset.mul_sum]

include hallowed in
theorem sourceColumn_norm_sq (hbase : 0 < C.base)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (q : Orbit) :
    ‖SourceReductionPoisson.sourceColumn K S D C.background (sourceMark K S C) W
      (C.base ^ C.length) q.out.val‖ ^ 2 =
      (C.base ^ C.length)⁻¹ *
        ‖DivisorInverseColumn.orbitColumn K S Γ D (family K S C Θ ψ hν W)
          (unitTriple K) (FirstInversePoisson.unitIdeal K S).val.val 1 q‖ ^ 2 := by
  rw [sourceColumn_eq_scaled_orbitColumn K S D C Θ ψ hν W hallowed Γ hbase hW q,
    norm_mul, mul_pow, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (Real.rpow_nonneg hbase.le _)]

include hallowed in
/-- Exact original normalization at the genuine second Poisson parent. -/
theorem source_energy_eq_inverse_parent (hbase : 0 < C.base)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (H : {r : ℝ // 0 < r}) :
    SourceReductionPoisson.orbitalEnergy K S D Γ C.background (sourceMark K S C)
        W (C.base ^ C.length) H =
      (((C.base ^ C.length)⁻¹ : ℝ) : ℂ) *
        DivisorInverseColumn.weightedEnergy K S Γ D (family K S C Θ ψ hν W)
          (unitTriple K) (FirstInversePoisson.unitIdeal K S).val.val 1
          (rowBallArchTest K S 1) (rowBallFiniteFamily K S 1) ∅
          (InverseRowMajorant.rowRadius H) := by
  unfold SourceReductionPoisson.orbitalEnergy DivisorInverseColumn.weightedEnergy
    sIntegerWeightedOrbitalSeries
  simp only [sIntegerOrbitAvoidanceMask, Finset.notMem_empty, false_implies, implies_true,
    if_true, one_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  rw [sourceColumn_norm_sq K S D C Θ ψ hν W hallowed Γ hbase hW q,
    Complex.ofReal_mul]
  ring

variable [DecidableEq σ]

/-- The inverse source is an actual input of the existing one-pass
canonical production theorem, with its original arithmetic data. -/
def parentData (hbase : 1 < C.base) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (H : {r : ℝ // 0 < r}) : SecondParentProduction.Data K S σ Θ ψ where
  columns := family K S C Θ ψ hν W
  triple := unitTriple K
  label := FirstInversePoisson.unitIdeal K S
  divisor := ⟨1, one_ne_zero⟩
  archTest := rowBallArchTest K S 1
  localTest := rowBallFiniteFamily K S 1
  locallyConstant := rowBallFiniteFamily_locallyConstant K S 1
  compactSupport := rowBallFiniteFamily_compactSupport K S 1
  radius := InverseRowMajorant.rowRadius H
  frequencyBound := 1
  base_gt_one := hbase
  cutoffSupport := by
    intro y hy
    have hb := hW hy
    constructor <;> linarith [hb.1, hb.2]
  fullPool := rfl

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable (hΓ : Γ ≤ (powMonoidHom 6 : ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →* ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include hallowed ν μ in
/-- Genuine initial one-pass Poisson with its actual common/divisor
cutoff. Both additive zeros and tails remain in the exact identity. -/
theorem initial_poisson_split (hbase : 1 < C.base)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (Hrow : {r : ℝ // 0 < r})
    (Hfreq : Ext → Finset (HeightOneSpectrum OS) → ℝ) :
    let T := parentData K S C Θ ψ hν W hbase hW Hrow
    let a := DivisorInverseColumn.coefficient K S D T.columns T.triple T.label.val.val T.divisor.val
    SourceReductionPoisson.orbitalEnergy K S D Γ C.background (sourceMark K S C)
      W (C.base ^ C.length) Hrow =
      (((C.base ^ C.length)⁻¹ : ℝ) : ℂ) *
        (SecondAdaptiveCutoff.retainedSourceAt K S D Γ hΓ μv a
          (T.columns.columns T.triple ×ˢ T.columns.columns T.triple)
          T.archTest T.localTest T.locallyConstant T.compactSupport T.radius Hfreq +
        SecondPoissonSplit.additiveZeros K S D Γ hΓ μv a (T.columns.columns T.triple)
          T.archTest T.localTest T.locallyConstant T.compactSupport T.radius +
        SecondAdaptiveCutoff.tailSourceAt K S D Γ hΓ μv a
          (T.columns.columns T.triple ×ˢ T.columns.columns T.triple)
          T.archTest T.localTest T.locallyConstant T.compactSupport T.radius Hfreq) := by
  dsimp only
  rw [source_energy_eq_inverse_parent K S D C Θ ψ hν W hallowed Γ
    (zero_lt_one.trans hbase) hW Hrow]
  congr 1
  exact SecondAdaptiveCutoff.genuine_second_split_at K S D Γ hΓ μv ν μ
    (family K S C Θ ψ hν W) (unitTriple K) (FirstInversePoisson.unitIdeal K S).val.val 1
    (rowBallArchTest K S 1) (rowBallFiniteFamily K S 1)
    (rowBallFiniteFamily_locallyConstant K S 1) (rowBallFiniteFamily_compactSupport K S 1)
    (InverseRowMajorant.rowRadius Hrow) Hfreq

include hallowed ν hΓ in
/-- Uniform actual retained production for the constructed initial
inverse parent. Its output consists of the real positive canonical
source energies, not a free endpoint estimate. -/
theorem exists_uniform_initial_retained_bound (eps : ℝ) (heps : 0 < eps) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ₀ : Type*} [DecidableEq σ₀] (C₀ : CanonicalBlock.ColumnData K S σ₀)
        (Θ₀ : Subgroup (HeckeCharacter K)) (ψ₀ : HeckeCharacter K)
        (hν₀ : BackgroundCycle.Admissible K Θ₀ ψ₀ C₀.background)
        (W₀ : SchwartzMap ℝ ℂ) (hbase₀ : 1 < C₀.base)
        (hW₀ : tsupport W₀ ⊆ Set.Icc (1 : ℝ) 2) (Hrow : {r : ℝ // 0 < r})
        (Hfreq : Ext → Finset (HeightOneSpectrum OS) → ℝ)
        (G : HeckeCharacter K) (hG : G ∈ Θ₀),
      ThetaCalibrationInput K Sset D C₀.lambda G →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K C₀.background p) →
      (∀ i ∈ C₀.slots, ∀ p ∈ C₀.primeLists i, Prime p) →
      let T := parentData K S C₀ Θ₀ ψ₀ hν₀ W₀ hbase₀ hW₀ Hrow
      ‖SecondAdaptiveCutoff.retainedSourceAt K S D Γ hΓ μv
        (DivisorInverseColumn.coefficient K S D T.columns T.triple T.label.val.val T.divisor.val)
        (T.columns.columns T.triple ×ˢ T.columns.columns T.triple)
        T.archTest T.localTest T.locallyConstant T.compactSupport T.radius Hfreq‖ ≤
        A * (Real.sqrt (SecondAdaptiveProduction.totalAt K S D Γ T Hfreq G hG eps m false) *
          Real.sqrt (SecondAdaptiveProduction.totalAt K S D Γ T Hfreq G hG eps m true)) := by
  obtain ⟨q, A, hA, hb⟩ := SecondAdaptiveProduction.exists_retained_centered_bound
    K S D Γ μv ν hΓ hallowed (rowBallFiniteFamily K S 1)
    (rowBallFiniteFamily_locallyConstant K S 1) (rowBallFiniteFamily_compactSupport K S 1)
    eps heps m
  refine ⟨A * q.sup (schwartzSeminormFamily ℝ Varch ℂ) (rowBallArchTest K S 1),
    mul_nonneg hA (apply_nonneg _ _), ?_⟩
  intro σ₀ _ C₀ Θ₀ ψ₀ hν₀ W₀ hbase₀ hW₀ Hrow Hfreq G hG hcal hbg hprime
  exact hb (parentData K S C₀ Θ₀ ψ₀ hν₀ W₀ hbase₀ hW₀ Hrow) rfl
    Hfreq G hG hcal hbg hprime

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialInverse

end
