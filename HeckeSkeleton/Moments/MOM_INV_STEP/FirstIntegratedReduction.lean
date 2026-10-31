import HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedErrorBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondSpectralCost

/-!
# The second production bound under the original first spectral measure

The actual positive source is dominated pointwise by the two actual
second productions and the complete second error. A continuous
polynomial majorant then justifies both integrations, even without a
parameter measurability theorem for the nested second production.
Only its already proved pointwise bound is needed for this compositional
lemma. All spectral degrees, seminorms and constants are chosen before
the original source and test.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstIntegratedReduction

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open CanonicalNormPools FirstParentRows FirstOuterCenters FirstPositiveSource
  FirstCenteredErrorIntegrals FirstErrorIntegration FirstSpectralAggregation
  SecondSpectralCost CommonKernel InverseRowMajorant
open scoped Classical BigOperators nonZeroDivisors

def degree (k : ℕ) : ℕ := (exists_cauchy_polynomial_majorant k).choose

def polynomialCoefficient (k : ℕ) : ℝ :=
  (exists_cauchy_polynomial_majorant k).choose_spec.choose

theorem polynomialCoefficient_nonneg (k : ℕ) : 0 ≤ polynomialCoefficient k :=
  (exists_cauchy_polynomial_majorant k).choose_spec.choose_spec.1

theorem cauchy_le_polynomial (k : ℕ) (s : ℝ) :
    NestedMellinBudget.cauchyCost (-(1 / 2 : ℝ)) s k ≤
      firstPolynomial (degree k) (polynomialCoefficient k) s :=
  (exists_cauchy_polynomial_majorant k).choose_spec.choose_spec.2 s

def testSeminorm (k : ℕ) : Finset (ℕ × ℕ) :=
  (exists_firstPolynomial_budget (degree k)).choose

def integralConstant (k : ℕ) : ℝ :=
  (exists_firstPolynomial_budget (degree k)).choose_spec.choose

theorem integralConstant_nonneg (k : ℕ) : 0 ≤ integralConstant k :=
  (exists_firstPolynomial_budget (degree k)).choose_spec.choose_spec.1

def coordinateConstant (k : ℕ) : ℝ :=
  coordinateMoment (degree k) (firstCoordinate false) +
    coordinateMoment (degree k) (firstCoordinate true)

theorem coordinateConstant_nonneg (k : ℕ) : 0 ≤ coordinateConstant k :=
  add_nonneg (coordinateMoment_nonneg _ _) (coordinateMoment_nonneg _ _)

theorem coordinateMoment_le (k : ℕ) (side : Bool) :
    coordinateMoment (degree k) (firstCoordinate side) ≤ coordinateConstant k := by
  cases side
  · exact le_add_of_nonneg_right (coordinateMoment_nonneg _ _)
  · exact le_add_of_nonneg_left (coordinateMoment_nonneg _ _)

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

def integrationConstant (slotCap : ℕ) (ε₂ : ℝ) (hε₂ : 0 < ε₂) (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ slotCap) ^ 2 * (rowCovolume K S)⁻¹ *
    integralConstant k * polynomialCoefficient k * coordinateConstant k *
      FirstNormalizedReduction.reductionConstant K S D Γ hΓ μv hallowed ν μ ε₂ hε₂ k

theorem integrationConstant_nonneg (slotCap : ℕ) (ε₂ : ℝ) (hε₂ : 0 < ε₂) (k : ℕ) :
    0 ≤ integrationConstant K S D Γ hΓ μv hallowed ν μ slotCap ε₂ hε₂ k := by
  unfold integrationConstant
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by positivity) (inv_nonneg.mpr (rowCovolume_pos K S).le))
      (integralConstant_nonneg k)) (polynomialCoefficient_nonneg k))
      (coordinateConstant_nonneg k))
    (FirstNormalizedReduction.reductionConstant_nonneg K S D Γ hΓ μv hallowed ν μ ε₂ hε₂ k)

variable {σ ι : Type*} [DecidableEq σ] [Fintype ι]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (labels : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))))
variable (grid : ι → {r : ℝ // 0 < r})
variable (centers : FirstOuterCenters.Centering K S D T grid) (side : Bool)
variable (R : OuterIndex K S D T → {r : ℝ // 0 < r}) (massEps ε₁ : ℝ)
variable (Z r ell V tau : ℝ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)

include hallowed ν μ in
theorem total_le_of_production (slotCap : ℕ) (hslots : T.columns.slots.card ≤ slotCap)
    (ε₂ : ℝ) (hε₂ : 0 < ε₂) (m₂ : ℕ) (Bprod : ℝ) (hBprod : 0 ≤ Bprod)
    (hZ : 0 ≤ Z)
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (hbg : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K T.columns.background p)
    (hprime : ∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k, Prime p)
    (hproduction : ∀ k : ι, ∀ J ∈ T.columns.slots.powerset, ∀ side₂ : Bool, ∀ s : ℝ,
      FirstNormalizedReduction.production K S D Γ T H labels grid centers side
        R massEps ε₁ Z r ell V tau Θ ψ G hν hG hbase ε₂ m₂ k J side₂ s ≤
      Bprod * NestedMellinBudget.cauchyCost (-(1 / 2 : ℝ)) s m₂)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) :
    FirstNormalizedSource.total K S D Γ T H labels grid centers side R massEps ε₁
      Z r ell V Θ ψ G hν hG W hW (degree m₂) ≤
    integrationConstant K S D Γ hΓ μv hallowed ν μ slotCap ε₂ hε₂ m₂ *
      (Fintype.card ι : ℝ) * Bprod *
        ((testSeminorm m₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 +
      FirstNormalizedErrorBudget.boxedTotal K S D Γ hΓ μv T grid centers side
        R massEps ε₁ Z r ell V tau Θ ψ G hν hG hbase W hW (degree m₂)
        (FirstNormalizedErrorBudget.liveSources K S D Γ T H labels) := by
  let C₂ := FirstNormalizedReduction.reductionConstant K S D Γ hΓ μv hallowed ν μ ε₂ hε₂ m₂
  have hC₂ : 0 ≤ C₂ := FirstNormalizedReduction.reductionConstant_nonneg
    K S D Γ hΓ μv hallowed ν μ ε₂ hε₂ m₂
  let B := C₂ * Bprod * polynomialCoefficient m₂
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hC₂ hBprod) (polynomialCoefficient_nonneg m₂)
  let P := firstPolynomial (degree m₂) B
  let ρ := MellinSeparation.density W hW
  let E (k : ι) (J : Finset σ) :=
    FirstNormalizedReduction.error K S D Γ T H labels grid centers side
      R massEps ε₁ Z r ell V tau Θ ψ G hν hG hbase hΓ μv k J
  have hpoint (k : ι) (J : Finset σ) (hJ : J ∈ T.columns.slots.powerset) (s : ℝ) :
      FirstNormalizedSource.sourceAt K S D Γ T H labels grid centers side R massEps ε₁
        Z r ell V Θ ψ G hν hG k J s ≤ P s + E k J s := by
    have hp := FirstNormalizedReduction.sourceAt_le K S D Γ T H labels grid centers side
      R massEps ε₁ Z r ell V tau Θ ψ G hν hG hbase hΓ μv hallowed ν μ
      ε₂ hε₂ m₂ hZ hcal hbg hprime k J s
    have hb (side₂ : Bool) := (hproduction k J hJ side₂ s).trans
      (mul_le_mul_of_nonneg_left (cauchy_le_polynomial m₂ s) hBprod)
    apply hp.trans
    have hh := add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add (hb false) (hb true)) (by positivity : 0 ≤ C₂ / 2))
      (le_refl (E k J s))
    convert hh using 1 <;> dsimp only [P, B, C₂, firstPolynomial] <;> ring
  have hav (k : ι) (J : Finset σ) (hJ : J ∈ T.columns.slots.powerset) :
      spectralAverage ρ (degree m₂) (signedCoordinate side)
        (FirstNormalizedSource.sourceAt K S D Γ T H labels grid centers side R massEps ε₁
          Z r ell V Θ ψ G hν hG k J) ≤
      spectralAverage ρ (degree m₂) (signedCoordinate side) P +
        spectralAverage ρ (degree m₂) (signedCoordinate side) (E k J) := by
    have he := FirstNormalizedErrorBudget.error_spectral_integrability
      (K := K) (S := S) (D := D) (Γ := Γ) (hΓ := hΓ) (μv := μv)
      (T := T) (H := H) (labels := labels) (grid := grid) (centers := centers) (side := side)
      (R := R) (massEps := massEps) (ε := ε₁) (Z := Z) (r := r) (ell := ell) (V := V)
      (tau := tau) (Θ := Θ) (ψ := ψ) (G := G) (hν := hν) (hG := hG) (hbase := hbase)
      (m := degree m₂) hZ k J ρ
    apply spectralAverage_le_add ρ (degree m₂) (signedCoordinate side) _ P (E k J)
      (FirstNormalizedSource.sourceAt_nonneg K S D Γ T H labels grid centers side R massEps ε₁
        Z r ell V Θ ψ G hν hG hZ k J) (hpoint k J hJ)
      (firstPolynomial_inner_integrable ρ (degree m₂) B hB) he.1
    · simpa only [firstCoordinate_apply] using
        firstPolynomial_outer_integrable ρ (degree m₂) B hB (firstCoordinate side)
    · exact he.2
  have houter : 0 ≤ FirstNormalizedErrorBudget.outerCoefficient K S T W hW :=
    FirstNormalizedErrorBudget.outerCoefficient_nonneg K S T W hW
  have hsum := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := (Finset.univ : Finset ι)) fun k hk =>
      Finset.sum_le_sum (s := T.columns.slots.powerset) fun J hJ => hav k J hJ) houter
  have hint := (exists_firstPolynomial_budget (degree m₂)).choose_spec.choose_spec.2
    W hW B hB (firstCoordinate side)
  change mellinMass W hW * spectralAverage ρ (degree m₂) (firstCoordinate side) P ≤
    integralConstant m₂ * B * coordinateMoment (degree m₂) (firstCoordinate side) *
      ((testSeminorm m₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 at hint
  simp only [firstCoordinate_apply] at hint
  have hmaskcard : (T.columns.slots.powerset.card : ℝ) ≤ (2 : ℝ) ^ slotCap := by
    simpa only [Finset.sdiff_empty] using remaining_masks_bound K S T slotCap hslots ∅
  have hprodterm : FirstNormalizedErrorBudget.outerCoefficient K S T W hW *
      ((Fintype.card ι : ℝ) * (T.columns.slots.powerset.card : ℝ) *
        spectralAverage ρ (degree m₂) (signedCoordinate side) P) ≤
      integrationConstant K S D Γ hΓ μv hallowed ν μ slotCap ε₂ hε₂ m₂ *
        (Fintype.card ι : ℝ) * Bprod *
          ((testSeminorm m₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 := by
    have hcov : 0 ≤ (rowCovolume K S)⁻¹ := inv_nonneg.mpr (rowCovolume_pos K S).le
    have hscale : 0 ≤ (Fintype.card ι : ℝ) * (T.columns.slots.powerset.card : ℝ) ^ 2 *
        (rowCovolume K S)⁻¹ := by positivity
    have hh := mul_le_mul_of_nonneg_left hint hscale
    have hAi := integralConstant_nonneg m₂
    have hBi := polynomialCoefficient_nonneg m₂
    have hci := coordinateMoment_nonneg (degree m₂) (firstCoordinate side)
    calc
      _ = ((Fintype.card ι : ℝ) * (T.columns.slots.powerset.card : ℝ) ^ 2 *
          (rowCovolume K S)⁻¹) *
          (mellinMass W hW * spectralAverage ρ (degree m₂) (signedCoordinate side) P) := by
            unfold FirstNormalizedErrorBudget.outerCoefficient
            ring
      _ ≤ _ := hh
      _ ≤ ((Fintype.card ι : ℝ) * ((2 : ℝ) ^ slotCap) ^ 2 * (rowCovolume K S)⁻¹) *
          (integralConstant m₂ * (C₂ * Bprod * polynomialCoefficient m₂) * coordinateConstant m₂ *
            ((testSeminorm m₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2) := by
        dsimp only [B]
        gcongr <;> first | exact hmaskcard | exact coordinateMoment_le m₂ side
      _ = _ := by unfold integrationConstant; dsimp only [C₂]; ring
  have heq := FirstNormalizedErrorBudget.error_total_eq K S D Γ hΓ μv T H labels grid centers
    side R massEps ε₁ Z r ell V tau Θ ψ G hν hG hbase W hW (degree m₂) hZ
  calc
    _ ≤ FirstNormalizedErrorBudget.outerCoefficient K S T W hW *
        (∑ k : ι, ∑ J ∈ T.columns.slots.powerset,
          (spectralAverage ρ (degree m₂) (signedCoordinate side) P +
            spectralAverage ρ (degree m₂) (signedCoordinate side) (E k J))) := hsum
    _ = FirstNormalizedErrorBudget.outerCoefficient K S T W hW *
        ((Fintype.card ι : ℝ) * (T.columns.slots.powerset.card : ℝ) *
          spectralAverage ρ (degree m₂) (signedCoordinate side) P) +
        FirstNormalizedErrorBudget.boxedTotal K S D Γ hΓ μv T grid centers side R massEps ε₁
          Z r ell V tau Θ ψ G hν hG hbase W hW (degree m₂)
          (FirstNormalizedErrorBudget.liveSources K S D Γ T H labels) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_add]
      rw [heq]
      ring
    _ ≤ _ := add_le_add hprodterm le_rfl

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstIntegratedReduction

end
