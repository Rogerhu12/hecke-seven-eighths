import HeckeSkeleton.Moments.MOM_ENGINE_STEP.UniformLengthCapacity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointKernelBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integrability of the actual Fourier children from their raw terms

A fixed finite carrier contains the actual rows and every actual plain and
prime support.  Only individual normalized summands receive polynomial
growth and measurability hypotheses.  Finite summation, multiplication,
and the row indicator prove the bound and measurability of the literal
paired energy internally.  Schwartz Fourier decay then proves
integrability for its genuine positive Fourier measure.

Only a common slot count is used.  Prime profiles, their supports, all
coefficients, and the twist may vary with the Fourier parameter.
-/

noncomputable section
open scoped Classical BigOperators FourierTransform SchwartzMap NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- One original normalized plain summand, with its own exact support. -/
def actualPlainAtom (d : MomentData K ω ψ) (W : IdealTest K)
    (u : NonzeroIdeal K) (N t : ℝ) (I : NonzeroIdeal K) : ℂ :=
  if I ∈ W.support u t N then
    (Real.sqrt N : ℂ)⁻¹ * heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
      W.profile u t (idealNorm K I / N) * maskValue d u I.val
  else 0

/-- One original normalized prime summand, with its own exact support. -/
def actualPrimeAtom (d : MomentData K ω ψ) (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (Z t : ℝ) (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  let P := Z ^ (d.geometry.slots i).length
  if p ∈ (d.geometry.slots i).support t P then
    (Real.sqrt P : ℂ)⁻¹ * primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
      (d.geometry.slots i).profile t ((Ideal.absNorm p.asIdeal : ℝ) / P) *
      maskValue d u p.asIdeal
  else 0

def actualPairedRowIndicator (d : MomentData K ω ψ) (a : RealParameters)
    (Z : ℝ) (u : NonzeroIdeal K) : ℂ :=
  if u ∈ pairedRows d a Z then 1 else 0

theorem actualPlainPolynomial_eq_carrier_sum (d : MomentData K ω ψ) (W : IdealTest K)
    (u : NonzeroIdeal K) (N t : ℝ) (carrier : Finset (NonzeroIdeal K))
    (hcarrier : W.support u t N ⊆ carrier) :
    plainPolynomial d W u N t = ∑ I ∈ carrier, actualPlainAtom d W u N t I := by
  calc
    _ = ∑ I ∈ W.support u t N, actualPlainAtom d W u N t I := by
      unfold plainPolynomial
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      simp only [actualPlainAtom, if_pos hI]
      ring
    _ = _ := Finset.sum_subset hcarrier
      (fun I _ hI => by simp only [actualPlainAtom, if_neg hI])

theorem actualPrimePolynomial_eq_carrier_sum (d : MomentData K ω ψ)
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal K) (Z t : ℝ)
    (carrier : Finset (HeightOneSpectrum (𝓞 K)))
    (hcarrier : (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length) ⊆ carrier) :
    primePolynomial d i u Z t = ∑ p ∈ carrier, actualPrimeAtom d i u Z t p := by
  calc
    _ = ∑ p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length),
        actualPrimeAtom d i u Z t p := by
      unfold primePolynomial
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [actualPrimeAtom, if_pos hp]
      ring
    _ = _ := Finset.sum_subset hcarrier
      (fun p _ hp => by simp only [actualPrimeAtom, if_neg hp])

theorem actualSlotProduct_reindex (d : MomentData K ω ψ) (n : ℕ)
    (hcount : d.geometry.slotCount = n) (u : NonzeroIdeal K) (Z t : ℝ) :
    slotProduct d u Z t = ∏ i : Fin n, primePolynomial d (lengthSlot d n hcount i) u Z t := by
  subst n
  rfl

theorem actualPairedEnergy_eq_carrier_sum (d : MomentData K ω ψ)
    (a : RealParameters) (Z t : ℝ) (carrier : Finset (NonzeroIdeal K))
    (hcarrier : pairedRows d a Z ⊆ carrier) :
    pairedEnergy d a Z t = ∑ u ∈ carrier,
      ‖actualPairedRowIndicator d a Z u *
        (plainPolynomial d d.plainTest₁ u (Z ^ a.n₁) t *
          plainPolynomial d d.plainTest₂ u (Z ^ a.n₂) t * slotProduct d u Z t)‖ ^ 2 := by
  calc
    _ = ∑ u ∈ pairedRows d a Z,
        ‖actualPairedRowIndicator d a Z u *
          (plainPolynomial d d.plainTest₁ u (Z ^ a.n₁) t *
            plainPolynomial d d.plainTest₂ u (Z ^ a.n₂) t * slotProduct d u Z t)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [actualPairedRowIndicator, if_pos hu, one_mul]
    _ = _ := Finset.sum_subset hcarrier
      (fun u _ hu => by simp only [actualPairedRowIndicator, if_neg hu, zero_mul, norm_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0)])

theorem norm_finite_sum_le_card {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (B : ℝ) (h : ∀ i ∈ s, ‖f i‖ ≤ B) :
    ‖∑ i ∈ s, f i‖ ≤ (s.card : ℝ) * B := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum h
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

section RawFamily

variable {V : Type*} [NormedAddCommGroup V] [MeasureSpace V]

/-- Raw finite carrier and individual-summand information only.  This
structure contains no energy estimate or integrability assertion. -/
structure ActualFiniteFamilyControl (D : V → MomentData K ω ψ)
    (n : ℕ) (hcount : ∀ ξ, (D ξ).geometry.slotCount = n)
    (a : RealParameters) (Z : ℝ) (t : V → ℝ) where
  rows : Finset (NonzeroIdeal K)
  plain₁ : Finset (NonzeroIdeal K)
  plain₂ : Finset (NonzeroIdeal K)
  primes : Fin n → Finset (HeightOneSpectrum (𝓞 K))
  rows_cover : ∀ ξ, pairedRows (D ξ) a Z ⊆ rows
  plain₁_cover : ∀ ξ u, u ∈ rows →
    (D ξ).plainTest₁.support u (t ξ) (Z ^ a.n₁) ⊆ plain₁
  plain₂_cover : ∀ ξ u, u ∈ rows →
    (D ξ).plainTest₂.support u (t ξ) (Z ^ a.n₂) ⊆ plain₂
  primes_cover : ∀ ξ i,
    ((D ξ).geometry.slots (lengthSlot (D ξ) n (hcount ξ) i)).support (t ξ)
      (Z ^ ((D ξ).geometry.slots (lengthSlot (D ξ) n (hcount ξ) i)).length) ⊆ primes i
  order : ℕ
  plain₁Bound : ℝ
  plain₂Bound : ℝ
  primeBound : Fin n → ℝ
  plain₁_nonneg : 0 ≤ plain₁Bound
  plain₂_nonneg : 0 ≤ plain₂Bound
  prime_nonneg : ∀ i, 0 ≤ primeBound i
  row_measurable : ∀ u ∈ rows, AEStronglyMeasurable
    (fun ξ => actualPairedRowIndicator (D ξ) a Z u) (volume : Measure V)
  plain₁_measurable : ∀ u ∈ rows, ∀ I ∈ plain₁, AEStronglyMeasurable
    (fun ξ => actualPlainAtom (D ξ) (D ξ).plainTest₁ u (Z ^ a.n₁) (t ξ) I)
      (volume : Measure V)
  plain₂_measurable : ∀ u ∈ rows, ∀ I ∈ plain₂, AEStronglyMeasurable
    (fun ξ => actualPlainAtom (D ξ) (D ξ).plainTest₂ u (Z ^ a.n₂) (t ξ) I)
      (volume : Measure V)
  prime_measurable : ∀ u ∈ rows, ∀ i, ∀ p ∈ primes i, AEStronglyMeasurable
    (fun ξ => actualPrimeAtom (D ξ) (lengthSlot (D ξ) n (hcount ξ) i) u Z (t ξ) p)
      (volume : Measure V)
  plain₁_bound : ∀ ξ u, u ∈ rows → ∀ I ∈ plain₁,
    ‖actualPlainAtom (D ξ) (D ξ).plainTest₁ u (Z ^ a.n₁) (t ξ) I‖ ≤
      plain₁Bound * (1 + ‖ξ‖) ^ order
  plain₂_bound : ∀ ξ u, u ∈ rows → ∀ I ∈ plain₂,
    ‖actualPlainAtom (D ξ) (D ξ).plainTest₂ u (Z ^ a.n₂) (t ξ) I‖ ≤
      plain₂Bound * (1 + ‖ξ‖) ^ order
  prime_bound : ∀ ξ u, u ∈ rows → ∀ i, ∀ p ∈ primes i,
    ‖actualPrimeAtom (D ξ) (lengthSlot (D ξ) n (hcount ξ) i) u Z (t ξ) p‖ ≤
      primeBound i * (1 + ‖ξ‖) ^ order

namespace ActualFiniteFamilyControl

variable {D : V → MomentData K ω ψ} {n : ℕ}
variable {hcount : ∀ ξ, (D ξ).geometry.slotCount = n}
variable {a : RealParameters} {Z : ℝ} {t : V → ℝ}
variable (cal : ActualFiniteFamilyControl D n hcount a Z t)

def polynomialConstant : ℝ :=
  ((cal.plain₁.card : ℝ) * cal.plain₁Bound) *
    ((cal.plain₂.card : ℝ) * cal.plain₂Bound) *
      ∏ i : Fin n, (cal.primes i).card * cal.primeBound i

def polynomialOrder : ℕ := cal.order * (n + 2)
def energyConstant : ℝ := (cal.rows.card : ℝ) * cal.polynomialConstant ^ 2
def energyOrder : ℕ := cal.polynomialOrder * 2

theorem polynomialConstant_nonneg : 0 ≤ cal.polynomialConstant := by
  unfold polynomialConstant
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) cal.plain₁_nonneg)
      (mul_nonneg (Nat.cast_nonneg _) cal.plain₂_nonneg))
    (Finset.prod_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (cal.prime_nonneg i)))

theorem energyConstant_nonneg : 0 ≤ cal.energyConstant :=
  mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem plain₁_polynomial_bound (ξ : V) (u : NonzeroIdeal K) (hu : u ∈ cal.rows) :
    ‖plainPolynomial (D ξ) (D ξ).plainTest₁ u (Z ^ a.n₁) (t ξ)‖ ≤
      ((cal.plain₁.card : ℝ) * cal.plain₁Bound) * (1 + ‖ξ‖) ^ cal.order := by
  rw [actualPlainPolynomial_eq_carrier_sum _ _ _ _ _ cal.plain₁ (cal.plain₁_cover ξ u hu)]
  exact (norm_finite_sum_le_card _ _ _ (cal.plain₁_bound ξ u hu)).trans_eq (by ring)

theorem plain₂_polynomial_bound (ξ : V) (u : NonzeroIdeal K) (hu : u ∈ cal.rows) :
    ‖plainPolynomial (D ξ) (D ξ).plainTest₂ u (Z ^ a.n₂) (t ξ)‖ ≤
      ((cal.plain₂.card : ℝ) * cal.plain₂Bound) * (1 + ‖ξ‖) ^ cal.order := by
  rw [actualPlainPolynomial_eq_carrier_sum _ _ _ _ _ cal.plain₂ (cal.plain₂_cover ξ u hu)]
  exact (norm_finite_sum_le_card _ _ _ (cal.plain₂_bound ξ u hu)).trans_eq (by ring)

theorem prime_polynomial_bound (ξ : V) (u : NonzeroIdeal K) (hu : u ∈ cal.rows) (i : Fin n) :
    ‖primePolynomial (D ξ) (lengthSlot (D ξ) n (hcount ξ) i) u Z (t ξ)‖ ≤
      (((cal.primes i).card : ℝ) * cal.primeBound i) * (1 + ‖ξ‖) ^ cal.order := by
  rw [actualPrimePolynomial_eq_carrier_sum _ _ _ _ _ (cal.primes i) (cal.primes_cover ξ i)]
  exact (norm_finite_sum_le_card _ _ _ (cal.prime_bound ξ u hu i)).trans_eq (by ring)

theorem slot_polynomial_bound (ξ : V) (u : NonzeroIdeal K) (hu : u ∈ cal.rows) :
    ‖slotProduct (D ξ) u Z (t ξ)‖ ≤
      (∏ i : Fin n, ((cal.primes i).card : ℝ) * cal.primeBound i) *
        (1 + ‖ξ‖) ^ (cal.order * n) := by
  rw [actualSlotProduct_reindex (D ξ) n (hcount ξ), norm_prod]
  apply (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
    (fun i _ => cal.prime_polynomial_bound ξ u hu i)).trans_eq
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

theorem row_polynomial_bound (ξ : V) (u : NonzeroIdeal K) (hu : u ∈ cal.rows) :
    ‖plainPolynomial (D ξ) (D ξ).plainTest₁ u (Z ^ a.n₁) (t ξ) *
      plainPolynomial (D ξ) (D ξ).plainTest₂ u (Z ^ a.n₂) (t ξ) *
      slotProduct (D ξ) u Z (t ξ)‖ ≤
      cal.polynomialConstant * (1 + ‖ξ‖) ^ cal.polynomialOrder := by
  have hp : 0 ≤ (1 + ‖ξ‖) ^ cal.order := pow_nonneg (by positivity) _
  have hB₁ : 0 ≤ ((cal.plain₁.card : ℝ) * cal.plain₁Bound) * (1 + ‖ξ‖) ^ cal.order :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) cal.plain₁_nonneg) hp
  have hB₂ : 0 ≤ ((cal.plain₂.card : ℝ) * cal.plain₂Bound) * (1 + ‖ξ‖) ^ cal.order :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) cal.plain₂_nonneg) hp
  rw [norm_mul, norm_mul]
  apply (mul_le_mul
    (mul_le_mul (cal.plain₁_polynomial_bound ξ u hu) (cal.plain₂_polynomial_bound ξ u hu)
      (norm_nonneg _) hB₁)
    (cal.slot_polynomial_bound ξ u hu) (norm_nonneg _) (mul_nonneg hB₁ hB₂)).trans_eq
  unfold polynomialConstant polynomialOrder
  rw [show cal.order * (n + 2) = cal.order + cal.order + cal.order * n by ring]
  rw [pow_add, pow_add]
  ring

/-- The genuine paired energy is polynomially bounded, proved by finite
algebra from individual raw terms, without a moment estimate. -/
theorem energy_polynomial_bound (ξ : V) :
    pairedEnergy (D ξ) a Z (t ξ) ≤
      cal.energyConstant * (1 + ‖ξ‖) ^ cal.energyOrder := by
  unfold pairedEnergy
  calc
    _ ≤ ∑ u ∈ cal.rows,
        ‖plainPolynomial (D ξ) (D ξ).plainTest₁ u (Z ^ a.n₁) (t ξ) *
          plainPolynomial (D ξ) (D ξ).plainTest₂ u (Z ^ a.n₂) (t ξ) *
          slotProduct (D ξ) u Z (t ξ)‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (cal.rows_cover ξ) (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ _u ∈ cal.rows,
        (cal.polynomialConstant * (1 + ‖ξ‖) ^ cal.polynomialOrder) ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      have hb := cal.row_polynomial_bound ξ u hu
      have hp : 0 ≤ cal.polynomialConstant * (1 + ‖ξ‖) ^ cal.polynomialOrder :=
        mul_nonneg cal.polynomialConstant_nonneg (pow_nonneg (by positivity) _)
      nlinarith [norm_nonneg
        (plainPolynomial (D ξ) (D ξ).plainTest₁ u (Z ^ a.n₁) (t ξ) *
          plainPolynomial (D ξ) (D ξ).plainTest₂ u (Z ^ a.n₂) (t ξ) *
          slotProduct (D ξ) u Z (t ξ))]
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [energyConstant, energyOrder, pow_mul, mul_pow]
      ring

include cal in
theorem energy_aestronglyMeasurable :
    AEStronglyMeasurable (fun ξ => pairedEnergy (D ξ) a Z (t ξ)) (volume : Measure V) := by
  have hplain₁ (u : NonzeroIdeal K) (hu : u ∈ cal.rows) :
      AEStronglyMeasurable
        (fun ξ => plainPolynomial (D ξ) (D ξ).plainTest₁ u (Z ^ a.n₁) (t ξ))
          (volume : Measure V) := by
    apply (cal.plain₁.aestronglyMeasurable_fun_sum
      (fun I hI => cal.plain₁_measurable u hu I hI)).congr
    exact Filter.Eventually.of_forall fun ξ =>
      (actualPlainPolynomial_eq_carrier_sum _ _ _ _ _ cal.plain₁
        (cal.plain₁_cover ξ u hu)).symm
  have hplain₂ (u : NonzeroIdeal K) (hu : u ∈ cal.rows) :
      AEStronglyMeasurable
        (fun ξ => plainPolynomial (D ξ) (D ξ).plainTest₂ u (Z ^ a.n₂) (t ξ))
          (volume : Measure V) := by
    apply (cal.plain₂.aestronglyMeasurable_fun_sum
      (fun I hI => cal.plain₂_measurable u hu I hI)).congr
    exact Filter.Eventually.of_forall fun ξ =>
      (actualPlainPolynomial_eq_carrier_sum _ _ _ _ _ cal.plain₂
        (cal.plain₂_cover ξ u hu)).symm
  have hprime (u : NonzeroIdeal K) (hu : u ∈ cal.rows) (i : Fin n) :
      AEStronglyMeasurable
        (fun ξ => primePolynomial (D ξ) (lengthSlot (D ξ) n (hcount ξ) i) u Z (t ξ))
          (volume : Measure V) := by
    apply ((cal.primes i).aestronglyMeasurable_fun_sum
      (fun p hp => cal.prime_measurable u hu i p hp)).congr
    exact Filter.Eventually.of_forall fun ξ =>
      (actualPrimePolynomial_eq_carrier_sum _ _ _ _ _ (cal.primes i)
        (cal.primes_cover ξ i)).symm
  have hslot (u : NonzeroIdeal K) (hu : u ∈ cal.rows) :
      AEStronglyMeasurable (fun ξ => slotProduct (D ξ) u Z (t ξ)) (volume : Measure V) := by
    apply (Finset.univ.aestronglyMeasurable_fun_prod
      (fun i _ => hprime u hu i)).congr
    exact Filter.Eventually.of_forall fun ξ =>
      (actualSlotProduct_reindex (D ξ) n (hcount ξ) u Z (t ξ)).symm
  have hsum := cal.rows.aestronglyMeasurable_fun_sum
    (fun u hu => ((cal.row_measurable u hu).mul
      (((hplain₁ u hu).mul (hplain₂ u hu)).mul (hslot u hu))).norm.pow 2)
  apply hsum.congr
  exact Filter.Eventually.of_forall fun ξ =>
    (actualPairedEnergy_eq_carrier_sum (D ξ) a Z (t ξ) cal.rows (cal.rows_cover ξ)).symm

end ActualFiniteFamilyControl

end RawFamily

section Family

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The actual positive measure used by the Fourier separation. -/
def actualFourierMeasure (F : 𝓢(V, ℂ)) : Measure V :=
  volume.withDensity (fun ξ => ENNReal.ofReal ‖(𝓕 F) ξ‖)

theorem actualFourierMeasure_finite (F : 𝓢(V, ℂ)) :
    IsFiniteMeasure (actualFourierMeasure F) := by
  obtain ⟨s, C, hC, hweight⟩ := joint_fourier_mass_bound (V := V) 0
  have hi : Integrable (fun ξ : V => ‖(𝓕 F) ξ‖) := by
    simpa only [pow_zero, mul_one] using (hweight F).1
  apply isFiniteMeasure_withDensity
  exact ((hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun ξ : V => norm_nonneg ((𝓕 F) ξ)))).mp
      hi.hasFiniteIntegral).ne

theorem actualFourierMeasure_mass_eq (F : 𝓢(V, ℂ)) :
    (actualFourierMeasure F).real Set.univ = ∫ ξ : V, ‖(𝓕 F) ξ‖ := by
  have hmeasure : (actualFourierMeasure F) Set.univ =
      ∫⁻ ξ : V, ENNReal.ofReal ‖(𝓕 F) ξ‖ ∂(volume : Measure V) := by
    simpa only [actualFourierMeasure, Measure.restrict_univ] using
      (Measure.withDensity_apply (μ := (volume : Measure V))
        (fun ξ : V => ENNReal.ofReal ‖(𝓕 F) ξ‖) MeasurableSet.univ)
  calc
    _ = (∫⁻ ξ : V, ENNReal.ofReal ‖(𝓕 F) ξ‖ ∂(volume : Measure V)).toReal :=
      congrArg ENNReal.toReal hmeasure
    _ = _ := (integral_eq_lintegral_of_nonneg_ae
      (μ := (volume : Measure V))
      (Filter.Eventually.of_forall (fun ξ : V => norm_nonneg ((𝓕 F) ξ)))
      (𝓕 F).continuous.norm.aestronglyMeasurable).symm

/-- The positive kernel's mass is controlled by fixed original Schwartz
seminorms, before choosing any actual child family. -/
theorem actualFourierMeasure_uniform_mass :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ F : 𝓢(V, ℂ),
      (actualFourierMeasure F).real Set.univ ≤
        C * s.sup (schwartzSeminormFamily ℝ V ℂ) F := by
  obtain ⟨s, C, hC, hweight⟩ := joint_fourier_mass_bound (V := V) 0
  refine ⟨s, C, hC, fun F => ?_⟩
  rw [actualFourierMeasure_mass_eq]
  simpa only [pow_zero, mul_one] using (hweight F).2

theorem actual_paired_family_integrable
    {D : V → MomentData K ω ψ} {n : ℕ}
    {hcount : ∀ ξ, (D ξ).geometry.slotCount = n}
    {a : RealParameters} {Z : ℝ} {t : V → ℝ}
    (cal : ActualFiniteFamilyControl D n hcount a Z t) (F : 𝓢(V, ℂ)) :
    Integrable (fun ξ => pairedEnergy (D ξ) a Z (t ξ)) (actualFourierMeasure F) := by
  obtain ⟨s, C, hC, hweight⟩ := joint_fourier_mass_bound (V := V) cal.energyOrder
  have hmajor := (hweight F).1.const_mul cal.energyConstant
  have hmeas : AEStronglyMeasurable
      (fun ξ => ‖(𝓕 F) ξ‖ * pairedEnergy (D ξ) a Z (t ξ)) (volume : Measure V) :=
    (𝓕 F).continuous.norm.aestronglyMeasurable.mul cal.energy_aestronglyMeasurable
  have hweighted : Integrable
      (fun ξ => ‖(𝓕 F) ξ‖ * pairedEnergy (D ξ) a Z (t ξ)) (volume : Measure V) := by
    apply hmajor.mono' hmeas
    exact Filter.Eventually.of_forall fun ξ => by
      have hE : 0 ≤ pairedEnergy (D ξ) a Z (t ξ) :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hE)]
      exact (mul_le_mul_of_nonneg_left (cal.energy_polynomial_bound ξ)
        (norm_nonneg _)).trans_eq (by ring)
  have hden : Measurable (fun ξ : V => ENNReal.ofReal ‖(𝓕 F) ξ‖) := by fun_prop
  apply (integrable_withDensity_iff_integrable_smul' hden
    (Filter.Eventually.of_forall (fun ξ : V => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul] using hweighted

theorem actual_normalized_paired_family_integrable
    {D : V → MomentData K ω ψ} {n : ℕ}
    {hcount : ∀ ξ, (D ξ).geometry.slotCount = n}
    {a : RealParameters} {Z : ℝ} {t : V → ℝ}
    (cal : ActualFiniteFamilyControl D n hcount a Z t) (F : 𝓢(V, ℂ)) :
    Integrable (fun ξ => normalizedPairedEnergy (D ξ) a Z (t ξ)) (actualFourierMeasure F) :=
  (actual_paired_family_integrable cal F).div_const (Z ^ (a.m + a.q))

/-- The Cauchy integrand is integrable under the same positive measure;
its proof uses only the two just-derived individual integrabilities. -/
theorem actual_normalized_cauchy_integrable
    {D₁ D₂ : V → MomentData K ω ψ} {n₁ n₂ : ℕ}
    {hc₁ : ∀ ξ, (D₁ ξ).geometry.slotCount = n₁}
    {hc₂ : ∀ ξ, (D₂ ξ).geometry.slotCount = n₂}
    {a₁ a₂ : RealParameters} {Z : ℝ} (hZ : 0 < Z) {t₁ t₂ : V → ℝ}
    (cal₁ : ActualFiniteFamilyControl D₁ n₁ hc₁ a₁ Z t₁)
    (cal₂ : ActualFiniteFamilyControl D₂ n₂ hc₂ a₂ Z t₂) (F : 𝓢(V, ℂ)) :
    Integrable (fun ξ =>
      Real.sqrt (normalizedPairedEnergy (D₁ ξ) a₁ Z (t₁ ξ)) *
        Real.sqrt (normalizedPairedEnergy (D₂ ξ) a₂ Z (t₂ ξ))) (actualFourierMeasure F) := by
  have hleft := actual_normalized_paired_family_integrable cal₁ F
  have hright := actual_normalized_paired_family_integrable cal₂ F
  have hmeas := (Real.continuous_sqrt.comp_aestronglyMeasurable hleft.aestronglyMeasurable).mul
    (Real.continuous_sqrt.comp_aestronglyMeasurable hright.aestronglyMeasurable)
  apply ((hleft.add hright).div_const 2).mono' hmeas
  exact Filter.Eventually.of_forall fun ξ => by
    have hl := normalizedPairedEnergy_nonneg (D₁ ξ) a₁ Z (t₁ ξ) hZ
    have hr := normalizedPairedEnergy_nonneg (D₂ ξ) a₂ Z (t₂ ξ) hZ
    simp only [Pi.mul_apply, Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    nlinarith [Real.sq_sqrt hl, Real.sq_sqrt hr, sq_nonneg
      (Real.sqrt (normalizedPairedEnergy (D₁ ξ) a₁ Z (t₁ ξ)) -
        Real.sqrt (normalizedPairedEnergy (D₂ ξ) a₂ Z (t₂ ξ)))]

end Family

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualFiniteFamilyControl.energy_polynomial_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actualFourierMeasure_finite
#print axioms HeckeSkeleton.Moments.EngineStep.actualFourierMeasure_uniform_mass
#print axioms HeckeSkeleton.Moments.EngineStep.actual_paired_family_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.actual_normalized_paired_family_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.actual_normalized_cauchy_integrable

