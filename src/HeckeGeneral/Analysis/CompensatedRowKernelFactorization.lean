import HeckeGeneral.Analysis.PhysicalProbeContours

/-!
The full correction extracted from the ACTUAL finite-window, whole-index
subset compensation in compensatedRowMellinKernel. The factorization is
literal algebra for Z > 0; it needs no Euler calibration or zero-free input.
No local Euler sum, local correction, or prime polynomial is divided out.
This does not identify the correction with a product of local G_p factors,
prove its holomorphy, shift a contour, or bound any physical row sum.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators ComplexConjugate Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Every mark and every actual Euler table is retained inside the finite sum. -/
def compensatedRowFullCorrection (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ) (s w z : ℂ) : ℂ :=
  ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
    (∏ i : Fin g.slots, windowWeight K S g Z i (p i)) *
    ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
      let selected := subsetPrimeIdeal K S p J
      let marked := subsetPrimeIdeal K S p (Finset.univ \ J)
      (-1 : ℂ) ^ J.card * (exteriorNorm K S selected : ℂ) ^ (z - w - 1) *
        conj (heckeIdealCoefficient K ψ marked.val) *
        (exteriorNorm K S marked : ℂ) ^ (s + z - 1) *
        rowCorrection K S P ψ E ((Finset.univ \ J).image p) u s w z

private theorem selectedNorm_cpow (q : ℝ) (hq : 0 < q) (w z : ℂ) :
    (q : ℂ) ^ (-(3 / 2 : ℂ)) * ((q : ℂ) ^ (1 / 2 - z))⁻¹ *
        ((q : ℂ) ^ (w - 1))⁻¹ = (q : ℂ) ^ (z - w - 1) := by
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  rw [← Complex.cpow_neg, ← Complex.cpow_neg,
    ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
  congr 1
  ring

private theorem compensation_scale_factorization (X Y Z q r : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hq : 0 < q) (hr : 0 ≤ r)
    (s w z : ℂ) :
    (q : ℂ) ^ (-(3 / 2 : ℂ)) * ((X / q : ℝ) : ℂ) ^ (1 / 2 - z) *
        ((Z * r : ℝ) : ℂ) ^ (s + z - 1) * ((Y / q : ℝ) : ℂ) ^ (w - 1) =
      (X : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (s + z - 1) * (Y : ℂ) ^ (w - 1) *
        (q : ℂ) ^ (z - w - 1) * (r : ℂ) ^ (s + z - 1) := by
  rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hX hq.le,
    Complex.mul_cpow_ofReal_nonneg hZ hr,
    Complex.div_cpow_ofReal_nonneg hY hq.le]
  simp only [div_eq_mul_inv]
  calc
    _ = (X : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (s + z - 1) * (Y : ℂ) ^ (w - 1) *
        ((q : ℂ) ^ (-(3 / 2 : ℂ)) * ((q : ℂ) ^ (1 / 2 - z))⁻¹ *
          ((q : ℂ) ^ (w - 1))⁻¹) * (r : ℂ) ^ (s + z - 1) := by ring
    _ = _ := by
      rw [selectedNorm_cpow q hq w z]
      simp only [div_eq_mul_inv]

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]

omit [∀ p : S, BorelSpace (p.val.adicCompletion K)]
    [∀ p : S, (μ p).IsAddHaarMeasure] in
/-- Exact extraction of the common three deleted L-factors and scale factors.
The statement remains an equality at their zeros under Lean's total division;
no cancellation by an L-value or a local factor occurs in its proof. -/
theorem compensatedRowMellinKernel_factorization
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E : RowEulerData K S P)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ) (hZ : 0 < Z) (s w z : ℂ) :
    compensatedRowMellinKernel K S μ P ψ E g T u Z s w z =
      (physicalPoissonScalar K : ℂ) *
        Complex.exp ((s + z - 1) ^ 2) * additiveMellin K S μ P.additive z *
        mellin P.denominator.toFun w * (frequencyRowNorm K S u : ℂ) ^ (-z) *
        ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z) *
        (Z : ℂ) ^ (s + z - 1) *
        ((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ^ (w - 1) *
        (heckeDeletedContinuation K 1 (exceptionalPrimes K S) (6 * z) *
          heckeDeletedContinuation K (E.rows.character u) (exceptionalPrimes K S) w /
          heckeDeletedContinuation K (ψ * conjugate (E.rows.character u))
            (exceptionalPrimes K S) s) *
        compensatedRowFullCorrection K S P ψ E g T u Z s w z /
        (physicalResidueNormalizer K S μ P * primeNormalizer K S g T Z) := by
  let A : ℂ := ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z) *
    (Z : ℂ) ^ (s + z - 1) * ((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ^ (w - 1)
  let L : ℂ := heckeDeletedContinuation K 1 (exceptionalPrimes K S) (6 * z) *
    heckeDeletedContinuation K (E.rows.character u) (exceptionalPrimes K S) w /
    heckeDeletedContinuation K (ψ * conjugate (E.rows.character u))
      (exceptionalPrimes K S) s
  have hsum :
      (∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        (∏ i : Fin g.slots, windowWeight K S g Z i (p i)) *
        ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
          let selected := subsetPrimeIdeal K S p J
          let marked := subsetPrimeIdeal K S p (Finset.univ \ J)
          (-1 : ℂ) ^ J.card * (exteriorNorm K S selected : ℂ) ^ (-(3 / 2 : ℂ)) *
            conj (heckeIdealCoefficient K ψ marked.val) *
            ((Z ^ (17 / 48 : ℝ) / exteriorNorm K S selected : ℝ) : ℂ) ^ (1 / 2 - z) *
            ((Z * exteriorNorm K S marked : ℝ) : ℂ) ^ (s + z - 1) *
            ((Z ^ (23 / 48 : ℝ) / exteriorNorm K S selected : ℝ) : ℂ) ^ (w - 1) *
            rowEulerContinuation K S P ψ E ((Finset.univ \ J).image p) u s w z) =
        (A * L) * compensatedRowFullCorrection K S P ψ E g T u Z s w z := by
    unfold compensatedRowFullCorrection
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro J hJ
    have hq : 0 < exteriorNorm K S (subsetPrimeIdeal K S p J) :=
      idealNorm_pos K (subsetPrimeIdeal K S p J).val
    have hr : 0 < exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) :=
      idealNorm_pos K (subsetPrimeIdeal K S p (Finset.univ \ J)).val
    have hscale := compensation_scale_factorization
      (Z ^ (17 / 48 : ℝ)) (Z ^ (23 / 48 : ℝ)) Z
      (exteriorNorm K S (subsetPrimeIdeal K S p J))
      (exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)))
      (Real.rpow_nonneg hZ.le _) (Real.rpow_nonneg hZ.le _) hZ.le hq hr.le s w z
    unfold rowEulerContinuation
    dsimp only [A, L]
    linear_combination
      (∏ i : Fin g.slots, windowWeight K S g Z i (p i)) *
        (-1 : ℂ) ^ J.card * conj (heckeIdealCoefficient K ψ
          (subsetPrimeIdeal K S p (Finset.univ \ J)).val) *
        (heckeDeletedContinuation K 1 (exceptionalPrimes K S) (6 * z) *
          heckeDeletedContinuation K (E.rows.character u) (exceptionalPrimes K S) w /
          heckeDeletedContinuation K (ψ * conjugate (E.rows.character u))
            (exceptionalPrimes K S) s) *
        rowCorrection K S P ψ E ((Finset.univ \ J).image p) u s w z * hscale
  unfold compensatedRowMellinKernel
  rw [hsum]
  dsimp only [A, L]
  ring

end HeckeGeneral.ThetaSkeleton.Physical
