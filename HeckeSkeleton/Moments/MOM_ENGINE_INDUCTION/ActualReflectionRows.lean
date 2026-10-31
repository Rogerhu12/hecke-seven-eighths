import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RestorationRows
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryRowReflection
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.NormalizedPowerWindowEnergy

/-!
# The literal original row as normalized common-frequency children

The finite conductor pruning is an exact coefficient identity.  The
inverse dual coefficient therefore has precisely the original common
mask, including the remaining ideal and the entire original row ideal.
The genuine functional equation and restoration operator can then be
inserted into either actual plain factor.  The other plain factor and
all prime slots remain inside the child row, never in its scalar density.

Only primitive mask, character, profile and scale calibrations are inputs.
There is no reflected-polynomial identity or moment estimate assumed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeConductorNorm
open HeckePort.Moments HeckePort.Moments.ReflectionMass
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

/-- Pruning actual conductor primes does not lose the original dual mask.
The coefficient equality is pointwise on the identical original ideal. -/
theorem rowRestorationDualCoefficient_eq
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (d : MomentData K omegaCharacter psiCharacter)
    (extra : NonzeroIdeal K → NonzeroIdeal K) (u : NonzeroIdeal K)
    (hmask : ∀ I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val))) :
    (fun I : NonzeroIdeal K => excl (rowRestorationDeletion S d extra u)
      (idealCoefficient (primeCoefficient K (d.plainBackground * d.rowCharacter u)⁻¹)) I.val) =
      (fun I : NonzeroIdeal K =>
        heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u)⁻¹ I * maskValue d u I.val) := by
  funext I
  let χ := d.plainBackground * d.rowCharacter u
  let P := remainingRowDeletionPrimes S u (extra u)
  have hprune := excl_heckeCoefficient_conductor_sdiff χ⁻¹ P I.val
  rw [finiteConductor_inv] at hprune
  change excl (P \ HeckePort.IdealMobiusDivisorSum.primeSupport (finiteConductor K χ).val)
      (idealCoefficient (primeCoefficient K χ⁻¹)) I.val =
    idealCoefficient (primeCoefficient K χ⁻¹) I.val * maskValue d u I.val
  rw [← hprune, maskValue_eq_remaining_deletion d S u (extra u) hmask I]
  by_cases hI : outside P I.val
  · simp only [excl, if_pos hI, mul_one]
  · simp only [excl, if_neg hI, mul_zero]

/-- The selected literal plain polynomial is the genuine restoration
tail plus finitely many common-frequency dual columns. -/
theorem plainPolynomial_row_commonFrequency
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (d : MomentData K omegaCharacter psiCharacter) (W : IdealTest K)
    (extra : NonzeroIdeal K → NonzeroIdeal K)
    (V : NonzeroIdeal K → SmoothAnnularTest) (u : NonzeroIdeal K)
    (hmask : ∀ I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val)))
    (hcharacter : ∀ t : ℝ, d.plainBackground * d.rowCharacter u ≠ heckeNormTwist K t)
    (hprofile : (V u).toFun = W.profile u 0)
    {δ U long Ymax : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 4)
    (hU : 0 < U) (hYmax : 0 < Ymax)
    (hscale : ∀ D ∈ (rowRestorationDeletion S d extra u).powerset,
      ∀ H : SmoothIdeal (rowRestorationDeletion S d extra u),
        heckeConductorScale K (d.plainBackground * d.rowCharacter u) *
          (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (U ^ long * inorm H.val) ≤ Ymax)
    (J : ℕ) (sigma : ℕ → ℝ)
    (hsigma : ∀ j ∈ Finset.range (J + 1), 1 / 4 ≤ sigma j ∧ sigma j ≤ 3 / 4) :
    let χ := d.plainBackground * d.rowCharacter u
    let b := idealCoefficient (primeCoefficient K χ)
    let bi := idealCoefficient (primeCoefficient K χ⁻¹)
    let E := rowRestorationDeletion S d extra u
    let Q := heckeConductorScale K χ
    ∃ G : ℂ, ‖G‖ = 1 ∧
      plainPolynomial d W u (U ^ long) 0 =
        G * rowRestorationPiece true S d extra V δ U long J u +
          G * ∑ j ∈ Finset.range (J + 1), ∫ frequency : ℝ,
            ordinaryReflectionDensity K χ (V u) b bi E Q (U ^ long) ((2 : ℝ) ^ j)
                (sigma j) frequency *
              ordinaryDualPowerColumn d u (sigma j) ((2 : ℝ) ^ j) frequency := by
  dsimp only
  let χ := d.plainBackground * d.rowCharacter u
  let b := idealCoefficient (primeCoefficient K χ)
  let bi := idealCoefficient (primeCoefficient K χ⁻¹)
  let E := rowRestorationDeletion S d extra u
  let Q := heckeConductorScale K χ
  have hsource : plainPolynomial d W u (U ^ long) 0 =
      plainPoly (excl E b) (V u).toFun (U ^ long) := by
    simpa only [E, rowRestorationDeletion, b, χ, hprofile] using
      plainPolynomial_eq_remaining_pruned_sum d W S u (extra u) hmask (U ^ long) 0
  obtain ⟨G, hG, hFE⟩ := deletedHeckePlainPoly_commonFrequency K hcomplex χ hcharacter
    E (rowRestorationDeletion_prime S d extra u) (V u) hδ hδsmall
      (Real.rpow_pos_of_pos hU long) hYmax hscale J sigma hsigma
  refine ⟨G, hG, ?_⟩
  have hcoeff := rowRestorationDualCoefficient_eq S d extra u hmask
  have hop :
      (∑ j ∈ Finset.range (J + 1), ∫ frequency : ℝ,
        ordinaryReflectionDensity K χ (V u) b bi E Q (U ^ long) ((2 : ℝ) ^ j)
            (sigma j) frequency *
          ordinaryPowerColumn K (fun I => excl E bi I.val) (sigma j) ((2 : ℝ) ^ j) frequency) =
      ∑ j ∈ Finset.range (J + 1), ∫ frequency : ℝ,
        ordinaryReflectionDensity K χ (V u) b bi E Q (U ^ long) ((2 : ℝ) ^ j)
            (sigma j) frequency *
          ordinaryDualPowerColumn d u (sigma j) ((2 : ℝ) ^ j) frequency := by
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [] with frequency
    change _ * ordinaryPowerColumn K (fun I => excl E bi I.val) _ _ _ =
      _ * ordinaryPowerColumn K
        (fun I => heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u)⁻¹ I *
          maskValue d u I.val) _ _ _
    rw [hcoeff]
  calc
    _ = plainPoly (excl E b) (V u).toFun (U ^ long) := hsource
    _ = G * ordinaryRestorationRemainder K b bi E (fun I => excl E bi I.val)
        χ (V u) δ Q (U ^ long) J +
        G * ∑ j ∈ Finset.range (J + 1), ∫ frequency : ℝ,
          ordinaryReflectionDensity K χ (V u) b bi E Q (U ^ long) ((2 : ℝ) ^ j)
              (sigma j) frequency *
            ordinaryPowerColumn K (fun I => excl E bi I.val) (sigma j) ((2 : ℝ) ^ j) frequency := hFE
    _ = _ := by rw [hop]

/-- The very-long-factor branch uses the whole genuine restored series;
it need not manufacture a reflected child with a negative exponent. -/
theorem plainPolynomial_row_wholeReflection
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (d : MomentData K omegaCharacter psiCharacter) (W : IdealTest K)
    (extra : NonzeroIdeal K → NonzeroIdeal K)
    (V : NonzeroIdeal K → SmoothAnnularTest) (u : NonzeroIdeal K)
    (hmask : ∀ I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val)))
    (hcharacter : ∀ t : ℝ, d.plainBackground * d.rowCharacter u ≠ heckeNormTwist K t)
    (hprofile : (V u).toFun = W.profile u 0)
    {δ U long : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 4) (hU : 0 < U) (J : ℕ) :
    ∃ G : ℂ, ‖G‖ = 1 ∧
      plainPolynomial d W u (U ^ long) 0 =
        G * rowRestorationPiece false S d extra V δ U long J u := by
  let χ := d.plainBackground * d.rowCharacter u
  let E := rowRestorationDeletion S d extra u
  have hsource := plainPolynomial_eq_remaining_pruned_sum
    d W S u (extra u) hmask (U ^ long) 0
  rw [← hprofile] at hsource
  obtain ⟨G, hG, hFE⟩ := deletedHeckePlainPoly_ordinary_reflection K hcomplex χ hcharacter
    E (rowRestorationDeletion_prime S d extra u) (V u) hδ hδsmall
  refine ⟨G, hG, ?_⟩
  rw [hsource, (hFE (U ^ long) (Real.rpow_pos_of_pos hU long)).2]
  congr 1
  unfold rowRestorationPiece restorationPiece restorationWholeSeries
  simp only [Bool.false_eq_true, if_false]
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro H
  rw [reflectedTerm_eq_coefficient, plainPoly_eq_nonzeroSeries]

/-- Exact original paired-row decomposition, with the genuine tail and
the normalized density/row integrands.  Both original plain factors and
every prime slot stay inside the row.  The unit phase remains a scalar
coefficient and has no effect on the envelope bound. -/
theorem pairedRow_commonFrequency_normalized
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (d : MomentData K omegaCharacter psiCharacter) (a : RealParameters) (first : Bool)
    (extra : NonzeroIdeal K → NonzeroIdeal K)
    (V : NonzeroIdeal K → SmoothAnnularTest) (u : NonzeroIdeal K)
    (hmask : ∀ I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val)))
    (hcharacter : ∀ t : ℝ, d.plainBackground * d.rowCharacter u ≠ heckeNormTwist K t)
    (hprofile : (V u).toFun = (if first then d.plainTest₁ else d.plainTest₂).profile u 0)
    {δ U Ymax E0 : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 4)
    (hU : 0 < U) (hYmax : 0 < Ymax) (hE0 : 1 ≤ E0) (childOrder J : ℕ)
    (hscale : ∀ D ∈ (rowRestorationDeletion S d extra u).powerset,
      ∀ H : SmoothIdeal (rowRestorationDeletion S d extra u),
        heckeConductorScale K (d.plainBackground * d.rowCharacter u) *
          (Ideal.absNorm (∏ P ∈ D, P) : ℝ) /
            (U ^ (if first then a.n₁ else a.n₂) * inorm H.val) ≤ Ymax)
    (sigma lengths : ℕ → ℝ)
    (hsigma : ∀ j ∈ Finset.range (J + 1), 1 / 4 ≤ sigma j ∧ sigma j ≤ 3 / 4)
    (hlengths : ∀ j ∈ Finset.range (J + 1), U ^ lengths j = (2 : ℝ) ^ j) :
    let χ := d.plainBackground * d.rowCharacter u
    let b := idealCoefficient (primeCoefficient K χ)
    let bi := idealCoefficient (primeCoefficient K χ⁻¹)
    let E := rowRestorationDeletion S d extra u
    let Q := heckeConductorScale K χ
    let long := if first then a.n₁ else a.n₂
    let short := if first then plainPolynomial d d.plainTest₂ u (U ^ a.n₂) 0
      else plainPolynomial d d.plainTest₁ u (U ^ a.n₁) 0
    ∃ G : ℂ, ‖G‖ = 1 ∧
      plainPolynomial d d.plainTest₁ u (U ^ a.n₁) 0 *
          plainPolynomial d d.plainTest₂ u (U ^ a.n₂) 0 * slotProduct d u U 0 =
        G * rowRestorationPiece true S d extra V δ U long J u * short * slotProduct d u U 0 +
          ∑ j ∈ Finset.range (J + 1), ∫ frequency : ℝ,
            (G * normalizedOrdinaryReflectionDensity K E0 childOrder d.geometry.slotCount
              χ (V u) b bi E Q (U ^ long) ((2 : ℝ) ^ j) (sigma j) frequency) *
              normalizedOrdinaryDualRow d a first (sigma j) (lengths j) U 0 E0 childOrder u frequency := by
  dsimp only
  let χ := d.plainBackground * d.rowCharacter u
  let b := idealCoefficient (primeCoefficient K χ)
  let bi := idealCoefficient (primeCoefficient K χ⁻¹)
  let E := rowRestorationDeletion S d extra u
  let Q := heckeConductorScale K χ
  let long := if first then a.n₁ else a.n₂
  let W := if first then d.plainTest₁ else d.plainTest₂
  let short := if first then plainPolynomial d d.plainTest₂ u (U ^ a.n₂) 0
    else plainPolynomial d d.plainTest₁ u (U ^ a.n₁) 0
  obtain ⟨G, hG, hplain⟩ := plainPolynomial_row_commonFrequency hcomplex S d W extra V u
    hmask hcharacter hprofile hδ hδsmall hU hYmax hscale J sigma hsigma
  refine ⟨G, hG, ?_⟩
  have hparent :
      plainPolynomial d d.plainTest₁ u (U ^ a.n₁) 0 *
          plainPolynomial d d.plainTest₂ u (U ^ a.n₂) 0 * slotProduct d u U 0 =
        plainPolynomial d W u (U ^ long) 0 * short * slotProduct d u U 0 := by
    cases first <;> dsimp [W, long, short] <;> ring
  have hterm (j : ℕ) (hj : j ∈ Finset.range (J + 1)) :
      (G * ∫ frequency : ℝ,
        ordinaryReflectionDensity K χ (V u) b bi E Q (U ^ long) ((2 : ℝ) ^ j)
          (sigma j) frequency * ordinaryDualPowerColumn d u (sigma j) ((2 : ℝ) ^ j) frequency) *
            short * slotProduct d u U 0 =
      ∫ frequency : ℝ,
        (G * normalizedOrdinaryReflectionDensity K E0 childOrder d.geometry.slotCount
          χ (V u) b bi E Q (U ^ long) ((2 : ℝ) ^ j) (sigma j) frequency) *
          normalizedOrdinaryDualRow d a first (sigma j) (lengths j) U 0 E0 childOrder u frequency := by
    rw [← integral_const_mul, ← integral_mul_const, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with frequency
    conv_rhs =>
      rw [mul_assoc, normalizedOrdinaryDualRow_integrand d a first (sigma j) (lengths j)
        U 0 E0 hE0 childOrder u frequency χ (V u) b bi E Q (U ^ long) ((2 : ℝ) ^ j)]
    unfold ordinaryDualRow
    rw [hlengths j hj]
    cases first <;> dsimp [short] <;> ring
  calc
    _ = plainPolynomial d W u (U ^ long) 0 * short * slotProduct d u U 0 := hparent
    _ = (G * rowRestorationPiece true S d extra V δ U long J u +
        G * ∑ j ∈ Finset.range (J + 1), ∫ frequency : ℝ,
          ordinaryReflectionDensity K χ (V u) b bi E Q (U ^ long) ((2 : ℝ) ^ j)
              (sigma j) frequency *
            ordinaryDualPowerColumn d u (sigma j) ((2 : ℝ) ^ j) frequency) *
        short * slotProduct d u U 0 := by rw [hplain]
    _ = G * rowRestorationPiece true S d extra V δ U long J u * short * slotProduct d u U 0 +
        ∑ j ∈ Finset.range (J + 1),
          (G * ∫ frequency : ℝ,
            ordinaryReflectionDensity K χ (V u) b bi E Q (U ^ long) ((2 : ℝ) ^ j)
                (sigma j) frequency *
              ordinaryDualPowerColumn d u (sigma j) ((2 : ℝ) ^ j) frequency) *
            short * slotProduct d u U 0 := by
      rw [add_mul, add_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    _ = _ := by
      congr 1
      exact Finset.sum_congr rfl hterm

/-- Exact whole-series terminal for the original paired row.  Its
separate finite-row bound is proved by the restoration terminal ledger. -/
theorem pairedRow_wholeReflection
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (d : MomentData K omegaCharacter psiCharacter) (a : RealParameters) (first : Bool)
    (extra : NonzeroIdeal K → NonzeroIdeal K)
    (V : NonzeroIdeal K → SmoothAnnularTest) (u : NonzeroIdeal K)
    (hmask : ∀ I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val)))
    (hcharacter : ∀ t : ℝ, d.plainBackground * d.rowCharacter u ≠ heckeNormTwist K t)
    (hprofile : (V u).toFun = (if first then d.plainTest₁ else d.plainTest₂).profile u 0)
    {δ U : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 4) (hU : 0 < U) (J : ℕ) :
    let long := if first then a.n₁ else a.n₂
    let short := if first then plainPolynomial d d.plainTest₂ u (U ^ a.n₂) 0
      else plainPolynomial d d.plainTest₁ u (U ^ a.n₁) 0
    ∃ G : ℂ, ‖G‖ = 1 ∧
      plainPolynomial d d.plainTest₁ u (U ^ a.n₁) 0 *
          plainPolynomial d d.plainTest₂ u (U ^ a.n₂) 0 * slotProduct d u U 0 =
        G * rowRestorationPiece false S d extra V δ U long J u * short * slotProduct d u U 0 := by
  dsimp only
  let W := if first then d.plainTest₁ else d.plainTest₂
  obtain ⟨G, hG, hplain⟩ := plainPolynomial_row_wholeReflection hcomplex S d W extra V u
    hmask hcharacter hprofile hδ hδsmall hU J (long := if first then a.n₁ else a.n₂)
  refine ⟨G, hG, ?_⟩
  have h := congrArg (fun z : ℂ =>
    z * (if first then plainPolynomial d d.plainTest₂ u (U ^ a.n₂) 0
      else plainPolynomial d d.plainTest₁ u (U ^ a.n₁) 0) * slotProduct d u U 0) hplain
  cases first <;> dsimp [W] at h ⊢ <;> convert h using 1 <;> ring

end HeckeSkeleton.Moments.EngineInduction
