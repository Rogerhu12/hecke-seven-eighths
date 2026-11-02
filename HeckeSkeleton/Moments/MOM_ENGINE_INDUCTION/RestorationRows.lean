import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryRestorationTail
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileControl

/-!
# Actual rowwise restoration pieces with uniform analytic constants

The two pieces are the literal finite-cutoff remainder and the literal
whole restored series. Their coefficients, conductor, inverse character
and remaining deletion set are constructed from the original moment row.
The six choices of background and piece share one proved Euler order and
constant, selected before all moment data and all moving rows.

The arithmetic calibration records an actual exterior row/sector
identification and the joint budget `N(u) N(R) ≤ U^width`. No moment or
terminal estimate is a field. In particular, the possibly large `q`
portion of the remaining ideal is never counted as a small boundary.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeConductorNorm
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum HeckePort.Moments.ReflectionMass
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The actual whole restoration series, with every D/H scale retained. -/
def restorationWholeSeries (a ai : Ideal (𝓞 K) → ℂ)
    (E : Finset (Ideal (𝓞 K))) (b : NonzeroIdeal K → ℂ)
    (background : HeckeCharacter K) (V : SmoothAnnularTest) (δ Q X : ℝ) : ℂ :=
  ∑ D ∈ E.powerset, ∑' H : SmoothIdeal E,
    let Y := Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)
    coefficient a ai E D H * ((Real.sqrt Y : ℂ)⁻¹ *
      ∑' I : NonzeroIdeal K, b I *
        ordinaryReflectedProfile K background V δ (idealNorm K I / Y))

/-- `true` is the genuine finite-cutoff tail; `false` is the genuine
whole-series terminal used for a very long original plain factor. -/
def restorationPiece (tail : Bool) (a ai : Ideal (𝓞 K) → ℂ)
    (E : Finset (Ideal (𝓞 K))) (b : NonzeroIdeal K → ℂ)
    (background : HeckeCharacter K) (V : SmoothAnnularTest)
    (δ Q X : ℝ) (J : ℕ) : ℂ :=
  if tail then ordinaryRestorationRemainder K a ai E b background V δ Q X J
  else restorationWholeSeries K a ai E b background V δ Q X

private def restorationWeight (tail : Bool) (A ε Y : ℝ)
    (E : Finset (Ideal (𝓞 K))) (J : ℕ) : ℝ :=
  Y ^ (A + 1 / 2) * (if tail then ((2 : ℝ) ^ J) ^ (1 - A) else 1) *
    (Ideal.absNorm (∏ P ∈ E, P) : ℝ) ^ ε

private def RawRestorationBound (background : HeckeCharacter K) (tail : Bool)
    (δ A ε : ℝ) (L : ℕ) (C : ℝ) : Prop :=
  ∀ (a ai : Ideal (𝓞 K) → ℂ), IdealCoeff a → IdealCoeff ai →
    ∀ (E : Finset (Ideal (𝓞 K))) (hE : ∀ P ∈ E, Prime P)
    (b : NonzeroIdeal K → ℂ), (∀ I, ‖b I‖ ≤ 1) →
    ∀ (V : SmoothAnnularTest) (Q X Y : ℝ), 0 < Q → 0 < X → 0 < Y →
    (∀ D ∈ E.powerset, ∀ H : SmoothIdeal E,
      Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val) ≤ Y) →
    ∀ J : ℕ, ‖restorationPiece K tail a ai E b background V δ Q X J‖ ≤
      C * testSeminorm V.toFun L A * restorationWeight K tail A ε Y E J

private theorem rawRestorationBound_exists
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (background : HeckeCharacter K) (tail : Bool) {δ A ε : ℝ}
    (hδ : 0 < δ) (hδA : δ ≤ A) (hA : 1 < A) (hε : 0 < ε) :
    ∃ L : ℕ, ∃ C : ℝ, 0 ≤ C ∧ RawRestorationBound K background tail δ A ε L C := by
  cases tail with
  | false =>
    obtain ⟨L, C, hC, h⟩ := ordinaryRestorationWhole_bound
      K hcomplex background hδ hδA hε
    refine ⟨L, C, hC, ?_⟩
    intro a ai ha hai E hE b hb V Q X Y hQ hX hY hscale J
    simpa only [restorationPiece, Bool.false_eq_true, if_false, restorationWholeSeries,
      restorationWeight, mul_one, mul_assoc] using
      h a ai ha hai E hE b hb V Q X Y hQ hX hY hscale
  | true =>
    obtain ⟨L, C, hC, h⟩ := ordinaryRestorationRemainder_bound
      K hcomplex background hδ hδA hA hε
    refine ⟨L, C, hC, ?_⟩
    intro a ai ha hai E hE b hb V Q X Y hQ hX hY hscale J
    simpa only [restorationPiece, if_true, restorationWeight, mul_assoc] using
      (h a ai ha hai E hE b hb V Q X Y hQ hX hY hscale J).2

private theorem RawRestorationBound.mono
    {background : HeckeCharacter K} {tail : Bool} {δ A ε C D : ℝ} {L N : ℕ}
    (h : RawRestorationBound K background tail δ A ε L C)
    (hC : 0 ≤ C) (hL : L ≤ N) (hD : C ≤ D) :
    RawRestorationBound K background tail δ A ε N D := by
  intro a ai ha hai E hE b hb V Q X Y hQ hX hY hscale J
  have hw : 0 ≤ restorationWeight K tail A ε Y E J := by
    unfold restorationWeight
    cases tail <;> simp only [Bool.false_eq_true, if_false, if_true] <;> positivity
  apply (h a ai ha hai E hE b hb V Q X Y hQ hX hY hscale J).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hD (testSeminorm_mono_order V.toFun A hL)
      (testSeminorm_nonneg V.toFun L A) (hC.trans hD)) hw

private theorem rawRestorationBound_uniform
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (ψ : HeckeCharacter K)
    {δ A ε : ℝ} (hδ : 0 < δ) (hδA : δ ≤ A) (hA : 1 < A) (hε : 0 < ε) :
    ∃ L : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ background : HeckeCharacter K,
      (background = 1 ∨ background = ψ ∨ background = ψ⁻¹) →
      ∀ tail : Bool, RawRestorationBound K background tail δ A ε L C := by
  let background : Fin 3 → HeckeCharacter K :=
    fun i => if i = 0 then 1 else if i = 1 then ψ else ψ⁻¹
  have hex (i : Fin 3 × Bool) : ∃ L : ℕ, ∃ C : ℝ,
      0 ≤ C ∧ RawRestorationBound K (background i.1) i.2 δ A ε L C :=
    rawRestorationBound_exists K hcomplex (background i.1) i.2 hδ hδA hA hε
  choose order constant hconstant hbound using hex
  let L : ℕ := ∑ i : Fin 3 × Bool, order i
  let C : ℝ := ∑ i : Fin 3 × Bool, constant i
  have hc : 0 ≤ C := Finset.sum_nonneg (fun i _ => hconstant i)
  have hi (i : Fin 3 × Bool) : RawRestorationBound K (background i.1) i.2 δ A ε L C := by
    apply RawRestorationBound.mono K (hbound i) (hconstant i)
    · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    · exact Finset.single_le_sum (fun k _ => hconstant k) (Finset.mem_univ i)
  refine ⟨L, C, hc, ?_⟩
  intro β hβ tail
  rcases hβ with rfl | rfl | rfl
  · simpa only [background, if_pos rfl] using hi (0, tail)
  · simpa [background] using hi (1, tail)
  · simpa [background] using hi (2, tail)

variable {K} {ω ψ : HeckeCharacter K}

/-- All original remaining exclusions are kept; conductor primes are
removed only by the already proved exact coefficient identity. -/
def rowRestorationDeletion (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (d : MomentData K ω ψ) (extra : NonzeroIdeal K → NonzeroIdeal K)
    (u : NonzeroIdeal K) : Finset (Ideal (𝓞 K)) :=
  remainingRowDeletionPrimes S u (extra u) \
    primeSupport (finiteConductor K (d.plainBackground * d.rowCharacter u)).val

theorem rowRestorationDeletion_prime
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (d : MomentData K ω ψ) (extra : NonzeroIdeal K → NonzeroIdeal K)
    (u : NonzeroIdeal K) :
    ∀ P ∈ rowRestorationDeletion S d extra u, Prime P :=
  fun P hP => remainingRowDeletionPrimes_prime S u (extra u) P (Finset.mem_sdiff.mp hP).1

/-- Primitive source calibration for the actual rows and remaining mask.
The stronger joint budget is separate from `rows_spec`. -/
structure ReflectionRowCalibration
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (node : Node K ω ψ) (extra : NonzeroIdeal K → NonzeroIdeal K) (U : ℝ) : Prop where
  identify : ∀ u ∈ pairedRows node.data node.parameters U,
    ∃ v : ExteriorIdeal K S, v.val = u ∧ ∃ ξ : SixthUnitClasses K S,
      node.data.rowCharacter u = completeIdealRowCharacter K S P R ξ u
  product_budget : ∀ u ∈ pairedRows node.data node.parameters U,
    idealNorm K u * idealNorm K (extra u) ≤ U ^ node.width

/-- Both local scalar bounds follow from the joint primitive budget;
neither an energy bound nor an externally postulated dual scale is used. -/
theorem ReflectionRowCalibration.scalar_bounds
    {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
    {P : ProbeData K S} {R : RowCharacterInput K S P}
    {node : Node K ω ψ} {extra : NonzeroIdeal K → NonzeroIdeal K} {U c : ℝ}
    (cal : ReflectionRowCalibration S P R node extra U)
    (hU : 1 < U) (hfixed : uniformReflectionConductorConstant S ψ ≤ U ^ c)
    (u : NonzeroIdeal K) (hu : u ∈ pairedRows node.data node.parameters U) :
    (Ideal.absNorm (∏ p ∈ rowRestorationDeletion S node.data extra u, p) : ℝ) ≤
        U ^ (node.width + c) ∧
      ∀ long : ℝ, ∀ D ∈ (rowRestorationDeletion S node.data extra u).powerset,
        ∀ H : SmoothIdeal (rowRestorationDeletion S node.data extra u),
          heckeConductorScale K (node.data.plainBackground * node.data.rowCharacter u) *
              (Ideal.absNorm (∏ p ∈ D, p) : ℝ) / (U ^ long * inorm H.val) ≤
            U ^ (node.width - long + c) := by
  obtain ⟨v, hv, ξ, hrow⟩ := cal.identify u hu
  have hrow' : node.data.rowCharacter v.val = completeIdealRowCharacter K S P R ξ v.val := by
    simpa only [hv] using hrow
  have hbudget : idealNorm K v.val * idealNorm K (extra u) ≤ U ^ node.width := by
    simpa only [hv] using cal.product_budget u hu
  constructor
  · simpa only [rowRestorationDeletion, hv] using
      actual_remainingProduct_rpow_le S P R node ξ v (extra u) hrow' hU hfixed hbudget
  · intro long D hD H
    have hD' : D ⊆ remainingRowDeletionPrimes S v.val (extra u) \
        primeSupport (finiteConductor K
          (node.data.plainBackground * node.data.rowCharacter v.val)).val := by
      simpa only [rowRestorationDeletion, hv] using Finset.mem_powerset.mp hD
    simpa only [hv] using actual_reflectedScale_rpow_le_of_row_product
      S P R node ξ v (extra u) hrow' (n := long) hU hfixed hbudget D hD' H.val

/-- Literal tail or whole-series piece of the original row. -/
def rowRestorationPiece (tail : Bool)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (d : MomentData K ω ψ) (extra : NonzeroIdeal K → NonzeroIdeal K)
    (V : NonzeroIdeal K → SmoothAnnularTest)
    (δ U long : ℝ) (J : ℕ) (u : NonzeroIdeal K) : ℂ :=
  let χ := d.plainBackground * d.rowCharacter u
  let a := idealCoefficient (primeCoefficient K χ)
  let ai := idealCoefficient (primeCoefficient K χ⁻¹)
  let E := rowRestorationDeletion S d extra u
  restorationPiece K tail a ai E (fun I => excl E ai I.val) χ (V u) δ
    (heckeConductorScale K χ) (U ^ long) J

private theorem rowRestorationPiece_background
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (tail : Bool)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (d : MomentData K ω ψ) (extra : NonzeroIdeal K → NonzeroIdeal K)
    (V : NonzeroIdeal K → SmoothAnnularTest)
    (δ U long : ℝ) (J : ℕ) (u : NonzeroIdeal K) :
    rowRestorationPiece tail S d extra V δ U long J u =
      let χ := d.plainBackground * d.rowCharacter u
      let a := idealCoefficient (primeCoefficient K χ)
      let ai := idealCoefficient (primeCoefficient K χ⁻¹)
      let E := rowRestorationDeletion S d extra u
      restorationPiece K tail a ai E (fun I => excl E ai I.val) d.plainBackground (V u) δ
        (heckeConductorScale K χ) (U ^ long) J := by
  unfold rowRestorationPiece restorationPiece ordinaryRestorationRemainder
    ordinaryReflectedRemainder restorationWholeSeries
  simp_rw [ordinaryReflectedProfile_mul_finiteOrder K hcomplex
    d.plainBackground (d.rowCharacter u) (d.rowCharacter_finite u)]

/-- Pure analytic restoration estimate from its two scalar arithmetic
inputs. Both are lower-level conductor/deletion statements; no energy,
terminal or moment bound is a premise. The canonical complete and moving
row calibrations prove these inputs separately. -/
theorem uniform_rowRestorationPiece_bound_of_scalars
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (ψ : HeckeCharacter K)
    {δ A ε : ℝ} (hδ : 0 < δ) (hδA : δ ≤ A) (hA : 1 < A) (hε : 0 < ε) :
    ∃ L : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
      {omega : HeckeCharacter K} (node : Node K omega ψ)
      (extra : NonzeroIdeal K → NonzeroIdeal K) (V : NonzeroIdeal K → SmoothAnnularTest)
      (U c long loss : ℝ), 1 < U →
      (∀ u ∈ pairedRows node.data node.parameters U,
        (Ideal.absNorm (∏ p ∈ rowRestorationDeletion S node.data extra u, p) : ℝ) ≤
            U ^ (node.width + c) ∧
          ∀ length : ℝ, ∀ D ∈ (rowRestorationDeletion S node.data extra u).powerset,
            ∀ H : SmoothIdeal (rowRestorationDeletion S node.data extra u),
              heckeConductorScale K (node.data.plainBackground * node.data.rowCharacter u) *
                  (Ideal.absNorm (∏ p ∈ D, p) : ℝ) / (U ^ length * inorm H.val) ≤
                U ^ (node.width - length + c)) →
      ε * (node.width + c) ≤ loss →
      ∀ (tail : Bool) (J : ℕ) (u : NonzeroIdeal K),
      u ∈ pairedRows node.data node.parameters U →
      ‖rowRestorationPiece tail S node.data extra V δ U long J u‖ ≤
        C * testSeminorm (V u).toFun L A *
          U ^ ((A + 1 / 2) * (node.width - long + c) +
            (if tail then (1 - A) * reflectionDyadicExponent U J else 0) + loss) := by
  obtain ⟨L, C, hC, hbound⟩ := rawRestorationBound_uniform K hcomplex ψ hδ hδA hA hε
  refine ⟨L, C, hC, ?_⟩
  intro S instS omega node extra V U c long loss hU hscalars hloss tail J u hu
  have hU0 : 0 < U := zero_lt_one.trans hU
  let χ := node.data.plainBackground * node.data.rowCharacter u
  let a := idealCoefficient (primeCoefficient K χ)
  let ai := idealCoefficient (primeCoefficient K χ⁻¹)
  let E := rowRestorationDeletion S node.data extra u
  have ha : IdealCoeff a := heckeIdealCoeff_for_deletion χ
  have hai : IdealCoeff ai := heckeIdealCoeff_for_deletion χ⁻¹
  have hb (I : NonzeroIdeal K) : ‖excl E ai I.val‖ ≤ 1 := by
    by_cases hI : outside E I.val
    · simpa only [excl, if_pos hI] using hai.norm_le_one I.val
    · simp only [excl, if_neg hI, norm_zero, zero_le_one]
  obtain ⟨hmass, hscale⟩ := hscalars u hu
  have h := hbound node.data.plainBackground node.data.plain_background_spec tail
    a ai ha hai E (rowRestorationDeletion_prime S node.data extra u)
    (fun I => excl E ai I.val) hb (V u) (heckeConductorScale K χ) (U ^ long)
    (U ^ (node.width - long + c)) (conductorScale_pos K χ)
    (Real.rpow_pos_of_pos hU0 _) (Real.rpow_pos_of_pos hU0 _) (hscale long) J
  rw [rowRestorationPiece_background hcomplex]
  apply h.trans
  have hm : (Ideal.absNorm (∏ p ∈ E, p) : ℝ) ^ ε ≤ U ^ loss := by
    calc
      _ ≤ (U ^ (node.width + c)) ^ ε :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hmass hε.le
      _ = U ^ (ε * (node.width + c)) := by
        rw [← Real.rpow_mul hU0.le]
        congr 1
        ring
      _ ≤ U ^ loss := Real.rpow_le_rpow_of_exponent_le hU.le hloss
  have hw : restorationWeight K tail A ε (U ^ (node.width - long + c)) E J ≤
      U ^ ((A + 1 / 2) * (node.width - long + c) +
        (if tail then (1 - A) * reflectionDyadicExponent U J else 0) + loss) := by
    unfold restorationWeight
    calc
      _ ≤ (U ^ (node.width - long + c)) ^ (A + 1 / 2) *
          (if tail then ((2 : ℝ) ^ J) ^ (1 - A) else 1) * U ^ loss :=
        mul_le_mul_of_nonneg_left hm (by cases tail <;> simp only [Bool.false_eq_true,
          if_false, if_true] <;> positivity)
      _ = _ := by
        rw [← reflectionDyadicExponent_scale hU J]
        cases tail <;> simp only [Bool.false_eq_true, if_false, if_true, mul_one, add_zero]
        · rw [← Real.rpow_mul hU0.le, ← Real.rpow_add hU0]
          congr 1
          ring
        · rw [← Real.rpow_mul hU0.le, ← Real.rpow_mul hU0.le,
            ← Real.rpow_add hU0, ← Real.rpow_add hU0]
          congr 1
          ring
  exact mul_le_mul_of_nonneg_left hw
    (mul_nonneg hC (testSeminorm_nonneg (V u).toFun L A))


/-- Constants are fixed before all nodes, their original profiles,
remaining ideals and row sectors. The local upper scale and Euler mass
are deduced from `ReflectionRowCalibration`. -/
theorem uniform_rowRestorationPiece_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (ψ : HeckeCharacter K)
    {δ A ε : ℝ} (hδ : 0 < δ) (hδA : δ ≤ A) (hA : 1 < A) (hε : 0 < ε) :
    ∃ L : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
      (P : ProbeData K S) (R : RowCharacterInput K S P)
      {omega : HeckeCharacter K} (node : Node K omega ψ)
      (extra : NonzeroIdeal K → NonzeroIdeal K) (V : NonzeroIdeal K → SmoothAnnularTest)
      (U c long loss : ℝ), 1 < U →
      ReflectionRowCalibration S P R node extra U →
      uniformReflectionConductorConstant S ψ ≤ U ^ c →
      ε * (node.width + c) ≤ loss →
      ∀ (tail : Bool) (J : ℕ) (u : NonzeroIdeal K),
      u ∈ pairedRows node.data node.parameters U →
      ‖rowRestorationPiece tail S node.data extra V δ U long J u‖ ≤
        C * testSeminorm (V u).toFun L A *
          U ^ ((A + 1 / 2) * (node.width - long + c) +
            (if tail then (1 - A) * reflectionDyadicExponent U J else 0) + loss) := by
  obtain ⟨L, C, hC, hbound⟩ :=
    uniform_rowRestorationPiece_bound_of_scalars hcomplex ψ hδ hδA hA hε
  refine ⟨L, C, hC, ?_⟩
  intro S instS P R omega node extra V U c long loss hU cal hfixed hloss
  exact hbound S node extra V U c long loss hU
    (fun u hu => cal.scalar_bounds hU hfixed u hu) hloss

end HeckeSkeleton.Moments.EngineInduction
