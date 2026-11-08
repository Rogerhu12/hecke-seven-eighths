module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bFirstColumnBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bMaskGeometry

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Paying the original first moving mask and every original deletion

The first fixed phase has prime support inside its actual common
support. The original pool factors at valuations one, six and seven
all retain the same prime radical. These statements apply before the
paid passive reduction. Together with the actual first deletion they
give a uniform bound for the literal mask used by exceptional charts.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid CommonSupportMass
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

namespace T3b

theorem primeSupport_mono {I J : Ideal (𝓞 K)} (hJ : J ≠ 0) (hd : I ∣ J) :
    primeSupport I ⊆ primeSupport J := by
  intro Q hQ
  have hmem : Q ∈ normalizedFactors I := by
    simpa only [primeSupport, Multiset.mem_toFinset] using hQ
  have hdiv : Q ∣ J := (dvd_of_mem_normalizedFactors hmem).trans hd
  change Q ∈ (normalizedFactors J).toFinset
  exact Multiset.mem_toFinset.mpr ((mem_normalizedFactors_iff hJ).mpr ⟨support_prime hQ, hdiv⟩)

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem firstPhaseRadical_dvd
    (primes : ι → ExteriorPrime A) (hp : Function.Injective primes)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (D : A.Exterior)
    (hD : D.val ∣ (primePowerProduct primes m).val)
    (e : HeckePort.Moments.Active.activeSupport Finset.univ m n → ℕ) :
    commonRadical
      (D.val * (primePowerProduct (firstActivePrimes primes m n) e).val)
      (D.val * (primePowerProduct (firstActivePrimes primes m n) e).val) ∣
        (primePowerProduct primes m).val := by
  rw [commonRadical, Finset.inter_self]
  apply support_product_dvd (primePowerProduct primes m).property.1
  intro Q hQ
  have hsplit : primeSupport
      (D.val * (primePowerProduct (firstActivePrimes primes m n) e).val) =
      primeSupport D.val ∪
        primeSupport (primePowerProduct (firstActivePrimes primes m n) e).val := by
    exact (congrArg Multiset.toFinset (normalizedFactors_mul D.property.1
      (primePowerProduct (firstActivePrimes primes m n) e).property.1)).trans
        (Multiset.toFinset_add _ _)
  rw [hsplit] at hQ
  rcases Finset.mem_union.mp hQ with hQ | hQ
  · exact primeSupport_mono (primePowerProduct primes m).property.1 hD hQ
  · rw [primePowerProduct_support_nonzero _ (firstActivePrimes_injective primes hp m n)] at hQ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
    rw [primePowerProduct_support primes hp m hm]
    exact Finset.mem_image.mpr ⟨i.val, Finset.mem_univ _, rfl⟩

private theorem firstMoving_support_dvd {σ : K →+* ℂ}
    {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
    (C : A.GeneralArithmeticContext σ η hS)
    (primes : ι → ExteriorPrime A) (hp : Function.Injective primes)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (D : A.Exterior)
    (hD : D.val ∣ (primePowerProduct primes m).val)
    (δ : A.R) (hδ : A.Generates D δ) (side : Bool) :
    (if side then CanonicalLiteralFirstPhase.rightMoving C P R primes m n D δ hδ
      else CanonicalLiteralFirstPhase.leftMoving C P R primes m n D δ hδ).support.val ∣
        (primePowerProduct primes m).val := by
  split_ifs
  · rw [CanonicalLiteralFirstPhase.rightMoving_support]
    exact firstPhaseRadical_dvd primes hp m n hm D hD _
  · rw [CanonicalLiteralFirstPhase.leftMoving_support]
    exact firstPhaseRadical_dvd primes hp m n hm D hD _

theorem singleton_one_support :
    (OriginalMovingFactors.singleton (P := P) (R := R) ⟨1, one_ne_zero⟩ 1).support.val = 1 := by
  rw [OriginalMovingFactors.singleton_support (unitExterior A) 1 (unitExterior_generates A) 1]
  simp [unitExterior, commonRadical, primeSupport, ← Ideal.one_eq_top]

theorem originalPoolMoving_support {σ : K →+* ℂ}
    {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
    (C : A.GeneralArithmeticContext σ η hS) (q : ExteriorPrime A) (e : AmplifierValuation) :
    (OriginalMovingFactors.singleton (P := P) (R := R)
      ⟨generator C q ^ (2 * e.multiplicity),
        (generator_power_generates C q (2 * e.multiplicity)).1⟩ 1).support.val =
      q.val.asIdeal := by
  rw [OriginalMovingFactors.singleton_support _ _
    (generator_power_generates C q (2 * e.multiplicity)) 1]
  have he : 2 * e.multiplicity ≠ 0 := by cases e <;> decide
  have hs : primeSupport (q.val.asIdeal ^ (2 * e.multiplicity)) = {q.val.asIdeal} := by
    change (normalizedFactors (q.val.asIdeal ^ (2 * e.multiplicity))).toFinset = _
    rw [q.val.irreducible.normalizedFactors_pow, normalize_eq,
      Multiset.toFinset_replicate, if_neg he]
  change commonRadical (q.val.asIdeal ^ (2 * e.multiplicity))
    (q.val.asIdeal ^ (2 * e.multiplicity)) = _
  rw [commonRadical, hs, Finset.inter_self, Finset.prod_singleton]

theorem append_effectiveSupport_norm_le (D E : OriginalMovingFactors A P R)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    A.exteriorNorm ((D.append E).effectiveFullSupport remaining) ≤
      A.exteriorNorm (D.effectiveFullSupport remaining) * A.exteriorNorm E.support :=
  D.append_fullMaskSupport_norm_le E (remainingMaskIdeal A remaining)

theorem deletion_union_singleton_dvd (S : Finset (Ideal (𝓞 K))) (Q : Ideal (𝓞 K)) :
    (∏ I ∈ S ∪ {Q}, I) ∣ (∏ I ∈ S, I) * Q := by
  rw [Finset.union_singleton]
  by_cases hQ : Q ∈ S
  · rw [Finset.insert_eq_of_mem hQ]
    exact dvd_mul_right _ _
  · rw [Finset.prod_insert hQ]
    exact dvd_of_eq (mul_comm _ _)

end T3b

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace T3b

def firstColumnBound (call : Call c) : ℝ := firstColumnAnnulus c call.frame *
  call.base ^ (2 * (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z))

theorem firstColumnBound_nonneg : 0 ≤ firstColumnBound call :=
  mul_nonneg (zero_le_one.trans firstColumnAnnulus_one_le) (Real.rpow_nonneg call.base_pos.le _)

def poolPrimeBound (call : Call c) : ℝ := call.base ^ (recipeInductionSigma c / 3)

theorem poolPrimeBound_one : 1 ≤ poolPrimeBound call :=
  Real.one_le_rpow call.domain.scale.le (div_nonneg (recipeInduction_budget (c := c)).1.le (by norm_num))

end T3b

namespace FirstCauchyKey

theorem t3b_moving_support_dvd_left (key : FirstCauchyKey F) (hF : F.Realizes) :
    (FirstCauchyKey.moving key).support.val ∣ key.1.val.1 := by
  let b := FirstCauchyKey.block key
  let D := firstPhysicalDivisorIdeal (A := Arithmetic.data c) key.2.1.val
  have hD : D.val ∣ (primePowerProduct b.primes b.leftMultiplicity).val := by
    rw [b.common_left]
    exact F.t3b_firstDivisor_dvd_left hF key.1 key.2.1
  let delta := sIntegerMaskGenerator K
    ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))) key.divisor.val
  have hrad : (FirstCauchyKey.moving key).support.val ∣
      (primePowerProduct b.primes b.leftMultiplicity).val :=
    T3b.firstMoving_support_dvd (P := probeData K c) (R := momentRowCharacters K c)
      (Arithmetic.context c) b.primes b.primes_injective b.leftMultiplicity
      b.rightMultiplicity b.left_positive D hD delta.val
      (originalFrequencyIdeal_generates _ delta.property) key.side
  exact hrad.trans (dvd_of_eq b.common_left)

theorem t3b_moving_norm_le (key : FirstCauchyKey F) (hF : F.Realizes)
    (input : ProfileInput call) :
    (Arithmetic.data c).exteriorNorm (FirstCauchyKey.moving key).support ≤
      T3b.firstColumnBound call := by
  have hleft : key.1.val.1 ≠ 0 := by
    rw [← key.block.common_left]
    exact (primePowerProduct _ _).property.1
  exact (norm_le_of_dvd hleft (key.t3b_moving_support_dvd_left hF)).trans
    (F.t3b_common_norm_le hF input key.1).1

end FirstCauchyKey

namespace FirstCauchyFamily

theorem t3b_deletion_norm_le (family : FirstCauchyFamily F) (hF : F.Realizes)
    (hfamily : family.Realizes) (input : ProfileInput call) (i : Fin family.count) :
    (Ideal.absNorm (∏ I ∈ (family.source i).first.fullDeletion, I) : ℝ) ≤
      T3b.firstColumnBound call := by
  rw [hfamily.deletion i]
  have hrad := norm_le_of_dvd (nonZeroDivisors.coe_ne_zero (family.source i).first.selected)
    (support_product_dvd (nonZeroDivisors.coe_ne_zero (family.source i).first.selected)
      (Finset.Subset.refl _))
  apply hrad.trans
  rw [hfamily.selected i]
  split_ifs
  · exact (F.t3b_common_norm_le hF input (family.index i).1).2
  · exact (F.t3b_common_norm_le hF input (family.index i).1).1

end FirstCauchyFamily

namespace PoolExpansion

theorem t3b_poolMoving_norm_le (expansion : PoolExpansion family)
    (i : Fin expansion.count) :
    (Arithmetic.data c).exteriorNorm (expansion.poolMoving i).support ≤
      T3b.poolPrimeBound call := by
  have hunit : (Arithmetic.data c).exteriorNorm
      (OriginalMovingFactors.singleton (P := probeData K c) (R := momentRowCharacters K c)
        ⟨1, one_ne_zero⟩ 1).support = 1 :=
    (congrArg (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ))
      (T3b.singleton_one_support (A := Arithmetic.data c)
        (P := probeData K c) (R := momentRowCharacters K c))).trans
      (by simp only [map_one, Nat.cast_one])
  cases expansion with
  | direct =>
    exact hunit.trans_le T3b.poolPrimeBound_one
  | pooled P count index source =>
    cases htag : (index i).2 with
    | inl u =>
      simp only [poolMoving, htag]
      exact hunit.trans_le T3b.poolPrimeBound_one
    | inr qe =>
      simp only [poolMoving, htag]
      exact (congrArg (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ))
        (T3b.originalPoolMoving_support (P := probeData K c) (R := momentRowCharacters K c)
          (Arithmetic.context c) qe.1.val qe.2)).trans_le
        (P.pool.norm_upper qe.1.val qe.1.property)

theorem t3b_deletion_norm_le (expansion : PoolExpansion family)
    (hF : F.Realizes) (hfamily : family.Realizes) (hexpansion : expansion.Realizes)
    (input : ProfileInput call) (i : Fin expansion.count) :
    (Ideal.absNorm (∏ I ∈ (expansion.source i).first.fullDeletion, I) : ℝ) ≤
      T3b.firstColumnBound call * T3b.poolPrimeBound call := by
  cases expansion with
  | direct =>
    exact (family.t3b_deletion_norm_le hF hfamily input i).trans
      (le_mul_of_one_le_right T3b.firstColumnBound_nonneg T3b.poolPrimeBound_one)
  | pooled P count index source =>
    have hfirst := family.t3b_deletion_norm_le hF hfamily input (index i).1
    cases htag : (index i).2 with
    | inl u =>
      have ho : P.MainOrigin (index i).1 (source i) := by
        simpa only [PoolPresentation.Origin, htag] using hexpansion.2.2 i
      rcases ho with ⟨_, _, _, _, _, _, _, he⟩
      change (Ideal.absNorm (∏ I ∈ (source i).first.fullDeletion, I) : ℝ) ≤ _
      rw [he]
      exact hfirst.trans
        (le_mul_of_one_le_right T3b.firstColumnBound_nonneg T3b.poolPrimeBound_one)
    | inr qe =>
      have ho : P.ErrorOrigin (index i).1 qe.1 qe.2 (source i) := by
        simpa only [PoolPresentation.Origin, htag] using hexpansion.2.2 i
      rcases ho with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd, _⟩
      change (Ideal.absNorm (∏ I ∈ (source i).first.fullDeletion, I) : ℝ) ≤ _
      rw [hd]
      have hzero := (OrdinaryPhaseFacts.first_phase_facts hfamily (index i).1).deletion
      have hb := norm_le_of_dvd (mul_ne_zero hzero qe.1.val.val.ne_bot)
        (T3b.deletion_union_singleton_dvd (family.source (index i).1).first.fullDeletion
          qe.1.val.val.asIdeal)
      rw [map_mul, Nat.cast_mul] at hb
      exact hb.trans (mul_le_mul hfirst (P.pool.norm_upper qe.1.val qe.1.property)
        (Nat.cast_nonneg _) T3b.firstColumnBound_nonneg)

theorem t3b_effectiveMoving_norm_le (expansion : PoolExpansion family)
    (hF : F.Realizes) (input : ProfileInput call) (i : Fin expansion.count) :
    (Arithmetic.data c).exteriorNorm
        ((expansion.moving i).effectiveFullSupport call.localizedSource.source.recipe.remaining) ≤
      (Arithmetic.data c).exteriorNorm call.oldSupport *
        T3b.firstColumnBound call * T3b.poolPrimeBound call := by
  let old := call.localizedSource.source.recipe.moving
  let first := FirstCauchyKey.moving (family.index (expansion.firstIndex i))
  let pool := expansion.poolMoving i
  let empty := CanonicalLiteralFixedPhases.emptyDivisorMoving
    (probeData K c) (momentRowCharacters K c)
  let remaining := call.localizedSource.source.recipe.remaining
  have hempty : (Arithmetic.data c).exteriorNorm empty.support = 1 := by
    exact (congrArg (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ))
      (CanonicalLiteralFixedPhases.emptyDivisorMoving_support (A := Arithmetic.data c)
        (probeData K c) (momentRowCharacters K c))).trans
      (by simp only [map_one, Nat.cast_one])
  have hfirst : (Arithmetic.data c).exteriorNorm first.support ≤ T3b.firstColumnBound call :=
    (family.index (expansion.firstIndex i)).t3b_moving_norm_le hF input
  have hpool : (Arithmetic.data c).exteriorNorm pool.support ≤ T3b.poolPrimeBound call :=
    expansion.t3b_poolMoving_norm_le i
  have hold : 0 ≤ (Arithmetic.data c).exteriorNorm call.oldSupport :=
    ((Arithmetic.data c).exteriorNorm_pos call.oldSupport).le
  calc
    _ ≤ (Arithmetic.data c).exteriorNorm
        (((old.append first).append pool).effectiveFullSupport remaining) *
          (Arithmetic.data c).exteriorNorm empty.support :=
      T3b.append_effectiveSupport_norm_le _ _ remaining
    _ = (Arithmetic.data c).exteriorNorm
        (((old.append first).append pool).effectiveFullSupport remaining) := by rw [hempty, mul_one]
    _ ≤ (Arithmetic.data c).exteriorNorm ((old.append first).effectiveFullSupport remaining) *
        (Arithmetic.data c).exteriorNorm pool.support :=
      T3b.append_effectiveSupport_norm_le _ _ remaining
    _ ≤ ((Arithmetic.data c).exteriorNorm call.oldSupport *
        (Arithmetic.data c).exteriorNorm first.support) *
        (Arithmetic.data c).exteriorNorm pool.support :=
      mul_le_mul_of_nonneg_right (T3b.append_effectiveSupport_norm_le _ _ remaining)
        ((Arithmetic.data c).exteriorNorm_pos pool.support).le
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hfirst hold) hpool
      ((Arithmetic.data c).exteriorNorm_pos pool.support).le
      (mul_nonneg hold T3b.firstColumnBound_nonneg)

end PoolExpansion

namespace T3b

def oldMaskExponentBound (c : TargetContext K) : ℝ :=
  10 + recipeInductionSigma c / 4 + 2 * (recipeInductionSigma c / 3)

theorem oldMaskExponentBound_nonneg : 0 ≤ oldMaskExponentBound c := by
  have hs := (recipeInduction_budget (c := c)).1
  unfold oldMaskExponentBound
  positivity

def completeMaskCoefficient (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  (Ideal.absNorm (Arithmetic.data c).cS : ℝ) * firstColumnAnnulus c frame ^ 2

def completeMaskExponentBound (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  oldMaskExponentBound c + secondOriginalRowExponentBound c p + 1

theorem completeMaskExponentBound_nonneg : 0 ≤ completeMaskExponentBound c p :=
  add_nonneg (add_nonneg oldMaskExponentBound_nonneg secondOriginalRowExponentBound_nonneg)
    zero_le_one

end T3b

namespace RawFamily

theorem t3b_oldMask_norm_le (trace : SourceTrace call p) (htrace : trace.Realizes)
    {geometry : GeometryFamily trace.second} (raw : RawFamily geometry) (j : Fin raw.count)
    (input : ProfileInput call) :
    idealNorm K ((OrdinaryPhaseFacts.ofRaw trace htrace raw j).mask false) ≤
      (Arithmetic.data c).exteriorNorm call.oldSupport *
        T3b.firstColumnBound call ^ 2 * T3b.poolPrimeBound call ^ 2 := by
  let phases := OrdinaryPhaseFacts.ofRaw trace htrace raw j
  let i := (raw.index j).val.1.1
  have hm := trace.expansion.t3b_effectiveMoving_norm_le htrace.first input i
  have hd := trace.expansion.t3b_deletion_norm_le htrace.first htrace.cauchy
    htrace.expansion input i
  change (Ideal.absNorm
    (((phases.moving false).effectiveFullSupport call.localizedSource.source.recipe.remaining).val *
      (∏ I ∈ (raw.packet j).second.physical.first.fullDeletion, I)) : ℝ) ≤ _
  rw [map_mul, Nat.cast_mul, OrdinaryPhaseFacts.ofRaw_moving_false]
  change (Arithmetic.data c).exteriorNorm
      ((trace.expansion.moving i).effectiveFullSupport call.localizedSource.source.recipe.remaining) *
      (Ideal.absNorm (∏ I ∈ (trace.second.source i).physical.first.fullDeletion, I) : ℝ) ≤ _
  rw [htrace.second.physical i]
  have hb := mul_le_mul hm hd (Nat.cast_nonneg _)
    (mul_nonneg
      (mul_nonneg ((Arithmetic.data c).exteriorNorm_pos call.oldSupport).le
        T3b.firstColumnBound_nonneg) (zero_le_one.trans T3b.poolPrimeBound_one))
  convert hb using 1 <;> ring

theorem t3b_oldMask_norm_uniform (trace : SourceTrace call p) (htrace : trace.Realizes)
    {geometry : GeometryFamily trace.second} (raw : RawFamily geometry) (j : Fin raw.count)
    (input : ProfileInput call) :
    idealNorm K ((OrdinaryPhaseFacts.ofRaw trace htrace raw j).mask false) ≤
      T3b.firstColumnAnnulus c call.frame ^ 2 * call.base ^ T3b.oldMaskExponentBound c := by
  have hold : (Arithmetic.data c).exteriorNorm call.oldSupport ≤ call.base ^ (2 : ℝ) :=
    (call.t3b_oldSupport_norm_le htrace.first.active).trans
      (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le call.width_le)
  have hA := call.t3b_totalLength_le
  have hsquare (e : ℝ) : (call.base ^ e) ^ 2 = call.base ^ (2 * e) := by
    rw [pow_two, ← Real.rpow_add call.base_pos]
    congr 1
    ring
  calc
    _ ≤ (Arithmetic.data c).exteriorNorm call.oldSupport *
        T3b.firstColumnBound call ^ 2 * T3b.poolPrimeBound call ^ 2 :=
      raw.t3b_oldMask_norm_le trace htrace j input
    _ ≤ call.base ^ (2 : ℝ) * T3b.firstColumnBound call ^ 2 * T3b.poolPrimeBound call ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hold (sq_nonneg _)) (sq_nonneg _)
    _ = T3b.firstColumnAnnulus c call.frame ^ 2 *
        call.base ^ (2 + 4 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
          call.node.parameters.z) + 2 * (recipeInductionSigma c / 3)) := by
      rw [T3b.firstColumnBound, T3b.poolPrimeBound, mul_pow, hsquare, hsquare]
      have he : 2 + 4 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
          call.node.parameters.z) + 2 * (recipeInductionSigma c / 3) =
          2 + 2 * (2 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
            call.node.parameters.z)) + 2 * (recipeInductionSigma c / 3) := by ring
      rw [he, Real.rpow_add call.base_pos
        (2 + 2 * (2 * (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z)))
        (2 * (recipeInductionSigma c / 3)),
        Real.rpow_add call.base_pos 2
          (2 * (2 * (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z)))]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (by
        unfold T3b.oldMaskExponentBound
        change call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z ≤
          2 + recipeInductionSigma c / 16 at hA
        linarith)) (sq_nonneg _)

theorem t3bCompleteMask_norm_uniform (trace : SourceTrace call p) (htrace : trace.Realizes)
    {geometry : GeometryFamily trace.second} (hgeometry : geometry.Realizes)
    (raw : RawFamily geometry) (hraw : raw.Realizes) (j : Fin raw.count)
    (input : ProfileInput call) (h : (raw.packet j).R.live)
    (hthreshold : T3b.completeMaskCoefficient c call.frame ≤ call.base) :
    (Ideal.absNorm ((raw.packet j).t3bCompleteMask
      (OrdinaryPhaseFacts.ofRaw trace htrace raw j) h) : ℝ) ≤
        call.base ^ T3b.completeMaskExponentBound c p := by
  let packet := raw.packet j
  let phases := OrdinaryPhaseFacts.ofRaw trace htrace raw j
  have hpacket : packet.Realizes := raw.packet_realizes trace htrace hgeometry hraw j
  have hm := raw.t3b_oldMask_norm_uniform trace htrace j input
  have hr := packet.t3b_originalRow_norm_uniform hpacket h
  have hb := packet.t3bCompleteMask_norm_le phases h
  calc
    _ ≤ (Ideal.absNorm (Arithmetic.data c).cS : ℝ) *
        idealNorm K (phases.mask false) *
        (Ideal.absNorm (packet.R.originalIdeal h.val).val : ℝ) := hb
    _ ≤ (Ideal.absNorm (Arithmetic.data c).cS : ℝ) *
        (T3b.firstColumnAnnulus c call.frame ^ 2 * call.base ^ T3b.oldMaskExponentBound c) *
        call.base ^ T3b.secondOriginalRowExponentBound c p :=
      mul_le_mul (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)) hr
        (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg call.base_pos.le _)))
    _ = T3b.completeMaskCoefficient c call.frame *
        call.base ^ (T3b.oldMaskExponentBound c + T3b.secondOriginalRowExponentBound c p) := by
      rw [Real.rpow_add call.base_pos]
      unfold T3b.completeMaskCoefficient
      ring
    _ ≤ call.base *
        call.base ^ (T3b.oldMaskExponentBound c + T3b.secondOriginalRowExponentBound c p) :=
      mul_le_mul_of_nonneg_right hthreshold (Real.rpow_nonneg call.base_pos.le _)
    _ = _ := by
      rw [T3b.completeMaskExponentBound,
        Real.rpow_add call.base_pos
          (T3b.oldMaskExponentBound c + T3b.secondOriginalRowExponentBound c p) 1,
        Real.rpow_one]
      ring

end RawFamily

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.t3b_oldMask_norm_uniform
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.t3bCompleteMask_norm_uniform
