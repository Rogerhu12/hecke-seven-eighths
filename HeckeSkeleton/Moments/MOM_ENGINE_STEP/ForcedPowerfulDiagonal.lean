import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PowerfulDiagonal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Pool
import HeckePort.Moments.Descent.Quotients

/-!
# A prescribed divisor on the actual square diagonal

The second dual zero is supported on equality of its two complete
column ideals. Their product is therefore an actual square. Counting
the common ideal after division by a prescribed divisor gives its full
norm saving. Tuple multiplicities still come from the original complete
product and its divisor bound.

This argument uses equality of the two ideals. It makes no assertion
that dividing an arbitrary powerful ideal by a square preserves the
powerful condition. The counting constants precede the divisor, cutoff,
finite carrier and all coefficients.
-/

noncomputable section
open scoped Classical NumberField BigOperators

namespace HeckeSkeleton.Moments.EngineStep.ForcedPowerfulDiagonal

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.LargeSieve
open HeckePort.Moments HeckePort.CenteredMomentCounting
open PowerfulDiagonal

variable {K : Type} [Field K] [NumberField K]

/-- A closed finite ideal count, including cutoffs below one. -/
theorem finite_ideal_count (K : Type) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal (𝓞 K))) (Y : ℝ), 0 ≤ Y →
      (∀ I ∈ S, I ≠ 0) → (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) →
      (S.card : ℝ) ≤ C * Y := by
  obtain ⟨C, C', hC, hC', hcounts⟩ := ideal_counting_harmonic_bounds K
  refine ⟨C, hC, ?_⟩
  intro S Y hY hzero hnorm
  have hcount : ((normBoundedIdeals K Y).ncard : ℝ) ≤ C * Y := by
    by_cases hYone : 1 ≤ Y
    · simpa only [Set.univ_inter] using (hcounts Set.univ).1 Y hYone
    · have he : normBoundedIdeals K Y = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro I hI
        exact hYone ((idealNorm_ge_one I.val I.property).trans hI)
      rw [he, Set.ncard_empty, Nat.cast_zero]
      exact mul_nonneg hC.le hY
  let lift : S → DedekindZetaZeroFree.NonzeroIdeal K :=
    fun I => ⟨I.val, hzero I.val I.property⟩
  have hinj : Function.Injective lift := by
    intro I J he
    apply Subtype.ext
    exact congrArg (fun Q : DedekindZetaZeroFree.NonzeroIdeal K => Q.val) he
  let T := S.attach.image lift
  have hcard : T.card = S.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  have hsub : (T : Set (DedekindZetaZeroFree.NonzeroIdeal K)) ⊆
      normBoundedIdeals K Y := by
    intro I hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    change (Ideal.absNorm J.val : ℝ) ≤ Y
    exact hnorm J.val J.property
  have hc : T.card ≤ (normBoundedIdeals K Y).ncard := by
    simpa only [Set.ncard_coe_finset] using
      Set.ncard_le_ncard hsub (normBoundedIdeals_finite K Y)
  rw [← hcard]
  exact (Nat.cast_le.mpr hc).trans hcount

/-- Dividing the actual ideals, rather than a powerful predicate,
retains the entire prescribed divisor saving. -/
theorem finite_divisible_ideal_count (K : Type) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
      (Y : ℝ), D ≠ 0 → 0 ≤ Y →
      (∀ I ∈ S, I ≠ 0) → (∀ I ∈ S, D ∣ I) →
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) →
      (S.card : ℝ) ≤ C * (Y / (Ideal.absNorm D : ℝ)) := by
  obtain ⟨C, hC, hcount⟩ := finite_ideal_count K
  refine ⟨C, hC, ?_⟩
  intro S D Y hD hY hzero hdiv hnorm
  have hND : 0 < (Ideal.absNorm D : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD))
  let T := quotientSupport D S
  have hTzero : ∀ I ∈ T, I ≠ 0 := quotientSupport_nonzero D hD S hzero
  have hTnorm : ∀ I ∈ T, (Ideal.absNorm I : ℝ) ≤ Y / (Ideal.absNorm D : ℝ) := by
    intro I hI
    apply (le_div_iff₀ hND).mpr
    have h := hnorm (D * I) ((mem_quotientSupport D I hD S).mp hI)
    simpa only [map_mul, Nat.cast_mul, mul_comm] using h
  have hfilter : S.filter (fun I => D ∣ I) = S := Finset.filter_eq_self.mpr hdiv
  have hinj : Set.InjOn (idealQuotient D) (S : Set (Ideal (𝓞 K))) := by
    intro I hI J hJ he
    exact idealQuotient_injective_on D (hdiv I hI) (hdiv J hJ) he
  have hcard : T.card = S.card := by
    dsimp only [T, quotientSupport]
    rw [hfilter, Finset.card_image_of_injOn hinj]
  rw [← hcard]
  exact hcount T _ (div_nonneg hY hND.le) hTzero hTnorm

/-- The complete tuple fibres are paid before summing over their
actual square root ideals. No tuple is reselected or divided here. -/
theorem square_tuple_card_of_fibers (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : Type*} (S : Finset α)
      (factors : α → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ),
      (∀ v, (S.filter (fun x => factors x = v)).card ≤ multiplicity) →
      ∀ (I : α → Ideal (𝓞 K)) (D : Ideal (𝓞 K)) (X : ℝ), D ≠ 0 → 1 ≤ X →
      (∀ v ∈ S, I v ≠ 0) →
      (∀ v ∈ S, tupleIdeal (factors v) = I v ^ 2) →
      (∀ v ∈ S, D ∣ I v) →
      (∀ v ∈ S, (Ideal.absNorm (tupleIdeal (factors v)) : ℝ) ≤ X) →
      (S.card : ℝ) ≤ C * multiplicity * Real.sqrt X * X ^ ε /
        (Ideal.absNorm D : ℝ) := by
  let δ : ℝ := ε / ((k : ℝ) + 1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hbudget : δ * (k : ℝ) ≤ ε := by
    have he : δ * ((k : ℝ) + 1) = ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  obtain ⟨Cdiv, hCdiv, hdivisor⟩ := ideal_divisor_count_le_rpow K δ hδ
  obtain ⟨Ccount, hCcount, hcount⟩ := finite_divisible_ideal_count K
  have hCdivpos : 0 < Cdiv := zero_lt_one.trans_le hCdiv
  refine ⟨Ccount * Cdiv ^ k, mul_pos hCcount (pow_pos hCdivpos k), ?_⟩
  intro α S factors multiplicity hfiber I D X hD hX hzero hfactor hdiv hnorm
  let roots := S.image I
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hrootzero (J : Ideal (𝓞 K)) (hJ : J ∈ roots) : J ≠ 0 := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hJ
    exact hzero v hv
  have hrootdiv (J : Ideal (𝓞 K)) (hJ : J ∈ roots) : D ∣ J := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hJ
    exact hdiv v hv
  have hsquareNorm (J : Ideal (𝓞 K)) (hJ : J ∈ roots) :
      (Ideal.absNorm (J ^ 2) : ℝ) ≤ X := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hJ
    simpa only [hfactor v hv] using hnorm v hv
  have hrootnorm (J : Ideal (𝓞 K)) (hJ : J ∈ roots) :
      (Ideal.absNorm J : ℝ) ≤ Real.sqrt X := by
    apply (Real.le_sqrt (Nat.cast_nonneg _) hX0).mpr
    simpa only [map_pow, Nat.cast_pow] using hsquareNorm J hJ
  have hroots := hcount roots D (Real.sqrt X) hD (Real.sqrt_nonneg X)
    hrootzero hrootdiv hrootnorm
  have hrootfiber (J : Ideal (𝓞 K)) (hJ : J ∈ roots) :
      ((S.filter (fun v => I v = J)).card : ℝ) ≤
        (multiplicity : ℝ) * (Cdiv ^ k * X ^ ε) := by
    let T := S.filter (fun v => I v = J)
    have hTfactor (v : Fin k → Ideal (𝓞 K)) (hv : v ∈ T.image factors) :
        tupleIdeal v = J ^ 2 := by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      rw [hfactor x (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2]
    have hfilter : (T.image factors).filter (fun v => tupleIdeal v = J ^ 2) =
        T.image factors := Finset.filter_eq_self.mpr hTfactor
    have htuple := tuple_product_fiber_card (T.image factors) (J ^ 2)
      (pow_ne_zero 2 (hrootzero J hJ))
    rw [hfilter] at htuple
    have hactual (v : Fin k → Ideal (𝓞 K)) :
        ((T.filter (fun x => factors x = v)).card : ℝ) ≤ multiplicity := by
      have hsub : T.filter (fun x => factors x = v) ⊆
          S.filter (fun x => factors x = v) := by
        intro x hx
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1,
            (Finset.mem_filter.mp hx).2⟩
      exact_mod_cast (Finset.card_le_card hsub).trans (hfiber v)
    have hTc : (T.card : ℝ) ≤ (multiplicity : ℝ) * (T.image factors).card := by
      simpa using positive_pushforward_bound T factors (fun _ => (1 : ℝ))
        (multiplicity : ℝ) (fun _ _ => zero_le_one) (fun v _ => hactual v)
    have htupleReal : ((T.image factors).card : ℝ) ≤ (idealDivisorCount (J ^ 2) : ℝ) ^ k := by
      exact_mod_cast htuple
    have htuples : ((T.image factors).card : ℝ) ≤ Cdiv ^ k * X ^ ε := by
      calc
        _ ≤ (idealDivisorCount (J ^ 2) : ℝ) ^ k := htupleReal
        _ ≤ (Cdiv * (Ideal.absNorm (J ^ 2) : ℝ) ^ δ) ^ k :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (hdivisor (J ^ 2)) k
        _ = Cdiv ^ k * (Ideal.absNorm (J ^ 2) : ℝ) ^ (δ * (k : ℝ)) := by
          rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
        _ ≤ Cdiv ^ k * X ^ ε := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hCdivpos.le k)
          exact (Real.rpow_le_rpow (Nat.cast_nonneg _) (hsquareNorm J hJ)
            (mul_nonneg hδ.le (Nat.cast_nonneg k))).trans
            (Real.rpow_le_rpow_of_exponent_le hX hbudget)
    exact hTc.trans (mul_le_mul_of_nonneg_left htuples (Nat.cast_nonneg _))
  have he := Finset.card_eq_sum_card_fiberwise
    (fun v (hv : v ∈ S) => Finset.mem_image_of_mem I hv)
  calc
    (S.card : ℝ) = ∑ J ∈ roots, ((S.filter (fun v => I v = J)).card : ℝ) := by
      exact_mod_cast he
    _ ≤ ∑ _J ∈ roots, (multiplicity : ℝ) * (Cdiv ^ k * X ^ ε) :=
      Finset.sum_le_sum hrootfiber
    _ = (roots.card : ℝ) * ((multiplicity : ℝ) * (Cdiv ^ k * X ^ ε)) := by simp
    _ ≤ (Ccount * (Real.sqrt X / (Ideal.absNorm D : ℝ))) *
        ((multiplicity : ℝ) * (Cdiv ^ k * X ^ ε)) :=
      mul_le_mul_of_nonneg_right hroots (by positivity)
    _ = _ := by ring

/-- This is the shape supplied by the actual equal-ideal second dual
zero. The original factor tuple and its finite fibres are retained. -/
theorem equal_ideal_tuple_count_of_fibers (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : Type*} (S : Finset α)
      (factors : α → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ),
      (∀ v, (S.filter (fun x => factors x = v)).card ≤ multiplicity) →
      ∀ (I J : α → Ideal (𝓞 K)) (D : Ideal (𝓞 K)) (X : ℝ), D ≠ 0 → 1 ≤ X →
      (∀ v ∈ S, I v ≠ 0) →
      (∀ v ∈ S, tupleIdeal (factors v) = I v * J v) →
      (∀ v ∈ S, I v = J v) →
      (∀ v ∈ S, D ∣ I v) →
      (∀ v ∈ S, (Ideal.absNorm (I v * J v) : ℝ) ≤ X) →
      (S.card : ℝ) / Real.sqrt X ≤
        C * multiplicity * X ^ ε / (Ideal.absNorm D : ℝ) := by
  obtain ⟨C, hC, hcount⟩ := square_tuple_card_of_fibers (K := K) k ε hε
  refine ⟨C, hC, ?_⟩
  intro α S factors multiplicity hfiber I J D X hD hX hzero hfactor hequal hdiv hnorm
  have hcard := hcount S factors multiplicity hfiber I D X hD hX hzero
    (by intro v hv; rw [hfactor v hv, ← hequal v hv, pow_two]) hdiv
    (by intro v hv; simpa only [hfactor v hv] using hnorm v hv)
  have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.mpr (zero_lt_one.trans_le hX)
  have hND : 0 < (Ideal.absNorm D : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD))
  apply (div_le_div_of_nonneg_right hcard hsqrt.le).trans_eq
  field_simp [hsqrt.ne', hND.ne'] <;> ring

end HeckeSkeleton.Moments.EngineStep.ForcedPowerfulDiagonal

#print axioms HeckeSkeleton.Moments.EngineStep.ForcedPowerfulDiagonal.finite_ideal_count
#print axioms HeckeSkeleton.Moments.EngineStep.ForcedPowerfulDiagonal.finite_divisible_ideal_count
#print axioms HeckeSkeleton.Moments.EngineStep.ForcedPowerfulDiagonal.square_tuple_card_of_fibers
#print axioms HeckeSkeleton.Moments.EngineStep.ForcedPowerfulDiagonal.equal_ideal_tuple_count_of_fibers
