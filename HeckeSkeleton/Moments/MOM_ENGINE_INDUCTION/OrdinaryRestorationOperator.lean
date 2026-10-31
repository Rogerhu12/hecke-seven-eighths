import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionOperator
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionWeights
import HeckeGeneral.Analysis.IdealDerivativeMellinSmoothing

/-!
# Restoration and the original common frequency integral

The actual finite Euler-deletion index and the infinite smooth-ideal
restoration index are absorbed into a scalar function of the same real
frequency.  Their exact mixed ideal-norm weights prove absolute Fubini.
The common child column consequently has no D/H-dependent profile: it is
the genuine power window at the original common dyadic scale.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckePort.Moments HeckePort.Moments.ReflectionMass
open scoped Classical BigOperators Topology

variable {K : Type} [Field K] [NumberField K]

/-- The exact original reflection coefficient with its common-scale
Mellin phase; its scale is Q N(D)/(X N(H)). -/
def ordinaryRestorationTerm (a ai : Ideal (𝓞 K) → ℂ)
    (S : Finset (Ideal (𝓞 K))) (Q X N σ : ℝ)
    (D : Finset (Ideal (𝓞 K))) (H : SmoothIdeal S) (t : ℝ) : ℂ :=
  coefficient a ai S D H *
    ((N / (Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)) : ℝ) : ℂ) ^
      (idealVerticalPoint σ t - ((1 / 2 : ℝ) : ℂ))

/-- No union of different rows' deleted prime sets is taken. -/
def ordinaryRestorationPhase (a ai : Ideal (𝓞 K) → ℂ)
    (S : Finset (Ideal (𝓞 K))) (Q X N σ t : ℝ) : ℂ :=
  ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
    ordinaryRestorationTerm a ai S Q X N σ D H t

private theorem restorationTerm_continuous
    (a ai : Ideal (𝓞 K) → ℂ) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, Prime P) (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset)
    (H : SmoothIdeal S) {Q X N : ℝ} (hQ : 0 < Q) (hX : 0 < X) (hN : 0 < N) (σ : ℝ) :
    Continuous (ordinaryRestorationTerm a ai S Q X N σ D H) := by
  have hd := subset_product_norm_pos D
    (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))
  have hr := div_pos hN (div_pos (mul_pos hQ hd) (mul_pos hX (inorm_pos H.val)))
  exact continuous_const.mul
    (((differentiable_id.sub_const ((1 / 2 : ℝ) : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))).continuous.comp
        (continuous_idealVerticalPoint σ))

private theorem restorationTerm_majorant
    {a ai : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a) (hai : IdealCoeff ai)
    (β : ℝ) (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) (H : SmoothIdeal S)
    {Q X N σ : ℝ} (hQ : 0 < Q) (hX : 0 < X) (hN : 0 < N)
    (hlo : β ≤ σ) (hhi : σ ≤ 1 - β) (t : ℝ) :
    ‖ordinaryRestorationTerm a ai S Q X N σ D H t‖ ≤
      ((N * X / Q) ^ (σ - 1 / 2) * reflectionPowerWeight β (∏ P ∈ D, P)) *
        reflectionPowerWeight β H.val.val := by
  have h := reflection_coefficient_phase_norm_le ha hai S hS D hD H
    Q X N hQ hX hN (idealVerticalPoint σ t)
  simp only [idealVerticalPoint_re] at h
  apply h.trans
  have hm := mixedReflectionWeight_le β σ hlo hhi
    ⟨∏ P ∈ D, P, subset_product_nonzero D
      (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))⟩ H.val
  simpa only [inorm, mul_assoc] using mul_le_mul_of_nonneg_left hm
    (Real.rpow_nonneg (div_pos (mul_pos hN hX) hQ).le (σ - 1 / 2))

/-- Absolute phase summability at every actual real frequency. -/
theorem summable_ordinaryRestorationTerm
    {a ai : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a) (hai : IdealCoeff ai)
    {β : ℝ} (hβ : 0 < β) (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset)
    {Q X N σ : ℝ} (hQ : 0 < Q) (hX : 0 < X) (hN : 0 < N)
    (hlo : β ≤ σ) (hhi : σ ≤ 1 - β) (t : ℝ) :
    Summable (fun H : SmoothIdeal S =>
      ‖ordinaryRestorationTerm a ai S Q X N σ D H t‖) := by
  simpa only [ordinaryRestorationTerm, idealVerticalPoint_re] using
    reflection_coefficient_phase_summable ha hai β hβ S hS D hD Q X N hQ hX hN
      (idealVerticalPoint σ t) (by simpa only [idealVerticalPoint_re] using hlo)
        (by simpa only [idealVerticalPoint_re] using hhi)

private theorem restorationTerm_kernel_integrable
    {a ai : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a) (hai : IdealCoeff ai)
    (β : ℝ) (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) (H : SmoothIdeal S)
    {Q X N σ : ℝ} (hQ : 0 < Q) (hX : 0 < X) (hN : 0 < N)
    (hlo : β ≤ σ) (hhi : σ ≤ 1 - β) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun t : ℝ => f t * ordinaryRestorationTerm a ai S Q X N σ D H t) :=
  hf.mul_bdd (restorationTerm_continuous a ai S hS D hD H hQ hX hN σ).aestronglyMeasurable
    (Eventually.of_forall (restorationTerm_majorant ha hai β S hS D hD H hQ hX hN hlo hhi))

private theorem restorationTerm_kernel_norm_summable
    {a ai : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a) (hai : IdealCoeff ai)
    {β : ℝ} (hβ : 0 < β) (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset)
    {Q X N σ : ℝ} (hQ : 0 < Q) (hX : 0 < X) (hN : 0 < N)
    (hlo : β ≤ σ) (hhi : σ ≤ 1 - β) {f : ℝ → ℂ} (hf : Integrable f) :
    Summable (fun H : SmoothIdeal S =>
      ∫ t : ℝ, ‖f t * ordinaryRestorationTerm a ai S Q X N σ D H t‖) := by
  let W : ℝ := (N * X / Q) ^ (σ - 1 / 2) * reflectionPowerWeight β (∏ P ∈ D, P)
  apply ((weightedSmoothSummable β hβ S hS).mul_left ((∫ t : ℝ, ‖f t‖) * W)).of_nonneg_of_le
  · exact fun _ => integral_nonneg (fun _ => norm_nonneg _)
  · intro H
    have hpoint (t : ℝ) :
        ‖f t * ordinaryRestorationTerm a ai S Q X N σ D H t‖ ≤
          ‖f t‖ * (W * reflectionPowerWeight β H.val.val) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (restorationTerm_majorant ha hai β S hS D hD H hQ hX hN hlo hhi t)
        (norm_nonneg _)
    calc
      _ ≤ ∫ t : ℝ, ‖f t‖ * (W * reflectionPowerWeight β H.val.val) :=
        integral_mono
          (restorationTerm_kernel_integrable ha hai β S hS D hD H hQ hX hN hlo hhi hf).norm
          (hf.norm.mul_const _) hpoint
      _ = _ := by rw [integral_mul_const]; ring

/-- Genuine absolute Fubini for the complete original restoration sum.
The input is any L1 frequency function, not a child-moment estimate. -/
theorem ordinaryRestorationPhase_fubini
    {a ai : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a) (hai : IdealCoeff ai)
    {β : ℝ} (hβ : 0 < β) (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    {Q X N σ : ℝ} (hQ : 0 < Q) (hX : 0 < X) (hN : 0 < N)
    (hlo : β ≤ σ) (hhi : σ ≤ 1 - β) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun t : ℝ => f t * ordinaryRestorationPhase a ai S Q X N σ t) ∧
      (∫ t : ℝ, f t * ordinaryRestorationPhase a ai S Q X N σ t) =
        ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
          ∫ t : ℝ, f t * ordinaryRestorationTerm a ai S Q X N σ D H t := by
  letI : Countable (SmoothIdeal S) := Countable.of_injective (exponents S) (exponents_injective S)
  have hD (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) :
      Integrable (fun t : ℝ => ∑' H : SmoothIdeal S,
        f t * ordinaryRestorationTerm a ai S Q X N σ D H t) :=
    integrable_complex_tsum_of_summable_integral_norm
      (fun H => restorationTerm_kernel_integrable ha hai β S hS D hD H hQ hX hN hlo hhi hf)
      (restorationTerm_kernel_norm_summable ha hai hβ S hS D hD hQ hX hN hlo hhi hf)
  have he (t : ℝ) : f t * ordinaryRestorationPhase a ai S Q X N σ t =
      ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
        f t * ordinaryRestorationTerm a ai S Q X N σ D H t := by
    simp only [ordinaryRestorationPhase, Finset.mul_sum, tsum_mul_left]
  constructor
  · exact (integrable_finsetSum _ hD).congr (Eventually.of_forall (fun t => (he t).symm))
  · simp_rw [he]
    rw [integral_finsetSum _ hD]
    apply Finset.sum_congr rfl
    intro D hDS
    exact (integral_tsum_of_summable_integral_norm
      (fun H => restorationTerm_kernel_integrable ha hai β S hS D hDS H hQ hX hN hlo hhi hf)
      (restorationTerm_kernel_norm_summable ha hai hβ S hS D hDS hQ hX hN hlo hhi hf)).symm

/-- A common subpower bound for the actual complex restoration phase.
Its constant precedes every prime set, conductor, scale and frequency. -/
theorem ordinaryRestorationPhase_norm_subpower (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a ai : Ideal (𝓞 K) → ℂ), IdealCoeff a → IdealCoeff ai →
      ∀ (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
      (Q X N σ : ℝ), 0 < Q → 0 < X → 0 < N → β ≤ σ → σ ≤ 1 - β →
      ∀ t : ℝ, ‖ordinaryRestorationPhase a ai S Q X N σ t‖ ≤
        C * (N * X / Q) ^ (σ - 1 / 2) *
          (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := reflection_coefficient_phase_mass_subpower (K := K) β ε hβ hε
  refine ⟨C, hC, ?_⟩
  intro a ai ha hai S hS Q X N σ hQ hX hN hlo hhi t
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun D hD => norm_tsum_le_tsum_norm
    (summable_ordinaryRestorationTerm ha hai hβ S hS D hD hQ hX hN hlo hhi t))).trans
  simpa only [ordinaryRestorationTerm, idealVerticalPoint_re] using
    (hbound S hS a ai ha hai Q X N hQ hX hN (idealVerticalPoint σ t)
      (by simpa only [idealVerticalPoint_re] using hlo)
      (by simpa only [idealVerticalPoint_re] using hhi)).2

/-- The actual retained dyadic piece after all finite deletions and
infinite restorations is a single common-frequency column integral.
The complete original deleted mask may be included in the explicit ideal
coefficient `b`; neither its row nor its support is changed here. -/
theorem ordinaryRestoredWindow_operator
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    {a ai : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a) (hai : IdealCoeff ai)
    (b : NonzeroIdeal K → ℂ)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    {δ Q X N σ : ℝ} (hδ : 0 < δ) (hQ : 0 < Q) (hX : 0 < X) (hN : 0 < N)
    (hlo : 1 / 4 ≤ σ) (hhi : σ ≤ 3 / 4) :
    (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
      let Y := Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)
      coefficient a ai S D H * ((Real.sqrt Y : ℂ)⁻¹ *
        ∑ I ∈ ordinaryPowerWindowSupport K N,
          b I * ordinaryReflectedProfile K χ V δ (idealNorm K I / Y) *
            (fixedDyadicWeight (idealNorm K I / N) : ℂ))) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
        ordinaryMellinGamma K χ V σ t * ordinaryRestorationPhase a ai S Q X N σ t *
          ordinaryPowerColumn K b σ N t := by
  have hline : σ ∈ Icc (-δ) (3 / 4) := ⟨by linarith, hhi⟩
  let f : ℝ → ℂ := fun t => ordinaryMellinGamma K χ V σ t * ordinaryPowerColumn K b σ N t
  have hf : Integrable f :=
    (integrable_ordinaryMellinGamma K hcomplex χ V hδ hline).mul_bdd
      (continuous_ordinaryPowerColumn K b σ N).aestronglyMeasurable
      (Eventually.of_forall (fun t => ordinaryPowerColumn_norm_le K b σ t hN))
  have hF := ordinaryRestorationPhase_fubini ha hai (β := 1 / 4) (by norm_num)
    S hS hQ hX hN hlo (by linarith) hf
  have hterm (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) (H : SmoothIdeal S) :
      (let Y := Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)
       coefficient a ai S D H * ((Real.sqrt Y : ℂ)⁻¹ *
        ∑ I ∈ ordinaryPowerWindowSupport K N,
          b I * ordinaryReflectedProfile K χ V δ (idealNorm K I / Y) *
            (fixedDyadicWeight (idealNorm K I / N) : ℂ))) =
        (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
          f t * ordinaryRestorationTerm a ai S Q X N σ D H t := by
    have hd := subset_product_norm_pos D
      (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))
    have hY := div_pos (mul_pos hQ hd) (mul_pos hX (inorm_pos H.val))
    dsimp only
    rw [ordinaryReflectedWindow_operator K hcomplex χ V b hδ hline hN hY]
    rw [mul_left_comm, ← integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [f, ordinaryRestorationTerm]
    push_cast
    ring
  calc
    _ = (2 * (Real.pi : ℂ))⁻¹ * ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
        ∫ t : ℝ, f t * ordinaryRestorationTerm a ai S Q X N σ D H t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      rw [← tsum_mul_left]
      exact tsum_congr (hterm D hD)
    _ = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ, f t * ordinaryRestorationPhase a ai S Q X N σ t := by rw [hF.2]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp [f]
      ring

end HeckeSkeleton.Moments.EngineInduction
