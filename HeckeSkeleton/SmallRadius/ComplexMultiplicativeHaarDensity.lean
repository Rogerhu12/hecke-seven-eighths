import HeckeSkeleton.SmallRadius.SLocalProductHaarMellin
import FLTReuse.M00c7be4ee0b6591d
import FLTReuse.M972ec44a948d2b38
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Ported from the old repository cache candidate of 2026-10-12; compiled in this project.
Actual complex units Haar versus punctured Lebesgue density |z|^(-2).
Support proofs are a literal-type adaptation of FLTReuse.M00c7be4ee0b6591d,
SHA 3c365b0daeedbc49d011db1b63ff35063ba253736accc8a1601768dfc66ecb38,
lines 2320-2585: replace an infinite completion by C and omit the place
parameter and obsolete section-instance omissions. Their mathematical
proofs and the source's dimension parameter are retained. All comparisons
and weighted-integral corollaries after namespace Support are new.

The actual dimension-two modulus is proved by the existing exported FLT
complex theorem. No Haar comparison, Fourier functional equation or
nonzero Fourier moment is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.Analysis.SLocalRadialHaarDraft.ComplexHaarDensityDraft

open MeasureTheory MeasureTheory.Measure LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Classical

namespace Support

theorem modulus_completion_eq (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (ℂ)ˣ, distribHaarChar ℂ t = ‖(t : ℂ)‖₊ ^ d)
    (a : ℂ) : modulus a = ‖a‖₊ ^ d := by
  by_cases h : a = 0
  · subst h
    rw [modulus_zero, nnnorm_zero, zero_pow hd]
  · rw [modulus_of_ne_zero h, hΔ (Units.mk0 a h)]
    rfl

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] [μ.Regular]

theorem mulMeasure_completion_eq (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (ℂ)ˣ, distribHaarChar ℂ t = ‖(t : ℂ)‖₊ ^ d) :
    mulMeasure μ = (μ.restrict {0}ᶜ).withDensity fun x => ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ := by
  rw [mulMeasure]
  congr 1
  funext x
  rw [modulus_completion_eq d hd hΔ]
  norm_cast

theorem measurable_nnnorm_pow_inv (d : ℕ) :
    Measurable fun x : ℂ => ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ :=
  ((measurable_nnnorm.coe_nnreal_ennreal).pow_const d).inv

theorem units_smul_set_eq (t : (ℂ)ˣ) (E : Set ℂ) :
    (t • E : Set ℂ) = (t : ℂ) • E := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem measure_units_smul (d : ℕ)
    (hΔ : ∀ t : (ℂ)ˣ, distribHaarChar ℂ t = ‖(t : ℂ)‖₊ ^ d)
    (t : (ℂ)ˣ) (E : Set ℂ) :
    μ ((t : ℂ) • E) = (‖(t : ℂ)‖₊ ^ d : ℝ≥0∞) * μ E := by
  rw [← units_smul_set_eq, ← distribHaarChar_mul (μ := μ) t E, hΔ t]
  norm_cast

theorem map_units_smul (d : ℕ) (_hd : d ≠ 0)
    (hΔ : ∀ t : (ℂ)ˣ, distribHaarChar ℂ t = ‖(t : ℂ)‖₊ ^ d)
    (t : (ℂ)ˣ) :
    Measure.map ((t : ℂ) • ·) μ = ((‖(t : ℂ)‖₊ ^ d : ℝ≥0∞))⁻¹ • μ := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_const_smul _) hA, Measure.smul_apply, smul_eq_mul]
  have hpre : ((t : ℂ) • ·) ⁻¹' A = ((t⁻¹ : (ℂ)ˣ) : ℂ) • A := by
    ext x
    constructor
    · intro hx
      refine ⟨(t : ℂ) • x, hx, ?_⟩
      show ((t⁻¹ : (ℂ)ˣ) : ℂ) • (t : ℂ) • x = x
      rw [smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero t), one_smul]
    · rintro ⟨y, hy, rfl⟩
      show (t : ℂ) • ((t⁻¹ : (ℂ)ˣ) : ℂ) • y ∈ A
      rw [smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero t), one_smul]
      exact hy
  rw [hpre, measure_units_smul d hΔ t⁻¹ A]
  congr 1
  rw [Units.val_inv_eq_inv_val, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr (Units.ne_zero t)),
    ← ENNReal.inv_pow]

theorem smul_set_subset_compl_zero (t : (ℂ)ˣ) {E : Set ℂ}
    (hE0 : E ⊆ {0}ᶜ) : (t : ℂ) • E ⊆ ({0}ᶜ : Set ℂ) := by
  rintro x ⟨y, hy, rfl⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, smul_eq_mul]
  exact mul_ne_zero (Units.ne_zero t) (fun h => hE0 hy (by simp [h]))

theorem measurableSet_units_smul (t : (ℂ)ˣ) {E : Set ℂ}
    (hE : MeasurableSet E) : MeasurableSet ((t : ℂ) • E) := by
  have h : (t : ℂ) • E
      = (fun x => ((t⁻¹ : (ℂ)ˣ) : ℂ) * x) ⁻¹' E := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (Units.ne_zero t), Set.mem_preimage]
    rw [Units.val_inv_eq_inv_val]
    rfl
  rw [h]
  exact hE.preimage (measurable_const_mul _)

theorem mulMeasure_units_smul (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (ℂ)ˣ, distribHaarChar ℂ t = ‖(t : ℂ)‖₊ ^ d)
    (t : (ℂ)ˣ) {E : Set ℂ}
    (hE : MeasurableSet E) (hE0 : E ⊆ {0}ᶜ) :
    mulMeasure μ ((t : ℂ) • E) = mulMeasure μ E := by
  have hne : ((‖(t : ℂ)‖₊ ^ d : ℝ≥0∞)) ≠ 0 :=
    pow_ne_zero d (ENNReal.coe_ne_zero.mpr (nnnorm_ne_zero_iff.mpr (Units.ne_zero t)))
  have hnt : ((‖(t : ℂ)‖₊ ^ d : ℝ≥0∞)) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hcE : MeasurableSet ((t : ℂ) • E) := measurableSet_units_smul t hE
  rw [mulMeasure_completion_eq d hd hΔ, withDensity_apply _ hcE, withDensity_apply _ hE,
    Measure.restrict_restrict hcE, Measure.restrict_restrict hE,
    Set.inter_eq_left.mpr (smul_set_subset_compl_zero t hE0), Set.inter_eq_left.mpr hE0]
  have hμ : μ = (‖(t : ℂ)‖₊ ^ d : ℝ≥0∞) • Measure.map ((t : ℂ) • ·) μ := by
    rw [map_units_smul d hd hΔ t, smul_smul, ENNReal.mul_inv_cancel hne hnt, one_smul]
  have hpre : ((t : ℂ) • ·) ⁻¹' ((t : ℂ) • E) = E := by
    ext x
    simp only [Set.mem_preimage]
    exact Set.smul_mem_smul_set_iff₀ (Units.ne_zero t) E x
  calc ∫⁻ x in (t : ℂ) • E, ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ
      = (‖(t : ℂ)‖₊ ^ d : ℝ≥0∞)
          * ∫⁻ x in (t : ℂ) • E, ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹
              ∂(Measure.map ((t : ℂ) • ·) μ) := by
        conv_lhs => rw [hμ]
        rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    _ = (‖(t : ℂ)‖₊ ^ d : ℝ≥0∞)
          * ∫⁻ y in E, ((‖(t : ℂ) • y‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ := by
        rw [setLIntegral_map hcE (measurable_nnnorm_pow_inv d) (measurable_const_smul _), hpre]
    _ = ∫⁻ y in E, ((‖y‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ := by
        have hint : ∀ y : ℂ, (((‖(t : ℂ) • y‖₊ ^ d : ℝ≥0∞)))⁻¹
            = ((‖(t : ℂ)‖₊ ^ d : ℝ≥0∞))⁻¹ * ((‖y‖₊ ^ d : ℝ≥0∞))⁻¹ := by
          intro y
          rw [smul_eq_mul, nnnorm_mul, ENNReal.coe_mul, mul_pow]
          exact ENNReal.mul_inv (Or.inl hne) (Or.inl (ENNReal.pow_ne_top ENNReal.coe_ne_top))
        simp only [hint]
        rw [lintegral_const_mul _ (measurable_nnnorm_pow_inv d), ← mul_assoc,
          ENNReal.mul_inv_cancel hne hnt, one_mul]

theorem isOpenEmbedding_val_completion :
    Topology.IsOpenEmbedding (Units.val : (ℂ)ˣ → ℂ) :=
  Units.isOpenEmbedding_val

theorem image_val_subset_compl_zero (A : Set (ℂ)ˣ) :
    (Units.val '' A : Set ℂ) ⊆ {0}ᶜ := by
  rintro x ⟨u, _, rfl⟩
  exact u.ne_zero

theorem image_val_preimage_mul (t : (ℂ)ˣ) (A : Set (ℂ)ˣ) :
    (Units.val '' ((fun u => t * u) ⁻¹' A) : Set ℂ)
      = ((t⁻¹ : (ℂ)ˣ) : ℂ) • (Units.val '' A) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨((t * u : (ℂ)ˣ) : ℂ), ⟨t * u, hu, rfl⟩, ?_⟩
    show ((t⁻¹ : (ℂ)ˣ) : ℂ) • ((t * u : (ℂ)ˣ) : ℂ)
        = (u : ℂ)
    rw [smul_eq_mul, Units.val_mul, Units.val_inv_eq_inv_val, ← mul_assoc,
      inv_mul_cancel₀ (Units.ne_zero t), one_mul]
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨t⁻¹ * v, by simpa using hv, ?_⟩
    show ((t⁻¹ * v : (ℂ)ˣ) : ℂ)
        = ((t⁻¹ : (ℂ)ˣ) : ℂ) • (v : ℂ)
    rw [Units.val_mul, smul_eq_mul]

variable [MeasurableSpace (ℂ)ˣ] [BorelSpace (ℂ)ˣ]

theorem measurableEmbedding_val_completion :
    MeasurableEmbedding (Units.val : (ℂ)ˣ → ℂ) :=
  (isOpenEmbedding_val_completion ).measurableEmbedding

def mulHaarCompletion (μ : Measure ℂ) : Measure (ℂ)ˣ :=
  Measure.comap Units.val (mulMeasure μ)

theorem mulHaarCompletion_apply {A : Set (ℂ)ˣ} (hA : MeasurableSet A) :
    mulHaarCompletion μ A = mulMeasure μ (Units.val '' A) :=
  Measure.comap_apply _ (fun _ _ h => Units.ext h)
    (fun _ hs => (measurableEmbedding_val_completion ).measurableSet_image' hs) _ hA

theorem isMulLeftInvariant_mulHaarCompletion (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (ℂ)ˣ, distribHaarChar ℂ t = ‖(t : ℂ)‖₊ ^ d) :
    (mulHaarCompletion μ).IsMulLeftInvariant := by
  refine ⟨fun t => ?_⟩
  refine Measure.ext fun A hA => ?_
  have hmt : Measurable fun u : (ℂ)ˣ => t * u :=
    (Homeomorph.mulLeft t).continuous.measurable
  rw [Measure.map_apply hmt hA]
  have hpre : MeasurableSet ((fun u => t * u) ⁻¹' A) := hA.preimage hmt
  rw [mulHaarCompletion_apply hpre, mulHaarCompletion_apply hA, image_val_preimage_mul]
  exact mulMeasure_units_smul d hd hΔ t⁻¹
    ((measurableEmbedding_val_completion ).measurableSet_image' hA)
    (image_val_subset_compl_zero A)

theorem mulMeasure_image_val_eq (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (ℂ)ˣ, distribHaarChar ℂ t = ‖(t : ℂ)‖₊ ^ d)
    {A : Set (ℂ)ˣ} (hA : MeasurableSet A) :
    mulMeasure μ (Units.val '' A)
      = ∫⁻ x in (Units.val '' A), ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ := by
  have hAm : MeasurableSet (Units.val '' A : Set ℂ) :=
    (measurableEmbedding_val_completion ).measurableSet_image' hA
  rw [mulMeasure_completion_eq d hd hΔ, withDensity_apply _ hAm, Measure.restrict_restrict hAm,
    Set.inter_eq_left.mpr (image_val_subset_compl_zero A)]

theorem isFiniteMeasureOnCompacts_mulHaarCompletion (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (ℂ)ˣ, distribHaarChar ℂ t = ‖(t : ℂ)‖₊ ^ d) :
    IsFiniteMeasureOnCompacts (mulHaarCompletion μ) := by
  refine ⟨fun K hK => ?_⟩
  rw [mulHaarCompletion_apply hK.measurableSet, mulMeasure_image_val_eq d hd hΔ hK.measurableSet]
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  have hKc : IsCompact (Units.val '' K : Set ℂ) :=
    hK.image (isOpenEmbedding_val_completion ).continuous
  obtain ⟨x₀, hx₀K, hx₀min⟩ :=
    hKc.exists_isMinOn (hne.image _) continuous_norm.continuousOn
  have hx₀0 : x₀ ≠ 0 := image_val_subset_compl_zero K hx₀K
  have hb : ∀ x ∈ (Units.val '' K : Set ℂ),
      ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ≤ ((‖x₀‖₊ ^ d : ℝ≥0∞))⁻¹ := by
    intro x hx
    refine ENNReal.inv_le_inv.mpr ?_
    have : ‖x₀‖₊ ≤ ‖x‖₊ := by exact_mod_cast (isMinOn_iff.mp hx₀min) x hx
    exact_mod_cast pow_le_pow_left' this d
  calc ∫⁻ x in (Units.val '' K), ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ
      ≤ ∫⁻ _ in (Units.val '' K), ((‖x₀‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ :=
        setLIntegral_mono' hKc.measurableSet hb
    _ = ((‖x₀‖₊ ^ d : ℝ≥0∞))⁻¹ * μ (Units.val '' K) := by rw [setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.inv_lt_top.mpr (ENNReal.pow_pos (ENNReal.coe_pos.mpr (nnnorm_pos.mpr hx₀0)) d))
        hKc.measure_lt_top

theorem isOpenPosMeasure_mulHaarCompletion (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (ℂ)ˣ, distribHaarChar ℂ t = ‖(t : ℂ)‖₊ ^ d) :
    (mulHaarCompletion μ).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [mulHaarCompletion_apply hU.measurableSet, mulMeasure_image_val_eq d hd hΔ hU.measurableSet]
  obtain ⟨u, hu⟩ := hne
  set W : Set ℂ := (Units.val '' U)
      ∩ Metric.ball ((u : (ℂ)ˣ) : ℂ) (‖((u : (ℂ)ˣ) : ℂ)‖ / 2)
    with hW
  have hWo : IsOpen W :=
    ((isOpenEmbedding_val_completion ).isOpenMap _ hU).inter Metric.isOpen_ball
  have hWne : W.Nonempty :=
    ⟨(u : ℂ), ⟨u, hu, rfl⟩,
      Metric.mem_ball_self (half_pos (norm_pos_iff.mpr (Units.ne_zero u)))⟩
  have hbound : ∀ x ∈ W,
      ((((‖((u : (ℂ)ˣ) : ℂ)‖₊ * 2) ^ d : ℝ≥0∞)))⁻¹
        ≤ ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ := by
    intro x hx
    refine ENNReal.inv_le_inv.mpr ?_
    have hxb : ‖x‖₊ ≤ ‖((u : (ℂ)ˣ) : ℂ)‖₊ * 2 := by
      have hdist := Metric.mem_ball.mp hx.2
      rw [dist_eq_norm] at hdist
      have : ‖x‖ ≤ ‖((u : (ℂ)ˣ) : ℂ)‖ * 2 := by
        have h1 := norm_le_norm_add_norm_sub' x ((u : (ℂ)ˣ) : ℂ)
        nlinarith [norm_nonneg ((u : (ℂ)ˣ) : ℂ),
          norm_nonneg (x - ((u : (ℂ)ˣ) : ℂ))]
      exact_mod_cast this
    calc ((‖x‖₊ ^ d : ℝ≥0) : ℝ≥0∞)
        ≤ (((‖((u : (ℂ)ˣ) : ℂ)‖₊ * 2) ^ d : ℝ≥0) : ℝ≥0∞) := by
          exact_mod_cast pow_le_pow_left' hxb d
      _ = ((((‖((u : (ℂ)ˣ) : ℂ)‖₊ * 2) ^ d : ℝ≥0∞))) := by push_cast; ring
  have hpos : (0 : ℝ≥0∞) < ∫⁻ x in (Units.val '' U), ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ := by
    calc (0 : ℝ≥0∞)
        < ((((‖((u : (ℂ)ˣ) : ℂ)‖₊ * 2) ^ d : ℝ≥0∞)))⁻¹ * μ W := by
          refine ENNReal.mul_pos ?_ (hWo.measure_pos μ hWne).ne'
          exact ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top (ENNReal.mul_ne_top
            ENNReal.coe_ne_top (by simp)))
      _ = ∫⁻ _ in W, ((((‖((u : (ℂ)ˣ) : ℂ)‖₊ * 2) ^ d : ℝ≥0∞)))⁻¹ ∂μ :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in W, ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ := setLIntegral_mono' hWo.measurableSet hbound
      _ ≤ ∫⁻ x in (Units.val '' U), ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ :=
          lintegral_mono_set Set.inter_subset_left
  exact hpos.ne'

theorem isHaarMeasure_mulHaarCompletion (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (ℂ)ˣ, distribHaarChar ℂ t = ‖(t : ℂ)‖₊ ^ d) :
    (mulHaarCompletion μ).IsHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := isFiniteMeasureOnCompacts_mulHaarCompletion d hd hΔ
    toIsMulLeftInvariant := isMulLeftInvariant_mulHaarCompletion d hd hΔ
    toIsOpenPosMeasure := isOpenPosMeasure_mulHaarCompletion d hd hΔ }


end Support

variable [MeasurableSpace ℂˣ] [BorelSpace ℂˣ]

local instance : SecondCountableTopology ℂˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

theorem complex_modulus_eq (z : ℂ) : modulus z = ‖z‖₊ ^ 2 :=
  P2MW.S_LanglandsTunnell_TateLocal_realZeta_eq_localZeta.P7Rows.ArchBridge.modulus_complex_eq_nnnorm_sq z

theorem complex_distribHaarChar_eq (z : ℂˣ) :
    distribHaarChar ℂ z = ‖(z : ℂ)‖₊ ^ 2 :=
  P2MW.S_LanglandsTunnell_TateLocal_realZeta_eq_localZeta.P7Rows.ArchBridge.distribHaarChar_complex_eq_nnnorm_sq z

/-- The density has support in the punctured plane and is |z| to power -2. -/
def complexAdditiveDensity : Measure ℂ :=
  (volume.restrict {0}ᶜ).withDensity (fun z : ℂ => ((‖z‖₊ ^ 2 : ℝ≥0∞))⁻¹)

theorem complexAdditiveDensity_eq_mulMeasure :
    complexAdditiveDensity = mulMeasure (volume : Measure ℂ) := by
  unfold complexAdditiveDensity
  exact (Support.mulMeasure_completion_eq 2 two_ne_zero complex_distribHaarChar_eq).symm

def complexDensityHaar : Measure ℂˣ :=
  Measure.comap Units.val complexAdditiveDensity

instance complexDensityHaar_isHaar : IsHaarMeasure complexDensityHaar := by
  unfold complexDensityHaar
  rw [complexAdditiveDensity_eq_mulMeasure]
  exact Support.isHaarMeasure_mulHaarCompletion 2 two_ne_zero complex_distribHaarChar_eq

def complexHaarDensityScalar : ℝ≥0 :=
  haarScalarFactor (Measure.haar : Measure ℂˣ) complexDensityHaar

theorem complexHaarDensityScalar_pos : 0 < complexHaarDensityScalar :=
  haarScalarFactor_pos_of_isHaarMeasure _ _

theorem complexHaar_eq_smul_density :
    (Measure.haar : Measure ℂˣ) = complexHaarDensityScalar • complexDensityHaar :=
  isMulLeftInvariant_eq_smul _ _

theorem integral_complexDensityHaar (f : ℂ → ℂ) :
    (∫ u : ℂˣ, f (u : ℂ) ∂complexDensityHaar) =
      ∫ z, f z ∂mulMeasure (volume : Measure ℂ) := by
  have hval : MeasurableEmbedding (Units.val : ℂˣ → ℂ) :=
    Units.isOpenEmbedding_val.measurableEmbedding
  unfold complexDensityHaar
  rw [complexAdditiveDensity_eq_mulMeasure,
    ← hval.integral_map, hval.map_comap,
    P2MW.S_NumberField_TateGlobal_integrable_zetaIntegrand.NumberField.TateGlobal.range_units_val,
    P2MW.S_NumberField_TateGlobal_integrable_zetaIntegrand.NumberField.TateGlobal.mulMeasure_restrict_compl_zero]

theorem integral_complexHaar_eq_mulMeasure (f : ℂ → ℂ) :
    (∫ u : ℂˣ, f (u : ℂ) ∂(Measure.haar : Measure ℂˣ)) =
      ((complexHaarDensityScalar : ℝ) : ℂ) *
        ∫ z, f z ∂mulMeasure (volume : Measure ℂ) := by
  rw [complexHaar_eq_smul_density, integral_smul_nnreal_measure,
    NNReal.smul_def, Complex.real_smul, integral_complexDensityHaar]

theorem integrable_complexHaar_of_mulMeasure (f : ℂ → ℂ)
    (hf : Integrable f (mulMeasure (volume : Measure ℂ))) :
    Integrable (fun u : ℂˣ => f (u : ℂ)) (Measure.haar : Measure ℂˣ) := by
  rw [complexHaar_eq_smul_density]
  apply Integrable.smul_measure_nnreal
  change Integrable (fun u : ℂˣ => f (u : ℂ))
    (Measure.comap Units.val complexAdditiveDensity)
  rw [complexAdditiveDensity_eq_mulMeasure]
  exact
    (P2MW.S_NumberField_TateGlobal_integrable_zetaIntegrand.NumberField.TateGlobal.integrable_comp_val_comap_mulMeasure_iff
      Units.isOpenEmbedding_val.measurableEmbedding volume f).mpr hf

theorem integral_complexHaar_weighted (f : ℂ → ℂ) (s : ℂ) :
    (∫ u : ℂˣ, f (u : ℂ) * ((‖(u : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s
      ∂(Measure.haar : Measure ℂˣ)) =
      ((complexHaarDensityScalar : ℝ) : ℂ) *
        ∫ z in ({0}ᶜ : Set ℂ), f z * (‖z‖ : ℂ) ^ (2 * s - 2) := by
  rw [integral_complexHaar_eq_mulMeasure
    (fun z : ℂ => f z * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s)]
  congr 1
  have hm : AEMeasurable (fun z : ℂ => (modulus z)⁻¹)
      ((volume : Measure ℂ).restrict {0}ᶜ) := by
    simp_rw [complex_modulus_eq]
    exact (measurable_nnnorm.pow_const 2).inv.aemeasurable
  rw [P2MW.S_LanglandsTunnell_TateLocal_realZeta_eq_localZeta.P7Rows.ArchBridge.integral_mulMeasure
    volume _ hm]
  apply setIntegral_congr_fun (MeasurableSet.singleton (0 : ℂ)).compl
  intro z hz
  beta_reduce
  have hz0 : z ≠ 0 := by simpa using hz
  have hn : (‖z‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz0)
  have hpow : ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s = (‖z‖ : ℂ) ^ (2 * s) := by
    rw [pow_two, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
      ← Complex.cpow_add _ _ hn]
    congr 1
    ring
  have hinv : ((((‖z‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ) : ℂ) = (‖z‖ : ℂ) ^ (-2 : ℂ) := by
    rw [show (-2 : ℂ) = (-1) + (-1) from by ring,
      Complex.cpow_add _ _ hn, Complex.cpow_neg_one]
    simp only [NNReal.coe_inv, NNReal.coe_pow, coe_nnnorm,
      Complex.ofReal_inv, Complex.ofReal_pow]
    rw [← inv_pow]
    ring
  rw [complex_modulus_eq]
  simp only [NNReal.smul_def, Complex.real_smul]
  rw [hpow, hinv]
  calc
    (‖z‖ : ℂ) ^ (-2 : ℂ) * (f z * (‖z‖ : ℂ) ^ (2 * s)) =
        f z * ((‖z‖ : ℂ) ^ (-2 : ℂ) * (‖z‖ : ℂ) ^ (2 * s)) := by ring
    _ = f z * (‖z‖ : ℂ) ^ ((-2 : ℂ) + 2 * s) := by
      rw [← Complex.cpow_add _ _ hn]
    _ = f z * (‖z‖ : ℂ) ^ (2 * s - 2) := by congr 2 <;> ring

/-- The original complex multiplicative norm is norm squared. -/
theorem integral_complexHaar_sixth (f : ℂ → ℂ) :
    (∫ u : ℂˣ, f (u : ℂ) * ((‖(u : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (1 / 6 : ℂ)
      ∂(Measure.haar : Measure ℂˣ)) =
      ((complexHaarDensityScalar : ℝ) : ℂ) *
        ∫ z in ({0}ᶜ : Set ℂ), f z * (‖z‖ : ℂ) ^ (-5 / 3 : ℂ) := by
  convert integral_complexHaar_weighted f (1 / 6) using 1 <;> norm_num

/-- The negative-sign Fourier integral is used literally, with Lebesgue measure. -/
theorem integral_complexHaar_fourier_sixth (ψ : AddChar ℂ ℂ) (W : ℂ → ℂ) :
    (∫ u : ℂˣ, NumberField.AdelicFourier.fourierIntegral ψ volume W (u : ℂ) *
      ((‖(u : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (1 / 6 : ℂ)
      ∂(Measure.haar : Measure ℂˣ)) =
      ((complexHaarDensityScalar : ℝ) : ℂ) *
        ∫ z in ({0}ᶜ : Set ℂ),
          NumberField.AdelicFourier.fourierIntegral ψ volume W z *
            (‖z‖ : ℂ) ^ (-5 / 3 : ℂ) :=
  integral_complexHaar_sixth _

end HeckeGeneral.Analysis.SLocalRadialHaarDraft.ComplexHaarDensityDraft
