import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSharpDualTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualGaussReconstruction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalActiveColumnWindow

/-!
# Actual second terminal windows from the original raw profile atoms

The original atom window constructs the central coefficient bound and
both active column windows. The post-extraction identity is supplied by
the six computed original-source dictionaries. The original Cartesian
carrier remains intact; its separate coarse window pays the tail.

The zero product exponent is nonnegative even for inactive sources.
When every actual coefficient is zero, both amplitudes are set to zero
on the same stage. Otherwise the sharp product exponent is recovered
from an actual original nonzero column and its integral ideal norm.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
namespace HeckeSkeleton.Moments.EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

section Terminal

variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)

namespace DualTerminalCalibration

variable {s}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

/-- A literal zero-coefficient source has zero amplitudes. All
physical rows, columns, factors, fibres and product exponents remain
those of the original calibration. -/
def zeroCoefficients
    (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (hzero : ∀ i ∈ G.columns, G.coefficient i = 0) :
    s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay where
  productExponent := T.productExponent
  profileExponent := T.profileExponent
  maskExponent := T.maskExponent
  inverseRadiusExponent := T.inverseRadiusExponent
  tailAmplitude := 0
  zeroAmplitude := 0
  zeroAmplitude_nonneg := le_rfl
  windows := {
    base_ge_one := T.windows.base_ge_one
    productExponent_nonneg := T.windows.productExponent_nonneg
    amplitude_nonneg := le_rfl
    factors := T.windows.factors
    multiplicity := T.windows.multiplicity
    factors_fiber_card := T.windows.factors_fiber_card
    factor_product := T.windows.factor_product
    product_norm := T.windows.product_norm
    profile_seminorm := by
      intro v hv
      have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
      simp only [hzero _ hm.1, zero_mul, zero_smul, map_zero, mul_zero]
    mask_norm := T.windows.mask_norm
    inverse_radius := T.windows.inverse_radius }
  exponent_bound := T.exponent_bound
  cutoff_eq := T.cutoff_eq
  zeroProductExponent := T.zeroProductExponent
  zeroProductExponent_nonneg := T.zeroProductExponent_nonneg
  zero_product_norm := T.zero_product_norm
  zeroDivisor := T.zeroDivisor
  zeroDivisor_ne_zero := T.zeroDivisor_ne_zero
  zero_divisor_dvd := T.zero_divisor_dvd
  zero_normalization := by
    intro v hv
    have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
    simp only [hzero _ hm.1, zero_mul, zero_smul, map_zero, zero_div]

end DualTerminalCalibration

/-- Nonzero original coefficients force the sharp upper exponent
to be nonnegative. This is not imposed on inactive common blocks. -/
theorem active_column_exponent_nonneg (Z exponent : ℝ) (hZ : 1 < Z)
    (hupper : ∀ i ∈ G.columns, G.coefficient i ≠ 0 →
      A.exteriorNorm (G.ideal i) ≤ Z ^ exponent)
    (hactive : ∃ i ∈ G.columns, G.coefficient i ≠ 0) : 0 ≤ exponent := by
  obtain ⟨i, hi, hc⟩ := hactive
  have hone : 1 ≤ A.exteriorNorm (G.ideal i) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (G.ideal i).property.1)
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  simpa only [Real.rpow_zero] using hone.trans (hupper i hi hc)

theorem originalSharpZeroPower (Z total pre frozen loss inverse δ : ℝ) (hZ : 0 < Z) :
    Z ^ (-total + 2 * pre * δ - (total - loss - frozen)) * Z ^ inverse *
        Real.sqrt (Z ^ (2 * (total + loss - frozen))) =
      Z ^ (-total + 2 * pre * δ + inverse + 2 * loss) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le, ← Real.rpow_add hZ,
    ← Real.rpow_add hZ]
  congr 1
  ring

section OriginalAtoms

variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {a : RealParameters} {Z t Y₁ Y₂ : ℝ} {centered : Bool}
variable (atoms : ParentConstantAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t)
variable {common : A.Exterior} {divisor : Ideal (𝓞 K)} {δ : ℝ}
variable (D : G.OriginalNumerator (atoms.raw Y₁ Y₂).exteriorColumns
  (atoms.raw Y₁ Y₂).columnExterior ((atoms.values Y₁ Y₂).coefficient centered)
  divisor common δ)
variable (post : G.OriginalPostIdeal (atoms.raw Y₁ Y₂).columnExterior D.index)

/-- All analytic column inputs are proved from the actual original
single-profile window. `D` and `post` are the six computed source
dictionaries, not estimates on a terminal or a transformed source.
Only the original tuple fibres and physical cutoff/radius/mask windows
remain as primitive inputs. -/
def canonicalOriginalDualCalibration
    (hdivisor : divisor ≠ 0) (hδ : 0 ≤ δ)
    (hleftArithmetic : ∀ I, ‖atoms.leftArithmetic I‖ ≤ 1)
    (hrightArithmetic : ∀ I, ‖atoms.rightArithmetic I‖ ≤ 1)
    (hprimeArithmetic : ∀ i p, ‖atoms.primeArithmetic i p‖ ≤ 1)
    (cap : ℕ) (orders : Finset (ℕ × ℕ))
    (B lo hi loss leftExponent rightExponent : ℝ)
    (hB : 1 ≤ B) (hlo : 0 < lo) (hloOne : lo ≤ 1) (hhi : 1 ≤ hi)
    (hcap : d.geometry.slotCount ≤ cap)
    (hlowerThreshold : (lo ^ (cap + 2))⁻¹ ≤ Z ^ loss)
    (hupperThreshold : hi ^ (cap + 2) ≤ Z ^ loss)
    {floor padding : ℝ}
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hleftPower : Z ^ a.n₁ ≤ Z ^ leftExponent)
    (hrightPower : Z ^ a.n₂ ≤ Z ^ rightExponent)
    (hY₁le : Y₁ ≤ Z ^ leftExponent) (hY₂le : Y₂ ≤ Z ^ rightExponent)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window
      (OriginalProfileAtomBounds.profileOrders orders) d B)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain)
    (hlowerWindow : window ⊆ Set.Ici lo) (hupperWindow : window ⊆ Set.Iic hi)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ)
    (Lmax Nsave decay maskExponent inverseRadiusExponent : ℝ)
    (hcoarse : 0 ≤ leftExponent + rightExponent + d.geometry.totalLength + loss)
    (factors : ι × ι → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ)
    (hfibers : ∀ v,
      ((G.columns ×ˢ G.columns).filter (fun ij => factors ij = v)).card ≤ multiplicity)
    (hfactor : ∀ ij ∈ G.columns ×ˢ G.columns,
      PowerfulDiagonal.tupleIdeal (factors ij) = (G.ideal ij.1).val * (G.ideal ij.2).val)
    (hmask : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) s.mask)).val ≤
        Z ^ maskExponent)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hdegree : secondTailExponent k
      (2 * (leftExponent + rightExponent + d.geometry.totalLength + loss))
      (((a.n₁ + a.n₂ + d.geometry.totalLength + loss - idealLogLength Z common.val) -
        (a.n₁ + a.n₂ + d.geometry.totalLength)) +
        2 * (a.n₁ + a.n₂ + d.geometry.totalLength + loss - idealLogLength Z common.val) * δ -
        2 * (a.n₁ + a.n₂ + d.geometry.totalLength - loss - idealLogLength Z post.frozen))
      maskExponent inverseRadiusExponent ≤ Lmax)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent Lmax Nsave decay) :
    s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay := by
  let total := a.n₁ + a.n₂ + d.geometry.totalLength
  let coarse := leftExponent + rightExponent + d.geometry.totalLength + loss
  let upper := total + loss - idealLogLength Z post.frozen
  have hz : 0 < Z := zero_lt_one.trans domain.scale
  have hcentral : ∀ i ∈ (atoms.raw Y₁ Y₂).exteriorColumns,
      ‖(atoms.values Y₁ Y₂).coefficient centered i‖ ≤
        (2 * B ^ (cap + 2)) * Z ^ (-total / 2) := by
    intro i hi'
    exact atoms.coefficient_norm_le_raw_profile_window profiles
      hleftArithmetic hrightArithmetic hprimeArithmetic cap hcap hB hz hrows ht centered
      domain.comparison_scale_left_nonneg domain.comparison_product_eq_power i
      (Finset.mem_filter.mp hi').1
  have hfull : ∀ i ∈ (atoms.raw Y₁ Y₂).exteriorColumns,
      (atoms.values Y₁ Y₂).coefficient centered i ≠ 0 →
        A.exteriorNorm ((atoms.raw Y₁ Y₂).columnExterior i) ≤ Z ^ (total + loss) := by
    intro i hi' hc
    exact atoms.original_active_column_norm_le_power profiles cap hi loss hhi hcap
      hupperThreshold hz hrows ht hupperWindow centered
      domain.comparison_scale_left_nonneg domain.comparison_product_eq_power i hi' hc
  have hlow : ∀ i ∈ G.columns, G.coefficient i ≠ 0 →
      Z ^ (total - loss - idealLogLength Z post.frozen) ≤ A.exteriorNorm (G.ideal i) := by
    intro i hi' hc
    apply post.lower Z (total - loss) domain.scale i hi'
    exact atoms.original_active_column_norm_lower_power profiles cap lo loss hlo hloOne hcap
      hlowerThreshold hz hrows ht hlowerWindow centered
      domain.comparison_scale_left_nonneg domain.comparison_product_eq_power (D.index i)
      (D.index_mem i hi') (D.original_nonzero i hi' hc)
  have hupper : ∀ i ∈ G.columns, G.coefficient i ≠ 0 →
      A.exteriorNorm (G.ideal i) ≤ Z ^ upper := by
    intro i hi' hc
    exact post.upper Z (total + loss) domain.scale i hi'
      (hfull _ (D.index_mem i hi') (D.original_nonzero i hi' hc))
  have hcoarseColumn : ∀ i ∈ G.columns, A.exteriorNorm (G.ideal i) ≤ Z ^ coarse := by
    intro i hi'
    apply (post.norm_le_original i hi').trans
    exact (atoms.raw Y₁ Y₂).original_union_column_norm_le_power profiles cap hi loss
      leftExponent rightExponent hhi hcap hupperThreshold hz hY₁ hY₂ hleftPower hrightPower
      hY₁le hY₂le hrows ht hupperWindow (D.index i) (D.index_mem i hi')
  have htail : ∀ ij ∈ G.columns ×ˢ G.columns,
      (Ideal.absNorm ((G.ideal ij.1).val * (G.ideal ij.2).val) : ℝ) ≤ Z ^ (2 * coarse) := by
    intro ij hij
    change _ ≤ _
    rw [map_mul, Nat.cast_mul, show 2 * coarse = coarse + coarse by ring, Real.rpow_add hz]
    exact mul_le_mul (hcoarseColumn _ (Finset.mem_product.mp hij).1)
      (hcoarseColumn _ (Finset.mem_product.mp hij).2) (A.exteriorNorm_pos _).le
      (Real.rpow_nonneg hz.le _)
  have hzero : ∀ ij ∈ G.columns ×ˢ G.columns,
      (G.coefficient ij.1 * star (G.coefficient ij.2)) • s.profile ≠ 0 →
      (Ideal.absNorm ((G.ideal ij.1).val * (G.ideal ij.2).val) : ℝ) ≤
        Z ^ (2 * max 0 upper) := by
    intro ij hij hgram
    have hl : G.coefficient ij.1 ≠ 0 := by
      intro he
      exact hgram (by simp only [he, zero_mul, zero_smul])
    have hr : G.coefficient ij.2 ≠ 0 := by
      intro he
      exact hgram (by simp only [he, star_zero, mul_zero, zero_smul])
    have hp := mul_le_mul (hupper _ (Finset.mem_product.mp hij).1 hl)
      (hupper _ (Finset.mem_product.mp hij).2 hr) (A.exteriorNorm_pos _).le
      (Real.rpow_nonneg hz.le _)
    have he : (Ideal.absNorm ((G.ideal ij.1).val * (G.ideal ij.2).val) : ℝ) ≤
        Z ^ (2 * upper) := by
      simpa only [map_mul, Nat.cast_mul, show 2 * upper = upper + upper by ring,
        Real.rpow_add hz] using hp
    exact he.trans (Real.rpow_le_rpow_of_exponent_le domain.scale.le
      (mul_le_mul_of_nonneg_left (le_max_right 0 upper) (by norm_num)))
  let T := s.dualCalibrationOfOriginalNumerator D hdivisor sTail sZero k
    Z Lmax Nsave decay total (total + loss) (2 * B ^ (cap + 2))
    (total - loss - idealLogLength Z post.frozen) (2 * coarse) (2 * max 0 upper)
    maskExponent inverseRadiusExponent domain.scale
    (mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans hB) _)) hδ hcentral hfull
    (mul_nonneg (by norm_num) hcoarse)
    (mul_nonneg (by norm_num) (le_max_left 0 upper)) factors multiplicity hfibers hfactor
    htail hzero hlow hmask hradius hdegree hcutoff
  by_cases hactive : ∃ i ∈ G.columns, G.coefficient i ≠ 0
  · exact T
  · exact T.zeroCoefficients (by
      intro i hi'
      by_contra hc
      exact hactive ⟨i, hi', hc⟩)

/-- Closed original amplitudes on the same calibration. A nonzero
supported fibre supplies `hphysical`; inactive coefficients contribute
zero, so no lower bound for an inactive formal residual length is used. -/
theorem canonicalOriginalDualCalibration_amplitude_bounds
    (hdivisor : divisor ≠ 0) (hδ : 0 ≤ δ)
    (hleftArithmetic : ∀ I, ‖atoms.leftArithmetic I‖ ≤ 1)
    (hrightArithmetic : ∀ I, ‖atoms.rightArithmetic I‖ ≤ 1)
    (hprimeArithmetic : ∀ i p, ‖atoms.primeArithmetic i p‖ ≤ 1)
    (cap : ℕ) (orders : Finset (ℕ × ℕ))
    (B lo hi loss leftExponent rightExponent : ℝ)
    (hB : 1 ≤ B) (hlo : 0 < lo) (hloOne : lo ≤ 1) (hhi : 1 ≤ hi)
    (hcap : d.geometry.slotCount ≤ cap)
    (hlowerThreshold : (lo ^ (cap + 2))⁻¹ ≤ Z ^ loss)
    (hupperThreshold : hi ^ (cap + 2) ≤ Z ^ loss)
    {floor padding : ℝ}
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hleftPower : Z ^ a.n₁ ≤ Z ^ leftExponent)
    (hrightPower : Z ^ a.n₂ ≤ Z ^ rightExponent)
    (hY₁le : Y₁ ≤ Z ^ leftExponent) (hY₂le : Y₂ ≤ Z ^ rightExponent)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window
      (OriginalProfileAtomBounds.profileOrders orders) d B)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain)
    (hlowerWindow : window ⊆ Set.Ici lo) (hupperWindow : window ⊆ Set.Iic hi)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ)
    (Lmax Nsave decay maskExponent inverseRadiusExponent : ℝ)
    (hcoarse : 0 ≤ leftExponent + rightExponent + d.geometry.totalLength + loss)
    (factors : ι × ι → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ)
    (hfibers : ∀ v,
      ((G.columns ×ˢ G.columns).filter (fun ij => factors ij = v)).card ≤ multiplicity)
    (hfactor : ∀ ij ∈ G.columns ×ˢ G.columns,
      PowerfulDiagonal.tupleIdeal (factors ij) = (G.ideal ij.1).val * (G.ideal ij.2).val)
    (hmask : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) s.mask)).val ≤
        Z ^ maskExponent)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hdegree : secondTailExponent k
      (2 * (leftExponent + rightExponent + d.geometry.totalLength + loss))
      (((a.n₁ + a.n₂ + d.geometry.totalLength + loss - idealLogLength Z common.val) -
        (a.n₁ + a.n₂ + d.geometry.totalLength)) +
        2 * (a.n₁ + a.n₂ + d.geometry.totalLength + loss - idealLogLength Z common.val) * δ -
        2 * (a.n₁ + a.n₂ + d.geometry.totalLength - loss - idealLogLength Z post.frozen))
      maskExponent inverseRadiusExponent ≤ Lmax)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent Lmax Nsave decay)
    (hphysical : G.rows.Nonempty) (hmaskEmpty : s.mask = ∅) :
    let T := s.canonicalOriginalDualCalibration atoms D post hdivisor hδ
      hleftArithmetic hrightArithmetic hprimeArithmetic cap orders B lo hi loss leftExponent rightExponent
      hB hlo hloOne hhi hcap hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower
      hY₁le hY₂le profiles hrows ht hlowerWindow hupperWindow sTail sZero k Lmax Nsave decay
      maskExponent inverseRadiusExponent hcoarse factors multiplicity hfibers hfactor hmask hradius hdegree hcutoff
    T.tailAmplitude ≤ ((2 * B ^ (cap + 2)) ^ 2 / (Ideal.absNorm divisor : ℝ)) *
        sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile ∧
      T.zeroAmplitude ≤
        (((2 * B ^ (cap + 2)) ^ 2 *
          sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile) /
            (Ideal.absNorm divisor : ℝ)) *
          Z ^ (-(a.n₁ + a.n₂ + d.geometry.totalLength) +
            2 * (a.n₁ + a.n₂ + d.geometry.totalLength + loss - idealLogLength Z common.val) * δ +
              inverseRadiusExponent + 2 * loss) := by
  dsimp only
  have hz : 0 < Z := zero_lt_one.trans domain.scale
  constructor
  · by_cases hactive : ∃ i ∈ G.columns, G.coefficient i ≠ 0
    · simp only [canonicalOriginalDualCalibration, dif_pos hactive,
        dualCalibrationOfOriginalNumerator, le_refl]
    · simp only [canonicalOriginalDualCalibration, dif_neg hactive,
        DualTerminalCalibration.zeroCoefficients]
      exact mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (apply_nonneg _ _)
  · by_cases hactive : ∃ i ∈ G.columns, G.coefficient i ≠ 0
    swap
    · simp only [canonicalOriginalDualCalibration, dif_neg hactive,
        DualTerminalCalibration.zeroCoefficients]
      exact mul_nonneg
        (div_nonneg (mul_nonneg (sq_nonneg _) (apply_nonneg _ _)) (Nat.cast_nonneg _))
        (Real.rpow_nonneg hz.le _)
    have hupper : ∀ i ∈ G.columns, G.coefficient i ≠ 0 →
        A.exteriorNorm (G.ideal i) ≤
          Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength + loss - idealLogLength Z post.frozen) := by
      intro i hi' hc
      apply post.upper Z (a.n₁ + a.n₂ + d.geometry.totalLength + loss) domain.scale i hi'
      exact atoms.original_active_column_norm_le_power profiles cap hi loss hhi hcap
        hupperThreshold hz hrows ht hupperWindow centered
        domain.comparison_scale_left_nonneg domain.comparison_product_eq_power (D.index i)
        (D.index_mem i hi') (D.original_nonzero i hi' hc)
    have hu := active_column_exponent_nonneg (G := G) Z
      (a.n₁ + a.n₂ + d.geometry.totalLength + loss - idealLogLength Z post.frozen)
      domain.scale hupper hactive
    simp only [canonicalOriginalDualCalibration, dif_pos hactive,
      dualCalibrationOfOriginalNumerator, max_eq_right hu, hmaskEmpty, Finset.card_empty,
      pow_zero, one_mul, D.countingDivisor_eq hphysical]
    apply le_of_eq
    calc
      _ = (((2 * B ^ (cap + 2)) ^ 2 *
          sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile) /
            (Ideal.absNorm divisor : ℝ)) *
          (Z ^ (-(a.n₁ + a.n₂ + d.geometry.totalLength) +
              2 * (a.n₁ + a.n₂ + d.geometry.totalLength + loss - idealLogLength Z common.val) * δ -
                (a.n₁ + a.n₂ + d.geometry.totalLength - loss - idealLogLength Z post.frozen)) *
            Z ^ inverseRadiusExponent *
              Real.sqrt (Z ^ (2 * (a.n₁ + a.n₂ + d.geometry.totalLength + loss -
                idealLogLength Z post.frozen)))) := by ring
      _ = _ := by
        rw [originalSharpZeroPower Z (a.n₁ + a.n₂ + d.geometry.totalLength)
          (a.n₁ + a.n₂ + d.geometry.totalLength + loss - idealLogLength Z common.val)
          (idealLogLength Z post.frozen) loss inverseRadiusExponent δ hz]


end OriginalAtoms

end ActualGaussStage

namespace CompleteMovingRowRecipe

open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Physical

variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

/-- The actual moving arithmetic recipe fills every arithmetic
atom bound internally. The remaining arguments are the original raw
single-profile window, computed source dictionaries, tuple fibres and
physical windows of the same canonical stage. -/
def canonicalOriginalDualCalibration
    (W : NormProfileRecipe data) (ξ : X) (a : RealParameters) (Z t Y₁ Y₂ : ℝ)
    (centered : Bool) {ι : Type*} {G : ActualGaussSource C ι}
    (s : ActualGaussStage (E := E)
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv hDiff G finiteTest)
    {common : A.Exterior} {divisor : Ideal (𝓞 K)} {δ : ℝ}
    (D : G.OriginalNumerator
      (((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t).raw Y₁ Y₂).exteriorColumns
      (((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t).raw Y₁ Y₂).columnExterior
      ((((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t).values Y₁ Y₂).coefficient centered)
      divisor common δ)
    (post : G.OriginalPostIdeal
      (((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t).raw Y₁ Y₂).columnExterior D.index)
    (hdivisor : divisor ≠ 0) (hδ : 0 ≤ δ) :=
  s.canonicalOriginalDualCalibration
    ((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t) D post hdivisor hδ
    (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
    (Q.arithmeticAtoms_prime_norm_le_one ξ)

end CompleteMovingRowRecipe
end Terminal
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.zeroCoefficients
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.active_column_exponent_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalOriginalDualCalibration

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalOriginalDualCalibration_amplitude_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalOriginalDualCalibration
