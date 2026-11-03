import HeckeGeneral.Analysis.TraceJointSchwartzCutoff
import HeckeGeneral.Analysis.TraceProductCovolume
import HeckeGeneral.Bridge.TraceSchwartzFourierBounds
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Fourier bounds for the actual two-column orbital kernel

The cutoff kernel is initially a Schwartz map on the ordinary, maximum-norm
product. Fourier transformation is performed on its `WithLp 2` copy, with the
genuine inner product. The trace transform conjugates both frequency columns
and includes the square of the one-column mixed-measure inverse Jacobian.

The final estimate controls every target Fourier seminorm by finitely many
seminorms of the original one-column test function, uniformly above a threshold
determined by the fixed cutoff. It does not identify a Gram kernel, select a
unit partition, or discard either dual coordinate axis.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField NumberField.InfinitePlace IsDedekindDomain
  HeckeGeneral.Arithmetic HeckeGeneral.Bridge MeasureTheory NumberField.AdelicFourier
open scoped Classical ContDiff BigOperators nonZeroDivisors FourierTransform NNReal

variable (K : Type) [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "M∞" => mixedEmbedding.mixedSpace K

/-- The Euclidean two-column space; the ordinary product retains its max norm. -/
abbrev TraceJointEuclideanSpace := WithLp 2 (V × V)

local notation "W" => TraceJointEuclideanSpace K

/-- The ordinary product has the product of the two canonical volumes. -/
instance (priority := 100) measureSpace_traceJointProduct : MeasureSpace (V × V) := by
  letI : MeasureSpace V := inferInstance
  exact Measure.prod.measureSpace

/-- The usual Borel structure on the nested Hilbert product, exposed directly
so Fourier's typeclass search does not repeat the full nested construction. -/
instance borelSpace_traceJointEuclideanSpace : BorelSpace W := inferInstance

/-- Coordinate transport, without assigning an inner product to the max product. -/
def traceJointToProduct : W ≃L[ℝ] V × V :=
  WithLp.prodContinuousLinearEquiv 2 ℝ V V

/-- Both complex frequency columns are conjugated in the trace pairing. -/
def traceJointConjugation : W ≃ₗᵢ[ℝ] W :=
  LinearIsometryEquiv.withLpProdCongr 2
    (traceConjugation K) (traceConjugation K)

@[simp] theorem traceJointConjugation_fst (y : W) :
    (traceJointConjugation K y).fst = traceConjugation K y.fst := rfl

@[simp] theorem traceJointConjugation_snd (y : W) :
    (traceJointConjugation K y).snd = traceConjugation K y.snd := rfl

/-- The pairing is the sum of the two actual mixed trace pairings. -/
theorem traceJoint_pairing_eq_inner (x y : W) :
    Algebra.trace ℝ M∞ (traceToMixed K x.fst * traceToMixed K y.fst) +
        Algebra.trace ℝ M∞ (traceToMixed K x.snd * traceToMixed K y.snd) =
      inner ℝ x (traceJointConjugation K y) := by
  rw [trace_mul_traceToMixed, trace_mul_traceToMixed, WithLp.prod_inner_apply]
  rfl

/-- The `WithLp 2` coordinate change preserves product Euclidean volume. -/
theorem measurePreserving_traceJointToProduct :
    MeasurePreserving (traceJointToProduct K)
      (volume (α := W)) (volume (α := V × V)) :=
  WithLp.volume_preserving_ofLp V V

/-- The actual two-column map to the mixed archimedean space. -/
def traceJointToMixed : W ≃L[ℝ] M∞ × M∞ :=
  (traceJointToProduct K).trans ((traceToMixed K).prodCongr (traceToMixed K))

@[simp] theorem traceJointToMixed_apply (x : W) :
    traceJointToMixed K x = (traceToMixed K x.fst, traceToMixed K x.snd) := rfl

/-- Product mixed Haar normalization: the Jacobian occurs once per column. -/
theorem map_traceJointToMixed_volume :
    Measure.map (traceJointToMixed K) (volume (α := W)) =
      ENNReal.ofReal (((2 : ℝ) ^ nrComplexPlaces K) ^ 2) •
        (volume : Measure (M∞ × M∞)) := by
  have hm : Measurable (Prod.map (traceToMixed K) (traceToMixed K)) :=
    (traceToMixed K).continuous.measurable.prodMap
      (traceToMixed K).continuous.measurable
  change Measure.map
    ((Prod.map (traceToMixed K) (traceToMixed K)) ∘ (traceJointToProduct K))
      volume = _
  rw [← Measure.map_map hm (traceJointToProduct K).continuous.measurable,
    (measurePreserving_traceJointToProduct K).map_eq]
  rw [Measure.volume_eq_prod, ← Measure.map_prod_map _ _
    (traceToMixed K).continuous.measurable (traceToMixed K).continuous.measurable,
    map_traceToMixed_volume,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
  simp only [pow_two, Measure.volume_eq_prod]

/-- This identity retains the actual mixed measure, including its squared
Jacobian. No integrability assumption is needed for totalized integrals. -/
theorem integral_eq_inv_jacobian_traceJointToMixed (f : M∞ × M∞ → ℂ) :
    (∫ z : M∞ × M∞, f z) =
      (((((2 : ℝ) ^ nrComplexPlaces K) ^ 2)⁻¹ : ℝ) : ℂ) *
        (∫ x : W, f (traceJointToMixed K x)) := by
  have he : MeasurableEmbedding (traceJointToMixed K) :=
    (traceJointToMixed K).toHomeomorph.measurableEmbedding
  have hchange : (∫ x : W, f (traceJointToMixed K x)) =
      (((2 : ℝ) ^ nrComplexPlaces K) ^ 2) • (∫ z : M∞ × M∞, f z) := by
    rw [← he.integral_map f, map_traceJointToMixed_volume, integral_smul_measure,
      ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [hchange, Complex.real_smul]
  push_cast
  have hc : ((2 : ℂ) ^ nrComplexPlaces K) ^ 2 ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ (by norm_num))
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- The actual two-column trace Fourier operator on the inner-product space.
The scalar is the inverse of the squared mixed-measure Jacobian. -/
def traceJointFourierCLM : SchwartzMap W ℂ →L[ℂ] SchwartzMap W ℂ :=
  (((((2 : ℝ) ^ nrComplexPlaces K) ^ 2)⁻¹ : ℝ) : ℂ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (traceJointConjugation K).toContinuousLinearEquiv).comp
        (SchwartzMap.fourierTransformCLM ℂ)

@[simp] theorem traceJointFourierCLM_apply (F : SchwartzMap W ℂ) (y : W) :
    traceJointFourierCLM K F y =
      (((((2 : ℝ) ^ nrComplexPlaces K) ^ 2)⁻¹ : ℝ) : ℂ) *
        (𝓕 (F : W → ℂ)) (traceJointConjugation K y) := rfl

/-- An explicit integral with the negative Fourier sign and both trace columns. -/
theorem traceJointFourierCLM_eq_trace_integral (F : SchwartzMap W ℂ) (y : W) :
    traceJointFourierCLM K F y =
      (((((2 : ℝ) ^ nrComplexPlaces K) ^ 2)⁻¹ : ℝ) : ℂ) *
        ∫ x : W,
          (Real.fourierChar (-(
            Algebra.trace ℝ M∞ (traceToMixed K x.fst * traceToMixed K y.fst) +
            Algebra.trace ℝ M∞ (traceToMixed K x.snd * traceToMixed K y.snd))) : ℂ) *
            F x := by
  rw [traceJointFourierCLM_apply, Real.fourier_eq]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [traceJoint_pairing_eq_inner]
    simp only [Circle.smul_def, smul_eq_mul]

/-- This is the literal two-column mixed Fourier integral with the standard
positive additive character evaluated at the negative trace pairing. In
particular the squared Jacobian in the operator is fixed by the actual Haar
change of variables, rather than a chosen self-dual normalization. -/
theorem traceJointFourierCLM_eq_mixed_integral (F : SchwartzMap W ℂ) (y : W) :
    traceJointFourierCLM K F y =
      ∫ z : M∞ × M∞,
        (standardMixedAddCharacter K (-(
          z.1 * traceToMixed K y.fst + z.2 * traceToMixed K y.snd)) : ℂ) *
          F ((traceJointToMixed K).symm z) := by
  rw [integral_eq_inv_jacobian_traceJointToMixed,
    traceJointFourierCLM_eq_trace_integral]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [ContinuousLinearEquiv.symm_apply_apply]
    change _ = (standardMixedAddCharacter K (-(
      traceToMixed K x.fst * traceToMixed K y.fst +
      traceToMixed K x.snd * traceToMixed K y.snd)) : ℂ) * F x
    rw [standardMixedAddCharacter_apply, map_neg (Algebra.trace ℝ M∞),
      map_add (Algebra.trace ℝ M∞)]

/-- The Fourier operator accepts the actual cutoff on the max-norm product,
by transporting it to `WithLp 2` before applying Fourier transformation. -/
def traceJointProductFourierCLM :
    SchwartzMap (V × V) ℂ →L[ℂ] SchwartzMap W ℂ :=
  (traceJointFourierCLM K).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (traceJointToProduct K))

@[simp] theorem traceJointProductFourierCLM_apply (F : SchwartzMap (V × V) ℂ) :
    traceJointProductFourierCLM K F = traceJointFourierCLM K
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (traceJointToProduct K) F) := rfl

/-- Genuine operator continuity supplies a finite input seminorm bound. -/
theorem traceJointProductFourier_real_seminorm_bound (k n : ℕ) :
    ∃ t : Finset (ℕ × ℕ), ∃ D : ℝ≥0, D ≠ 0 ∧
      ∀ F : SchwartzMap (V × V) ℂ,
        SchwartzMap.seminorm ℝ k n (traceJointProductFourierCLM K F) ≤
          (D : ℝ) * t.sup (schwartzSeminormFamily ℝ (V × V) ℂ) F := by
  let T := (traceJointProductFourierCLM K).restrictScalars ℝ
  let q : Seminorm ℝ (SchwartzMap (V × V) ℂ) :=
    (SchwartzMap.seminorm ℝ k n).comp T.toLinearMap
  have hp := schwartz_withSeminorms ℝ (V × V) ℂ
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℝ W ℂ).continuous_seminorm (k, n)).comp T.continuous
  obtain ⟨t, D, hD, hbound⟩ := Seminorm.bound_of_continuous hp q hq
  refine ⟨t, D, hD, fun F => ?_⟩
  have hF := Seminorm.le_def.mp hbound F
  change SchwartzMap.seminorm ℝ k n (traceJointProductFourierCLM K F) ≤
    (D : ℝ) * t.sup (schwartzSeminormFamily ℝ (V × V) ℂ) F at hF
  exact hF

private theorem traceOriginalSeminorms_mono {s t : Finset (ℕ × ℕ)}
    (hst : s ⊆ t) (φ : SchwartzMap V ℂ) :
    s.sup (schwartzSeminormFamily ℝ V ℂ) φ ≤
      t.sup (schwartzSeminormFamily ℝ V ℂ) φ :=
  Seminorm.finset_sup_apply_le (apply_nonneg _ φ)
    (fun i hi => Seminorm.le_finset_sup_apply (hst hi))

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "Ω" => Set.prod (traceArchRegular K) (traceArchRegular K)
local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

include Γ in
/-- Finite aggregation of proved cutoff bounds. In particular the finite set
of Fourier input seminorms need not have a rectangular shape. -/
theorem exists_traceCutoffOrbitalSchwartz_finite_seminorm_power_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupport : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ Lattice < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
      ∀ i ∈ t,
        SchwartzMap.seminorm ℝ i.1 i.2
          (traceCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) := by
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, 0, 1, le_rfl, le_rfl, by simp⟩
  | @insert a t _hat ih =>
    obtain ⟨st, Ct, Rt, hCt, _hRt, ht⟩ := ih
    obtain ⟨sa, Ca, Ra, hCa, hRa, ha⟩ :=
      exists_traceCutoffOrbitalSchwartz_seminorm_power_bound
        K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ B M hM hOrder a.1 a.2
    refine ⟨sa ∪ st, Ca + Ct, max Ra Rt, add_nonneg hCa hCt,
      hRa.trans (le_max_left _ _), fun φ R hR i hi => ?_⟩
    have hpower : 0 ≤ R.val ^ (-B) := Real.rpow_nonneg R.property.le _
    have hsa := traceOriginalSeminorms_mono K (s := sa) (t := sa ∪ st)
      Finset.subset_union_left φ
    have hst := traceOriginalSeminorms_mono K (s := st) (t := sa ∪ st)
      Finset.subset_union_right φ
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      calc
        _ ≤ Ca * sa.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) :=
          ha φ R ((le_max_left _ _).trans hR) a.2 le_rfl
        _ ≤ (Ca + Ct) * (sa ∪ st).sup (schwartzSeminormFamily ℝ V ℂ) φ *
            R.val ^ (-B) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (le_add_of_nonneg_right hCt) hsa
              (apply_nonneg _ _) (add_nonneg hCa hCt)) hpower
    · calc
        _ ≤ Ct * st.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) :=
          ht φ R ((le_max_right _ _).trans hR) i hi
        _ ≤ (Ca + Ct) * (sa ∪ st).sup (schwartzSeminormFamily ℝ V ℂ) φ *
            R.val ^ (-B) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (le_add_of_nonneg_left hCa) hst
              (apply_nonneg _ _) (add_nonneg hCa hCt)) hpower

include Γ in
/-- The Fourier transform of the actual fixed-cutoff orbital kernel has
uniform decay in R in every Schwartz seminorm. All constants, finite original
test-function seminorms, and the threshold precede φ and R in the quantifiers. -/
theorem exists_traceCutoffOrbitalFourier_seminorm_power_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupport : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ Lattice < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
        SchwartzMap.seminorm ℝ k n (traceJointProductFourierCLM K
          (traceCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ φ R)) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) := by
  obtain ⟨t, D, _hD, hFourier⟩ := traceJointProductFourier_real_seminorm_bound K k n
  obtain ⟨s, C, R0, hC, hR0, hcutoff⟩ :=
    exists_traceCutoffOrbitalSchwartz_finite_seminorm_power_bound
      K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ B M hM hOrder t
  refine ⟨s, (D : ℝ) * C, R0, mul_nonneg (NNReal.coe_nonneg D) hC,
    hR0, fun φ R hR => ?_⟩
  have hnonneg : 0 ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) :=
    mul_nonneg (mul_nonneg hC (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le _)
  have hsup := Seminorm.finset_sup_apply_le hnonneg (hcutoff φ R hR)
  calc
    _ ≤ (D : ℝ) * t.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
        (traceCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ φ R) :=
      hFourier _
    _ ≤ (D : ℝ) * (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B)) :=
      mul_le_mul_of_nonneg_left hsup (NNReal.coe_nonneg D)
    _ = ((D : ℝ) * C) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) := by ring

end HeckeGeneral.Analysis
