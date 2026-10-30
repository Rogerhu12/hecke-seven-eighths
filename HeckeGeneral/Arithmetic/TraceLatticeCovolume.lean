import HeckeGeneral.Arithmetic.IdealTraceLattice

/-!
The trace-normalized ideal lattice uses a factor `sqrt 2` in every complex
coordinate. Its covolume therefore differs from the unweighted mixed embedding.
The change of volume below is computed from the actual real determinant.
-/

noncomputable section

open MeasureTheory Module ZSpan NumberField NumberField.InfinitePlace Classical
open scoped nonZeroDivisors

namespace HeckeGeneral.Arithmetic

/-- Change of covolume under a real linear coordinate change. -/
theorem covolume_comap_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (e : E ≃L[ℝ] E) (μ : Measure E) [μ.IsAddHaarMeasure] :
    ZLattice.covolume (ZLattice.comap ℝ L e.toLinearMap) μ =
      |LinearMap.det e.symm.toLinearMap| * ZLattice.covolume L μ := by
  classical
  let b := Free.chooseBasis ℤ L
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ μ
      (ZLattice.isAddFundamentalDomain (b.ofZLatticeComap ℝ L e.toLinearEquiv) μ),
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ)]
  have hset : fundamentalDomain
      ((b.ofZLatticeComap ℝ L e.toLinearEquiv).ofZLatticeBasis ℝ) =
      e ⁻¹' fundamentalDomain (b.ofZLatticeBasis ℝ) := by
    rw [← e.image_symm_eq_preimage, ← e.symm.coe_toLinearEquiv,
      map_fundamentalDomain]
    rw [Basis.ofZLatticeBasis_comap]
  rw [measureReal_def, hset, Measure.addHaar_preimage_continuousLinearEquiv,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

variable (K : Type*) [Field K] [NumberField K]

/-- The mixed-space coordinate change which leaves real coordinates fixed and
divides the complex coordinates by `sqrt 2`. -/
def traceMixedUnscale : mixedEmbedding.mixedSpace K ≃L[ℝ] mixedEmbedding.mixedSpace K :=
  (ContinuousLinearEquiv.refl ℝ
    ({w : InfinitePlace K // IsReal w} → ℝ)).prodCongr (unscaleComplexCoordinates K)

theorem det_traceMixedUnscale_symm :
    LinearMap.det (traceMixedUnscale K).symm.toLinearMap =
      (2 : ℝ) ^ nrComplexPlaces K := by
  classical
  have hmap : (traceMixedUnscale K).symm.toLinearMap =
      LinearMap.prodMap (LinearMap.id :
        ({w : InfinitePlace K // IsReal w} → ℝ) →ₗ[ℝ] _) 
        ((Real.sqrt 2) • (LinearMap.id :
          ({w : InfinitePlace K // IsComplex w} → ℂ) →ₗ[ℝ] _)) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · funext w
      simp [traceMixedUnscale, unscaleComplexCoordinates]
  rw [hmap, LinearMap.det_prodMap, LinearMap.det_id, one_mul,
    LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [show Fintype.card {w : InfinitePlace K // IsComplex w} = nrComplexPlaces K from rfl,
    mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The covolume for the trace-normalized Euclidean lattice. In particular the
complex-place factor `2^(-r₂)` of the unweighted embedding cancels exactly. -/
theorem covolume_traceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (traceIdealLattice K I) =
      FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) * √|discr K| := by
  classical
  have hL : traceIdealLattice K I = ZLattice.comap ℝ
      (ZLattice.comap ℝ (mixedEmbedding.idealLattice K I)
        (traceMixedUnscale K).toLinearMap)
      (mixedEmbedding.euclidean.toMixed K).toLinearMap := by
    rw [ZLattice.comap_comp]
    rfl
  rw [hL, ZLattice.covolume_comap _ volume volume
      (mixedEmbedding.euclidean.volumePreserving_toMixed K),
    covolume_comap_det, det_traceMixedUnscale_symm,
    abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _),
    mixedEmbedding.covolume_idealLattice]
  have hcancel : (2 : ℝ) ^ nrComplexPlaces K * (2⁻¹) ^ nrComplexPlaces K = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (2 : ℝ) ^ nrComplexPlaces K *
        (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) *
          (2⁻¹) ^ nrComplexPlaces K * √|discr K|) =
        FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) *
          ((2 : ℝ) ^ nrComplexPlaces K * (2⁻¹) ^ nrComplexPlaces K) * √|discr K| := by ring
    _ = _ := by rw [hcancel, mul_one]

end HeckeGeneral.Arithmetic
