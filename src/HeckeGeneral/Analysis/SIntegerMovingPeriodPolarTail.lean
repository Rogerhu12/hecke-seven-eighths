import HeckeGeneral.Arithmetic.SIntegerMovingPeriodNormScale
import HeckeGeneral.Analysis.SUnitTotalNormLatticeFourierBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Actual polar transport and moving-period mass/tail.
The inverse polar operator is controlled by the FORWARD primal operator.
Only the single origin is omitted; no nonzero-coordinate restriction occurs.
This does not establish coefficient periodicity or a product correlation bound. -/

noncomputable section
namespace HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic NumberField
open scoped Classical nonZeroDivisors

section Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual inverse-adjoint map, rather than a supplied polar shape. -/
def movingPeriodPolarEquiv (e : E ≃L[ℝ] E) : E ≃L[ℝ] E where
  toLinearEquiv :=
    { toFun := ContinuousLinearMap.adjoint e.symm.toContinuousLinearMap
      invFun := ContinuousLinearMap.adjoint e.toContinuousLinearMap
      left_inv := by
        intro x
        apply ext_inner_right ℝ
        intro y
        rw [ContinuousLinearMap.adjoint_inner_left,
          ContinuousLinearMap.adjoint_inner_left]
        simp
      right_inv := by
        intro x
        apply ext_inner_right ℝ
        intro y
        rw [ContinuousLinearMap.adjoint_inner_left,
          ContinuousLinearMap.adjoint_inner_left]
        simp
      map_add' := (ContinuousLinearMap.adjoint e.symm.toContinuousLinearMap).map_add
      map_smul' := (ContinuousLinearMap.adjoint e.symm.toContinuousLinearMap).map_smul }
  continuous_toFun := (ContinuousLinearMap.adjoint e.symm.toContinuousLinearMap).continuous
  continuous_invFun := (ContinuousLinearMap.adjoint e.toContinuousLinearMap).continuous

theorem movingPeriodPolarEquiv_inverse_norm (e : E ≃L[ℝ] E) :
    ‖(movingPeriodPolarEquiv e).symm.toContinuousLinearMap‖ = ‖e.toContinuousLinearMap‖ := by
  change ‖ContinuousLinearMap.adjoint e.toContinuousLinearMap‖ = _
  exact ContinuousLinearMap.adjoint.norm_map _

/-- Literal dual-lattice identity proved from the integral inner-product condition. -/
theorem dualLattice_image_movingPeriod (L : Submodule ℤ E) (e : E ≃L[ℝ] E) :
    dualLattice (imageLattice L e) = imageLattice (dualLattice L) (movingPeriodPolarEquiv e) := by
  ext x
  change (∀ y ∈ imageLattice L e, inner ℝ x y ∈ (1 : Submodule ℤ ℝ)) ↔
    ∀ y ∈ L, inner ℝ (ContinuousLinearMap.adjoint e.toContinuousLinearMap x) y ∈
      (1 : Submodule ℤ ℝ)
  constructor
  · intro hx y hy
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact hx (e y) (by change e.symm (e y) ∈ L; simpa using hy)
  · intro hx y hy
    have h := hx (e.symm y) hy
    simpa only [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using h

/-- Nonzero polar mass has the correct direction: forward primal size. -/
theorem movingPeriod_polar_mass_le (L : Submodule ℤ E)
    [DiscreteTopology (dualLattice L)] (e : E ≃L[ℝ] E) (p : ℕ)
    (hp : Module.finrank ℤ (dualLattice L) < p) {C : ℝ}
    (hC : ‖e.toContinuousLinearMap‖ ≤ C) :
    latticeInversePowerMass (dualLattice (imageLattice L e)) p ≤
      C ^ p * latticeInversePowerMass (dualLattice L) p := by
  rw [dualLattice_image_movingPeriod]
  exact latticeInversePowerMass_image_le (dualLattice L) (movingPeriodPolarEquiv e) p hp
    (by rw [movingPeriodPolarEquiv_inverse_norm]; exact hC)
/-- Origin separated before applying any inverse-power tail estimate.
For a product lattice, `m ≠ 0` includes `(m₁,0)` and `(0,m₂)` automatically. -/
theorem movingPeriod_polar_origin_split (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (F : SchwartzMap E ℂ) :
    (∑' m : dualLattice L, F (m : E)) = F 0 +
      ∑' m : dualLattice L, if m = 0 then 0 else F (m : E) := by
  have hs : Summable (fun m : dualLattice L => F (m : E)) := by
    simpa using (summable_norm_schwartz_lattice (dualLattice L) F 0).of_norm
  simpa using hs.tsum_eq_add_tsum_ite 0
end Polar

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Compactness supplies the missing FORWARD shape bound before any modulus. -/
theorem exists_movingPeriod_shape_forward_bound
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex] :
    ∃ C : ℝ, 0 < C ∧ ∀ z : FiniteIndexArchShape K (ordinaryUnitPullback K S Γ),
      ‖(traceCoordinateMulEquiv K z (movingPeriod_shape_nonzero K z)).toContinuousLinearMap‖ ≤ C := by
  let T := FiniteIndexArchShape K (ordinaryUnitPullback K S Γ)
  let e : T → mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ]
      mixedEmbedding.euclidean.mixedSpace K := fun z =>
    traceCoordinateMulEquiv K z (movingPeriod_shape_nonzero K z)
  have hc : Continuous (fun z : T => (e z).toContinuousLinearMap) := by
    have heq (z : T) : (e z).toContinuousLinearMap =
        (traceToMixed K).symm.toContinuousLinearMap.comp
          ((ContinuousLinearMap.mul ℝ (mixedEmbedding.mixedSpace K) z.val).comp
            (traceToMixed K).toContinuousLinearMap) := by
      ext v
      rfl
    simp_rw [heq]
    exact continuous_const.clm_comp
      (((ContinuousLinearMap.mul ℝ (mixedEmbedding.mixedSpace K)).continuous.comp
        continuous_subtype_val).clm_comp continuous_const)
  have hcompact : IsCompact (Set.univ : Set T) :=
    isCompact_iff_isCompact_univ.mp
      (isCompact_finiteIndexBalancedShape K (ordinaryUnitPullback K S Γ))
  obtain ⟨C, hC, hb⟩ := (hcompact.image hc).isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun z => hb _ (Set.mem_image_of_mem _ (Set.mem_univ z))⟩

/-- A real scale multiplies the forward bound by precisely rho. -/
theorem movingPeriod_scaled_forward_bound
    (e : mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ]
      mixedEmbedding.euclidean.mixedSpace K)
    (ρ C : ℝ) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (he : ‖e.toContinuousLinearMap‖ ≤ C) :
    ‖(e.trans (tracePositiveScalarEquiv K ρ hρ)).toContinuousLinearMap‖ ≤ ρ * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hρ.le hC)
  intro v
  change ‖ρ • e v‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg hρ.le]
  exact (mul_le_mul_of_nonneg_left (e.toContinuousLinearMap.le_of_opNorm_le he v) hρ.le).trans_eq
    (by ring)

variable (M : (Ideal (𝓞 K))⁰)

/-- Actual moving periods, with the SAME scalar/class/shape witnesses and
exact norm scale. The exponent p exceeds the ordinary polar lattice rank.
The bound grows as rho^p because the moving polar lattice shrinks as rho grows. -/
theorem exists_uniform_movingPeriod_polar_mass
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (p : ℕ) (hp : Module.finrank ℚ K < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : NonzeroRingElements (S.integer K),
      ∃ q : ClassGroup (𝓞 K), ∃ x : K, ∃ hx : x ≠ 0,
      ∃ u : ordinaryUnitPullback K S Γ,
      ∃ z : FiniteIndexArchShape K (ordinaryUnitPullback K S Γ),
      ∃ hρ : 0 < arithmeticNormRoot K (mixedEmbedding K x),
        FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
          ((periodClassRepresentative K q).val : FractionalIdeal (𝓞 K)⁰ K) =
            ((sIntegerMovingPeriod K S M c).val : FractionalIdeal (𝓞 K)⁰ K) ∧
        z.val = (arithmeticNormRoot K (mixedEmbedding K x))⁻¹ •
          ((u : (𝓞 K)ˣ) • mixedEmbedding K x) ∧
        arithmeticNormRoot K (mixedEmbedding K x) ^ Module.finrank ℚ K =
          (Ideal.absNorm (sIntegerMovingPeriod K S M c).val : ℝ) /
            (Ideal.absNorm (periodClassRepresentative K q).val : ℝ) ∧
        latticeInversePowerMass
          (dualLattice (traceIdealLattice K (integralIdealUnit K (sIntegerMovingPeriod K S M c)))) p ≤
          (arithmeticNormRoot K (mixedEmbedding K x) * C) ^ p *
            latticeInversePowerMass
              (dualLattice (traceIdealLattice K (integralIdealUnit K (periodClassRepresentative K q)))) p := by
  obtain ⟨C, hC, hforward⟩ := exists_movingPeriod_shape_forward_bound K S Γ
  obtain ⟨B, hB, hshape⟩ := exists_uniform_movingPeriod_scaled_shape_with_norm_scale K S M Γ
  refine ⟨C, hC, fun c => ?_⟩
  obtain ⟨q, x, hx, u, z, hρ, hclass, hz, hbound, hlat, hnorm⟩ := hshape c
  refine ⟨q, x, hx, u, z, hρ, hclass, hz, hnorm, ?_⟩
  let L := traceIdealLattice K (integralIdealUnit K (periodClassRepresentative K q))
  let e := traceCoordinateMulEquiv K z (movingPeriod_shape_nonzero K z)
  let ρ := arithmeticNormRoot K (mixedEmbedding K x)
  have hrank : Module.finrank ℤ (dualLattice L) < p := by
    rw [ZLattice.rank ℝ (dualLattice L), mixedEmbedding.euclidean.finrank]
    exact hp
  have hmass := movingPeriod_polar_mass_le L
    (e.trans (tracePositiveScalarEquiv K ρ hρ)) p hrank
    (movingPeriod_scaled_forward_bound K e ρ C hρ hC.le (hforward z))
  have htrans : imageLattice L (e.trans (tracePositiveScalarEquiv K ρ hρ)) =
      imageLattice (imageLattice L e) (tracePositiveScalarEquiv K ρ hρ) := by
    ext v
    rfl
  rw [htrans] at hmass
  rw [hlat]
  exact hmass

/-- Uniform actual polar tails for arbitrary Schwartz kernels. The tail index
excludes exactly m=0. In a product-space application this convention retains
both axes; no origin estimate is inferred from the inverse-power majorant. -/
theorem exists_uniform_movingPeriod_polar_tail
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (p : ℕ) (hp : Module.finrank ℚ K < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : NonzeroRingElements (S.integer K),
      ∃ q : ClassGroup (𝓞 K), ∃ x : K, ∃ hx : x ≠ 0,
      ∃ u : ordinaryUnitPullback K S Γ,
      ∃ z : FiniteIndexArchShape K (ordinaryUnitPullback K S Γ),
      ∃ hρ : 0 < arithmeticNormRoot K (mixedEmbedding K x),
        FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
          ((periodClassRepresentative K q).val : FractionalIdeal (𝓞 K)⁰ K) =
            ((sIntegerMovingPeriod K S M c).val : FractionalIdeal (𝓞 K)⁰ K) ∧
        z.val = (arithmeticNormRoot K (mixedEmbedding K x))⁻¹ •
          ((u : (𝓞 K)ˣ) • mixedEmbedding K x) ∧
        arithmeticNormRoot K (mixedEmbedding K x) ^ Module.finrank ℚ K =
          (Ideal.absNorm (sIntegerMovingPeriod K S M c).val : ℝ) /
            (Ideal.absNorm (periodClassRepresentative K q).val : ℝ) ∧
        latticeInversePowerMass
          (dualLattice (traceIdealLattice K (integralIdealUnit K (sIntegerMovingPeriod K S M c)))) p ≤
          (arithmeticNormRoot K (mixedEmbedding K x) * C) ^ p *
            latticeInversePowerMass
              (dualLattice (traceIdealLattice K (integralIdealUnit K (periodClassRepresentative K q)))) p ∧
        ∀ F : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ,
        ∀ α : ℝ, 0 < α →
          let D := dualLattice (traceIdealLattice K
            (integralIdealUnit K (sIntegerMovingPeriod K S M c)))
          Summable (fun m : NonzeroLattice D => ‖F (α • ((m : D) : mixedEmbedding.euclidean.mixedSpace K))‖) ∧
          ‖∑' m : NonzeroLattice D, F (α • ((m : D) : mixedEmbedding.euclidean.mixedSpace K))‖ ≤
            SchwartzMap.seminorm ℂ p 0 F * α⁻¹ ^ p *
              ((arithmeticNormRoot K (mixedEmbedding K x) * C) ^ p *
                latticeInversePowerMass
                  (dualLattice (traceIdealLattice K (integralIdealUnit K (periodClassRepresentative K q)))) p) := by
  obtain ⟨C, hC, hm⟩ := exists_uniform_movingPeriod_polar_mass K S M Γ p hp
  refine ⟨C, hC, fun c => ?_⟩
  obtain ⟨q, x, hx, u, z, hρ, hclass, hz, hnorm, hmass⟩ := hm c
  refine ⟨q, x, hx, u, z, hρ, hclass, hz, hnorm, hmass, ?_⟩
  intro F α hα
  let D := dualLattice (traceIdealLattice K
    (integralIdealUnit K (sIntegerMovingPeriod K S M c)))
  have hrank : Module.finrank ℤ D < p := by
    rw [ZLattice.rank ℝ D, mixedEmbedding.euclidean.finrank]
    exact hp
  refine ⟨?_, ?_⟩
  · simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using
      summable_scaled_schwartz_derivative D F p 0 hrank hα
  · exact (norm_tsum_scaled_schwartz_le D F p hrank hα).trans
      (mul_le_mul_of_nonneg_left hmass (by positivity))

end HeckeGeneral.Analysis
