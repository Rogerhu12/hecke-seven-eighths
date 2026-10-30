import HeckeGeneral.Arithmetic.SIntegerMovingPeriodClassScalar
import HeckeGeneral.Arithmetic.IdealLatticeQuotient
import HeckeGeneral.Arithmetic.ArchimedeanUnitShape
import HeckeGeneral.Arithmetic.SUnitArchimedeanBalancing

/-! Actual class-scalar transport for the moving period.
The full class group and original subgroup pullback are retained. No
uniformity of the unnormalized moving lattice is asserted. -/

noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField IsDedekindDomain HeckeGeneral.Analysis
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

private theorem scalar_normAtPlace_ne_zero (x : K) (hx : x ≠ 0)
    (w : InfinitePlace K) :
    mixedEmbedding.normAtPlace w (mixedEmbedding K x) ≠ 0 := by
  rw [mixedEmbedding.normAtPlace_apply]
  exact (map_ne_zero w).mpr hx

private theorem traceCoordinateMul_traceEmbedding (x y : K) (hx : x ≠ 0) :
    traceCoordinateMulEquiv K (mixedEmbedding K x)
      (scalar_normAtPlace_ne_zero K x hx) (traceEmbedding K y) =
        traceEmbedding K (x * y) := by
  apply (traceToMixed K).injective
  simp only [traceCoordinateMulEquiv, ContinuousLinearEquiv.trans_apply,
    traceEmbedding, ContinuousLinearEquiv.apply_symm_apply,
    mixedCoordinateMulEquiv_apply]
  exact (map_mul (mixedEmbedding K) x y).symm

/-- Literal transport of an ideal scalar equality, with the actual trace
coordinate multiplication and its inverse pullback image lattice. -/
theorem traceIdealLattice_of_scalar_eq
    (I J : (Ideal (𝓞 K))⁰) (x : K) (hx : x ≠ 0)
    (hIJ : FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
        (I.val : FractionalIdeal (𝓞 K)⁰ K) =
          (J.val : FractionalIdeal (𝓞 K)⁰ K)) :
    traceIdealLattice K (integralIdealUnit K J) =
      imageLattice (traceIdealLattice K (integralIdealUnit K I))
        (traceCoordinateMulEquiv K (mixedEmbedding K x)
          (scalar_normAtPlace_ne_zero K x hx)) := by
  let e := traceCoordinateMulEquiv K (mixedEmbedding K x)
    (scalar_normAtPlace_ne_zero K x hx)
  ext z
  change z ∈ traceIdealLattice K (integralIdealUnit K J) ↔
    e.symm z ∈ traceIdealLattice K (integralIdealUnit K I)
  constructor
  · intro hz
    obtain ⟨y, hy, hzy⟩ := exists_traceEmbedding_eq_of_mem_traceIdealLattice K _ hz
    change y ∈ (J.val : FractionalIdeal (𝓞 K)⁰ K) at hy
    rw [← hIJ, FractionalIdeal.mem_singleton_mul] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    have het : e (traceEmbedding K t) = z := by
      rw [show e (traceEmbedding K t) = traceEmbedding K (x * t) from
        traceCoordinateMul_traceEmbedding K x t hx]
      exact hzy
    rw [← het, ContinuousLinearEquiv.symm_apply_apply]
    exact (traceEmbedding_mem_traceIdealLattice K _).mpr ht
  · intro hz
    obtain ⟨t, ht, hzt⟩ := exists_traceEmbedding_eq_of_mem_traceIdealLattice K _ hz
    have hy : x * t ∈ (J.val : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← hIJ, FractionalIdeal.mem_singleton_mul]
      exact ⟨t, ht, rfl⟩
    have hez : traceEmbedding K (x * t) = z := by
      rw [← traceCoordinateMul_traceEmbedding K x t hx]
      change e (traceEmbedding K t) = z
      rw [hzt, ContinuousLinearEquiv.apply_symm_apply]
    rw [← hez]
    exact (traceEmbedding_mem_traceIdealLattice K _).mpr hy

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (M : (Ideal (𝓞 K))⁰)

/-- Every actual moving period lattice is the actual trace-multiplication
image of one fixed class lattice. Neither principalization nor a chosen
single class sector is assumed. -/
theorem exists_movingPeriod_trace_image
    (c : NonzeroRingElements (S.integer K)) :
    ∃ q : ClassGroup (𝓞 K), ∃ x : K, ∃ hx : x ≠ 0,
      traceIdealLattice K (integralIdealUnit K (sIntegerMovingPeriod K S M c)) =
        imageLattice (traceIdealLattice K (integralIdealUnit K (periodClassRepresentative K q)))
          (traceCoordinateMulEquiv K (mixedEmbedding K x)
            (scalar_normAtPlace_ne_zero K x hx)) := by
  obtain ⟨q, x, hx, heq⟩ := exists_movingPeriod_class_scalar K S M c
  exact ⟨q, x, hx, traceIdealLattice_of_scalar_eq K _ _ x hx heq⟩

/-- The scalar of the actual moving period can be balanced by an ordinary
unit lying in the pullback of the original subgroup. The correcting unit
is retained explicitly; it has not yet been erased from the lattice map. -/
theorem exists_movingPeriod_trace_image_and_subgroup_balance
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (c : NonzeroRingElements (S.integer K)) :
    ∃ q : ClassGroup (𝓞 K), ∃ x : K, ∃ hx : x ≠ 0,
      ∃ u : ordinaryUnitPullback K S Γ,
      ∃ z : FiniteIndexArchShape K (ordinaryUnitPullback K S Γ),
        z.val = (arithmeticNormRoot K (mixedEmbedding K x))⁻¹ •
          ((u : (𝓞 K)ˣ) • mixedEmbedding K x) ∧
        traceIdealLattice K (integralIdealUnit K (sIntegerMovingPeriod K S M c)) =
          imageLattice (traceIdealLattice K (integralIdealUnit K (periodClassRepresentative K q)))
            (traceCoordinateMulEquiv K (mixedEmbedding K x)
              (scalar_normAtPlace_ne_zero K x hx)) := by
  obtain ⟨q, x, hx, hlat⟩ := exists_movingPeriod_trace_image K S M c
  have hn : mixedEmbedding.norm (mixedEmbedding K x) ≠ 0 :=
    mixedEmbedding.norm_ne_zero_iff.mpr (scalar_normAtPlace_ne_zero K x hx)
  obtain ⟨u, hu⟩ := exists_subgroup_unit_normalize_mem K
    (ordinaryUnitPullback K S Γ) hn
  exact ⟨q, x, hx, u, ⟨_, hu⟩, rfl, hlat⟩

/-- The actual original-subgroup compact shape has bounded inverse operator
norm. This chooses B before any moving period or scalar is selected. -/
theorem exists_originalSubgroup_shape_inverse_bound
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex] :
    ∃ B : ℝ, 0 < B ∧ ∀ z : FiniteIndexArchShape K (ordinaryUnitPullback K S Γ),
      ‖(traceCoordinateMulEquiv K z
        (mixedEmbedding.norm_ne_zero_iff.mp (show mixedEmbedding.norm z.val ≠ 0 by
          rw [norm_eq_one_of_mem_finiteIndexBalancedShape K _ z.property]
          exact one_ne_zero))).symm.toContinuousLinearMap‖ ≤ B := by
  let Δ := ordinaryUnitPullback K S Γ
  let T := FiniteIndexArchShape K Δ
  let hn : ∀ z : T, mixedEmbedding.norm z.val ≠ 0 := fun z => by
    rw [norm_eq_one_of_mem_finiteIndexBalancedShape K Δ z.property]
    exact one_ne_zero
  let e : T → mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ]
      mixedEmbedding.euclidean.mixedSpace K := fun z =>
    traceCoordinateMulEquiv K z (mixedEmbedding.norm_ne_zero_iff.mp (hn z))
  have hc : Continuous (fun z : T => (e z).symm.toContinuousLinearMap) :=
    continuous_traceCoordinateMulEquiv_inverseCLM K Subtype.val continuous_subtype_val
      (fun z => mixedEmbedding.norm_ne_zero_iff.mp (hn z))
  have hcompact : IsCompact (Set.univ : Set T) :=
    isCompact_iff_isCompact_univ.mp (isCompact_finiteIndexBalancedShape K Δ)
  obtain ⟨B, hB, hb⟩ := (hcompact.image hc).isBounded.exists_pos_norm_le
  exact ⟨B, hB, fun z => hb _ (Set.mem_image_of_mem _ (Set.mem_univ z))⟩

end HeckeGeneral.Arithmetic
