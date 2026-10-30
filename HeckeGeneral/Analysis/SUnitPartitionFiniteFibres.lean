import HeckeGeneral.Analysis.SUnitAnnularPartitionCutoff

/-! The archimedean partition depends on a finite unit coordinate only
through its valuations. On the actual finite valuation box this gives a
finite family of archimedean cutoffs, indexed by the original box. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

theorem localUnit_norm_eq_of_order_eq (v : HeightOneSpectrum (𝓞 K))
    (x y : (v.adicCompletion K)ˣ)
    (h : localOrderHom K v x = localOrderHom K v y) :
    ‖x.val‖ = ‖y.val‖ := by
  have hv : (Valued.v x.val : WithZero (Multiplicative ℤ)) = Valued.v y.val := by
    rw [localOrder_valuation, localOrder_valuation, h]
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, hv]

theorem sFiniteProductNorm_eq_of_orders_eq
    (ζ ξ : (v : S) → (v.val.adicCompletion K)ˣ)
    (h : ∀ v, localOrderHom K v.val (ζ v) = localOrderHom K v.val (ξ v)) :
    sFiniteProductNorm K S ζ = sFiniteProductNorm K S ξ := by
  apply Finset.prod_congr rfl
  intro v _
  exact localUnit_norm_eq_of_order_eq K v.val (ζ v) (ξ v) (h v)

theorem sUnitFinitePartitionCutoff_eq_of_orders_eq (H : ℕ)
    (ζ ξ : (v : S) → (v.val.adicCompletion K)ˣ)
    (h : ∀ v, localOrderHom K v.val (ζ v) = localOrderHom K v.val (ξ v)) :
    sUnitFinitePartitionCutoff K S H ζ = sUnitFinitePartitionCutoff K S H ξ := by
  have hmem : ζ ∈ finiteLocalValuationBox K S H ↔
      ξ ∈ finiteLocalValuationBox K S H := by
    apply forall_congr'
    intro v
    rw [mem_localValuationBox_iff_order_bounds, mem_localValuationBox_iff_order_bounds, h v]
  simp only [sUnitFinitePartitionCutoff_apply, hmem]

theorem sUnitPartitionFibreScale_eq_of_orders_eq
    (ζ ξ : (v : S) → (v.val.adicCompletion K)ˣ)
    (h : ∀ v, localOrderHom K v.val (ζ v) = localOrderHom K v.val (ξ v)) (z : V) :
    sUnitPartitionFibreScale K S ζ z = sUnitPartitionFibreScale K S ξ z := by
  rw [sUnitPartitionFibreScale, sUnitPartitionFibreScale,
    sFiniteProductNorm_eq_of_orders_eq K S ζ ξ h]

variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

theorem sUnitPartitionFibreBaseTerm_eq_of_orders_eq
    (ζ ξ : (v : S) → (v.val.adicCompletion K)ˣ)
    (h : ∀ v, localOrderHom K v.val (ζ v) = localOrderHom K v.val (ξ v))
    (u : Γ) (z : V) :
    sUnitPartitionFibreBaseTerm K S Γ ζ u z =
      sUnitPartitionFibreBaseTerm K S Γ ξ u z := by
  unfold sUnitPartitionFibreBaseTerm
  rw [sUnitPartitionFibreScale_eq_of_orders_eq K S ζ ξ h]
  congr 1
  apply sUnitFinitePartitionCutoff_eq_of_orders_eq
  intro v
  change localOrderHom K v.val (_ * ζ v) = localOrderHom K v.val (_ * ξ v)
  simp only [map_mul, h v]

theorem sUnitPartitionFibrePeriod_eq_of_orders_eq
    (ζ ξ : (v : S) → (v.val.adicCompletion K)ˣ)
    (h : ∀ v, localOrderHom K v.val (ζ v) = localOrderHom K v.val (ξ v)) (z : V) :
    sUnitPartitionFibrePeriod K S Γ ζ z = sUnitPartitionFibrePeriod K S Γ ξ z := by
  apply tsum_congr
  intro u
  exact sUnitPartitionFibreBaseTerm_eq_of_orders_eq K S Γ ζ ξ h u z

theorem sUnitNormalizedPartitionArchFibre_eq_of_orders_eq
    (ζ ξ : (v : S) → (v.val.adicCompletion K)ˣ)
    (h : ∀ v, localOrderHom K v.val (ζ v) = localOrderHom K v.val (ξ v)) (z : V) :
    sUnitNormalizedPartitionArchFibre K S Γ ζ z =
      sUnitNormalizedPartitionArchFibre K S Γ ξ z := by
  rw [sUnitNormalizedPartitionArchFibre, sUnitNormalizedPartitionArchFibre,
    sUnitPartitionFibreBaseTerm_eq_of_orders_eq K S Γ ζ ξ h,
    sUnitPartitionFibrePeriod_eq_of_orders_eq K S Γ ζ ξ h]

theorem sUnitNormalizedPartitionArchPullback_eq_of_orders_eq
    (ζ ξ : (v : S) → (v.val.adicCompletion K)ˣ)
    (h : ∀ v, localOrderHom K v.val (ζ v) = localOrderHom K v.val (ξ v)) (z : V) :
    sUnitNormalizedPartitionArchPullback K S Γ ζ z =
      sUnitNormalizedPartitionArchPullback K S Γ ξ z := by
  unfold sUnitNormalizedPartitionArchPullback
  split_ifs with hz
  · rw [← sUnitNormalizedPartitionArchFibre_eq_actual K S Γ ζ ⟨z, hz⟩,
      ← sUnitNormalizedPartitionArchFibre_eq_actual K S Γ ξ ⟨z, hz⟩]
    exact sUnitNormalizedPartitionArchFibre_eq_of_orders_eq K S Γ ζ ξ h z
  · rfl

theorem sUnitAnnularPartitionCutoff_eq_of_orders_eq (a : ℝ → ℝ)
    (ζ ξ : (v : S) → (v.val.adicCompletion K)ˣ)
    (h : ∀ v, localOrderHom K v.val (ζ v) = localOrderHom K v.val (ξ v)) :
    sUnitAnnularPartitionCutoff K S Γ a ζ = sUnitAnnularPartitionCutoff K S Γ a ξ := by
  funext z
  rw [sUnitAnnularPartitionCutoff, sUnitAnnularPartitionCutoff,
    sFiniteProductNorm_eq_of_orders_eq K S ζ ξ h,
    sUnitNormalizedPartitionArchPullback_eq_of_orders_eq K S Γ ζ ξ h]

/-- The representatives use the same uniformizers and valuation signs as
the finite box, with no enlargement of the subgroup or support. -/
def sUnitPartitionFiniteFibreRepresentative (H : ℕ) (e : S → Fin H) :
    (v : S) → (v.val.adicCompletion K)ˣ :=
  fun v => localUniformizerUnit K v.val ^ (-(e v).val : ℤ)

theorem exists_sUnitPartitionFiniteFibreRepresentative (H : ℕ)
    (ζ : (v : S) → (v.val.adicCompletion K)ˣ)
    (hζ : ζ ∈ finiteLocalValuationBox K S H) :
    ∃ e : S → Fin H, ∀ v,
      localOrderHom K v.val (ζ v) =
        localOrderHom K v.val (sUnitPartitionFiniteFibreRepresentative K S H e v) := by
  have hex : ∀ v : S, ∃ e : Fin H,
      localOrderHom K v.val (ζ v) =
        localOrderHom K v.val (localUniformizerUnit K v.val ^ (-(e.val : ℤ))) := by
    intro v
    obtain ⟨e, u, hu⟩ := Set.mem_iUnion.mp (hζ v)
    refine ⟨e, ?_⟩
    rw [← hu, map_mul, localOrder_integralUnit, one_mul]
  choose e he using hex
  exact ⟨e, he⟩

/-- All actual finite coordinates in the compact valuation box give one
of finitely many archimedean functions. No representative is discarded. -/
theorem finite_sUnitAnnularPartitionCutoff_fibres (a : ℝ → ℝ) (H : ℕ) :
    Set.Finite ((fun ζ : (v : S) → (v.val.adicCompletion K)ˣ =>
      sUnitAnnularPartitionCutoff K S Γ a ζ) '' finiteLocalValuationBox K S H) := by
  apply (Set.finite_range (fun e : S → Fin H => sUnitAnnularPartitionCutoff K S Γ a
    (sUnitPartitionFiniteFibreRepresentative K S H e))).subset
  rintro f ⟨ζ, hζ, rfl⟩
  obtain ⟨e, he⟩ := exists_sUnitPartitionFiniteFibreRepresentative K S H ζ hζ
  exact ⟨e, (sUnitAnnularPartitionCutoff_eq_of_orders_eq K S Γ a ζ _ he).symm⟩

/-- The finite coordinate is unchanged by radial normalization. Outside
the original box the actual numerator vanishes, so the cutoff is zero. -/
theorem sUnitAnnularPartitionCutoff_eq_zero_of_not_mem_box (a : ℝ → ℝ)
    (ζ : (v : S) → (v.val.adicCompletion K)ˣ)
    (hζ : ζ ∉ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    sUnitAnnularPartitionCutoff K S Γ a ζ = 0 := by
  funext z
  have hfinite : sUnitFinitePartitionCutoff K S (finiteIndexSUnitBoxWidth K S Γ) ζ = 0 := by
    rw [sUnitFinitePartitionCutoff_apply, if_neg hζ]
  by_cases hz : z ∈ traceArchRegular K
  · have hbase : sUnitPartitionBase K S Γ
        (sUnitPartitionFibreNormalize K S ζ ⟨z, hz⟩) = 0 := by
      unfold sUnitPartitionBase sUnitPartitionNumerator
      rw [sUnitPartitionFibreNormalize_finite, hfinite, mul_zero]
    simp only [sUnitAnnularPartitionCutoff, sUnitNormalizedPartitionArchPullback,
      dif_pos hz, sUnitNormalizedPartition, hbase, zero_div, mul_zero, Pi.zero_apply]
  · simp only [sUnitAnnularPartitionCutoff, sUnitNormalizedPartitionArchPullback,
      dif_neg hz, mul_zero, Pi.zero_apply]

/-- The complete finite-coordinate family is finite, including the zero
function off the box. This does not restrict an orbit to one finite fibre. -/
theorem finite_range_sUnitAnnularPartitionCutoff (a : ℝ → ℝ) :
    Set.Finite (Set.range (sUnitAnnularPartitionCutoff K S Γ a)) := by
  apply ((finite_sUnitAnnularPartitionCutoff_fibres K S Γ a
    (finiteIndexSUnitBoxWidth K S Γ)).insert 0).subset
  rintro f ⟨ζ, rfl⟩
  by_cases hζ : ζ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)
  · exact Set.mem_insert_of_mem _ ⟨ζ, hζ, rfl⟩
  · exact Set.mem_insert_iff.mpr (Or.inl
      (sUnitAnnularPartitionCutoff_eq_zero_of_not_mem_box K S Γ a ζ hζ))

end HeckeGeneral.Analysis
