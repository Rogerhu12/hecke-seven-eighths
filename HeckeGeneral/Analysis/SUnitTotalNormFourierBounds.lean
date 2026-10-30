import HeckeGeneral.Analysis.SUnitMellinFourierBounds

/-! The literal total-norm radial parameter on each finite fibre. The
Fourier operator and its Haar normalization are unchanged: only the positive
profile parameter is reindexed. Compactness of the original valuation box
controls that reindexing uniformly, including for arbitrary real decay orders.
Outside the original box the actual annular cutoff, Schwartz map and Fourier
transform vanish. No fixed finite fibre is identified with a whole orbit. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Bridge
open scoped Classical ContDiff BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Z" => SFiniteLocalGroup K S
local notation "Regular" => traceArchRegular K

def sUnitTotalNormFibreFactor (ζ ξ : Z) : ℝ :=
  sFiniteProductNorm K S ζ * sFiniteProductNorm K S ξ

theorem sUnitTotalNormFibreFactor_pos (ζ ξ : Z) :
    0 < sUnitTotalNormFibreFactor K S ζ ξ :=
  mul_pos (sFiniteProductNorm_pos K S ζ) (sFiniteProductNorm_pos K S ξ)

/-- The archimedean-only kernel must be evaluated at this parameter when
R denotes the total S-local scale. This changes no vector-space variable. -/
def sUnitTotalNormRadius (ζ ξ : Z) (R : {r : ℝ // 0 < r}) : {r : ℝ // 0 < r} :=
  ⟨R.val / sUnitTotalNormFibreFactor K S ζ ξ,
    div_pos R.property (sUnitTotalNormFibreFactor_pos K S ζ ξ)⟩

/-- The literal radius divides by both actual total column norms. -/
theorem sUnitTotalNormRadius_profileRadius (ζ ξ : Z) (R : {r : ℝ // 0 < r})
    (x y : Regular) :
    (sUnitTotalNormRadius K S ζ ξ R).val /
        (traceArchProductNorm K x.val * traceArchProductNorm K y.val) =
      R.val / ((traceArchProductNorm K x.val * sFiniteProductNorm K S ζ) *
        (traceArchProductNorm K y.val * sFiniteProductNorm K S ξ)) := by
  have hx := (traceArchProductNorm_pos K x.property).ne'
  have hy := (traceArchProductNorm_pos K y.property).ne'
  have hζ := (sFiniteProductNorm_pos K S ζ).ne'
  have hξ := (sFiniteProductNorm_pos K S ξ).ne'
  change (R.val / (sFiniteProductNorm K S ζ * sFiniteProductNorm K S ξ)) / _ = _
  field_simp [hx, hy, hζ, hξ] <;> ring

variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]

/-- Identification with the genuine Fourier orbital profile, including its
norm-one Haar integral. Both finite norm factors occur in the radius. -/
theorem traceJointOrbitalKernel_totalNormRadius (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (ζ ξ : Z) (R : {r : ℝ // 0 < r}) (x y : Regular) :
    traceJointOrbitalKernel K S φ ψ (sUnitTotalNormRadius K S ζ ξ R) (x.val, y.val) =
      sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S (traceSchwartzFourier K φ) ψ)
        ⟨R.val / ((traceArchProductNorm K x.val * sFiniteProductNorm K S ζ) *
          (traceArchProductNorm K y.val * sFiniteProductNorm K S ξ)),
          div_pos R.property (mul_pos
            (mul_pos (traceArchProductNorm_pos K x.property) (sFiniteProductNorm_pos K S ζ))
            (mul_pos (traceArchProductNorm_pos K y.property) (sFiniteProductNorm_pos K S ξ)))⟩ := by
  let nx : {r : ℝ // 0 < r} := ⟨traceArchProductNorm K x.val,
    traceArchProductNorm_pos K x.property⟩
  let ny : {r : ℝ // 0 < r} := ⟨traceArchProductNorm K y.val,
    traceArchProductNorm_pos K y.property⟩
  have h := sUnitJointRadialProfile_at_logs K S φ ψ
    (sUnitTotalNormRadius K S ζ ξ R) nx ny 0
  change sUnitJointRadialProfile K S φ ψ (sUnitTotalNormRadius K S ζ ξ R) 0
    (Real.log nx.val, Real.log ny.val) = _
  rw [h, traceSchwartzEulerIterCLM_zero]
  congr 1
  apply Subtype.ext
  exact sUnitTotalNormRadius_profileRadius K S ζ ξ R x y

variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

def sUnitTotalNormAnnularPartitionJointSchwartz
    (ν : ℝ) (ζ ξ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    SchwartzMap (V × V) ℂ :=
  sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
    ψ hψ hψsupport ν ζ ξ φ (sUnitTotalNormRadius K S ζ ξ R)

theorem sUnitTotalNormAnnularPartitionJointSchwartz_apply
    (ν : ℝ) (ζ ξ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (p : V × V) :
    sUnitTotalNormAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν ζ ξ φ R p =
      sUnitMellinPhase K S ν ζ ξ p *
        (sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ p *
          traceJointOrbitalKernel K S φ ψ (sUnitTotalNormRadius K S ζ ξ R) p) :=
  sUnitMellinAnnularPartitionJointSchwartz_apply K S Γ a ha a0 b0 ha0 haSupport
    ψ hψ hψsupport ν ζ ξ φ (sUnitTotalNormRadius K S ζ ξ R) p

/-- The same actual two-column trace Fourier map, with both conjugations
and the same mixed Haar Jacobian; there is no new Jacobian factor. -/
def sUnitTotalNormAnnularPartitionJointFourier
    (ν : ℝ) (ζ ξ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    SchwartzMap (TraceJointEuclideanSpace K) ℂ :=
  traceJointProductFourierCLM K
    (sUnitTotalNormAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport ν ζ ξ φ R)

theorem sUnitTotalNormAnnularPartitionJointSchwartz_eq_zero_of_not_mem_box
    (ν : ℝ) (ζ ξ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
    (hout : ζ ∉ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) ∨
      ξ ∉ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    sUnitTotalNormAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport ν ζ ξ φ R = 0 := by
  ext p
  rw [sUnitTotalNormAnnularPartitionJointSchwartz_apply]
  have hzero : sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ p = 0 := by
    rcases hout with hζ | hξ
    · simp [sUnitAnnularPartitionJointCutoff,
        sUnitAnnularPartitionCutoff_eq_zero_of_not_mem_box K S Γ a ζ hζ]
    · simp [sUnitAnnularPartitionJointCutoff,
        sUnitAnnularPartitionCutoff_eq_zero_of_not_mem_box K S Γ a ξ hξ]
  simp [hzero]

theorem sUnitTotalNormAnnularPartitionJointFourier_eq_zero_of_not_mem_box
    (ν : ℝ) (ζ ξ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
    (hout : ζ ∉ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) ∨
      ξ ∉ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    sUnitTotalNormAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport ν ζ ξ φ R = 0 := by
  unfold sUnitTotalNormAnnularPartitionJointFourier
  rw [sUnitTotalNormAnnularPartitionJointSchwartz_eq_zero_of_not_mem_box K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport ν ζ ξ φ R hout, map_zero]

/-- A compact-box proof controls the actual finite norm factor itself,
not just the finite family of cutoff functions. Arbitrary real B is allowed. -/
private theorem exists_sUnitTotalNormFibreFactor_box_bounds (B : ℝ) :
    ∃ U T : ℝ, 1 ≤ U ∧ 1 ≤ T ∧ ∀ ζ ξ : Z,
      ζ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) →
      ξ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) →
      sUnitTotalNormFibreFactor K S ζ ξ ≤ U ∧
        sUnitTotalNormFibreFactor K S ζ ξ ^ B ≤ T := by
  let Q : Set (Z × Z) :=
    finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) ×ˢ
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)
  have hQ : IsCompact Q :=
    (isCompact_finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)).prod
      (isCompact_finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
  let F : Z × Z → ℝ := fun p => sUnitTotalNormFibreFactor K S p.1 p.2
  have hF : Continuous F :=
    ((continuous_sFiniteProductNorm K S).comp continuous_fst).mul
      ((continuous_sFiniteProductNorm K S).comp continuous_snd)
  have hFB : ContinuousOn (fun p => F p ^ B) Q :=
    hF.continuousOn.rpow_const (fun p _ => Or.inl
      (sUnitTotalNormFibreFactor_pos K S p.1 p.2).ne')
  obtain ⟨U, hU⟩ := hQ.bddAbove_image hF.continuousOn
  obtain ⟨T, hT⟩ := hQ.bddAbove_image hFB
  refine ⟨max 1 U, max 1 T, le_max_left _ _, le_max_left _ _, fun ζ ξ hζ hξ => ?_⟩
  have hp : (ζ, ξ) ∈ Q := ⟨hζ, hξ⟩
  exact ⟨(hU (Set.mem_image_of_mem F hp)).trans (le_max_right _ _),
    (hT (Set.mem_image_of_mem (fun p => F p ^ B) hp)).trans (le_max_right _ _)⟩

local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The total-norm kernel has one uniform Fourier estimate for all finite
fibres and moving Mellin heights. The finite original-input seminorms,
constant, threshold and height degree are chosen before ν, ζ, ξ, φ and R. -/
theorem exists_sUnitTotalNormAnnularPartitionJointFourier_seminorm_power_bound
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ Lattice < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, ∃ J : ℕ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ ν : ℝ, ∀ ζ ξ : Z, ∀ φ : SchwartzMap V ℂ,
      ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
        SchwartzMap.seminorm ℝ k n
          (sUnitTotalNormAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν ζ ξ φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B) := by
  obtain ⟨s, C, R0, J, hC, hR0, hb⟩ :=
    exists_sUnitMellinAnnularPartitionJointFourier_seminorm_power_bound
      K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport B M hM hOrder k n
  obtain ⟨U, T, hU, hT, hbox⟩ := exists_sUnitTotalNormFibreFactor_box_bounds K S Γ B
  have hR00 : 0 ≤ R0 := zero_le_one.trans hR0
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hRnew : 1 ≤ U * R0 := by
    calc
      1 = (1 : ℝ) * 1 := by norm_num
      _ ≤ U * R0 := mul_le_mul hU hR0 zero_le_one (zero_le_one.trans hU)
  refine ⟨s, C * T, U * R0, J, mul_nonneg hC hT0, hRnew, fun ν ζ ξ φ R hR => ?_⟩
  have hfinal : 0 ≤ (C * T) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
      (1 + |ν|) ^ J * R.val ^ (-B) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hC hT0) (apply_nonneg _ _))
        (pow_nonneg (by positivity) _))
      (Real.rpow_nonneg R.property.le _)
  by_cases hζ : ζ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)
  · by_cases hξ : ξ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)
    · obtain ⟨hFU, hFT⟩ := hbox ζ ξ hζ hξ
      have hFpos := sUnitTotalNormFibreFactor_pos K S ζ ξ
      have hparam : R0 ≤ (sUnitTotalNormRadius K S ζ ξ R).val := by
        change R0 ≤ R.val / sUnitTotalNormFibreFactor K S ζ ξ
        apply (le_div_iff₀ hFpos).mpr
        calc
          R0 * sUnitTotalNormFibreFactor K S ζ ξ ≤ R0 * U :=
            mul_le_mul_of_nonneg_left hFU hR00
          _ = U * R0 := mul_comm _ _
          _ ≤ R.val := hR
      have hpow : (sUnitTotalNormRadius K S ζ ξ R).val ^ (-B) =
          sUnitTotalNormFibreFactor K S ζ ξ ^ B * R.val ^ (-B) := by
        change (R.val / sUnitTotalNormFibreFactor K S ζ ξ) ^ (-B) = _
        rw [Real.div_rpow R.property.le hFpos.le, Real.rpow_neg hFpos.le,
          div_inv_eq_mul]
        exact mul_comm _ _
      let P : ℝ := C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ J * R.val ^ (-B)
      have hP : 0 ≤ P :=
        mul_nonneg
          (mul_nonneg (mul_nonneg hC (apply_nonneg _ _))
            (pow_nonneg (by positivity) _))
          (Real.rpow_nonneg R.property.le _)
      have hbase := hb ν ζ ξ φ (sUnitTotalNormRadius K S ζ ξ R) hparam
      change SchwartzMap.seminorm ℝ k n
        (sUnitMellinAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport ν ζ ξ φ (sUnitTotalNormRadius K S ζ ξ R)) ≤ _
      calc
        _ ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
            (1 + |ν|) ^ J * (sUnitTotalNormRadius K S ζ ξ R).val ^ (-B) := hbase
        _ = P * sUnitTotalNormFibreFactor K S ζ ξ ^ B := by rw [hpow]; dsimp [P]; ring
        _ ≤ P * T := mul_le_mul_of_nonneg_left hFT hP
        _ = (C * T) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
            (1 + |ν|) ^ J * R.val ^ (-B) := by dsimp [P]; ring
    · rw [sUnitTotalNormAnnularPartitionJointFourier_eq_zero_of_not_mem_box K S Γ
        a ha a0 b0 ha0 haSupport ψ hψ hψsupport ν ζ ξ φ R (Or.inr hξ), map_zero]
      exact hfinal
  · rw [sUnitTotalNormAnnularPartitionJointFourier_eq_zero_of_not_mem_box K S Γ
      a ha a0 b0 ha0 haSupport ψ hψ hψsupport ν ζ ξ φ R (Or.inl hζ), map_zero]
    exact hfinal

end HeckeGeneral.Analysis
