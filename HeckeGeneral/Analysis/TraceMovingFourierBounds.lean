import HeckeGeneral.Analysis.TraceMovingPhaseBounds
import HeckeGeneral.Analysis.SUnitPartitionFourierBounds

/-!
# Moving Mellin frequency bounds after actual joint trace Fourier transform

The phase is the literal `exp (I * ν * (log n(x) - log n(y)))` already
constructed in `TraceMovingPhaseBounds`. Its proved polynomial derivative
cost is passed through the genuine two-column trace Fourier CLM. Both
frequency conjugations and the squared mixed Haar Jacobian are unchanged.

The complete finite annular partition family then has shared bounds selected
before ν, both finite coordinates, the original test function, and R. The
threshold remains support dependent. These estimates do not assemble a Gram
identity, alter the original Γ, or identify a fixed fibre with an entire orbit.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical ContDiff BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- Elementary finite aggregation. This helper only combines bounds already
proved for each member; the applications below supply those bounds from the
actual moving orbital kernel and the actual Fourier operator. -/
private theorem finite_uniform_moving_bounds
    {ι : Type*} [Fintype ι]
    (P : ι → ℝ → SchwartzMap V ℂ → {r : ℝ // 0 < r} → ℝ) (B : ℝ)
    (hP : ∀ i, ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, ∃ J : ℕ,
      0 ≤ C ∧ 1 ≤ R0 ∧
        ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
          P i ν φ R ≤
            C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, ∃ J : ℕ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
        ∀ i, P i ν φ R ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B) := by
  choose s C R0 J hC _hR0 hbound using hP
  let sall : Finset (ℕ × ℕ) := Finset.univ.biUnion s
  let Call : ℝ := ∑ i : ι, C i
  let Rall : ℝ := 1 + ∑ i : ι, max (R0 i) 0
  let Jall : ℕ := Finset.univ.sup J
  have hCall : 0 ≤ Call := Finset.sum_nonneg (fun i _ => hC i)
  have hRall : 1 ≤ Rall :=
    le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => le_max_right (R0 i) 0))
  have hCi (i : ι) : C i ≤ Call :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  have hRi (i : ι) : R0 i ≤ Rall := by
    calc
      R0 i ≤ max (R0 i) 0 := le_max_left _ _
      _ ≤ ∑ j : ι, max (R0 j) 0 :=
        Finset.single_le_sum (fun j _ => le_max_right (R0 j) 0) (Finset.mem_univ i)
      _ ≤ 1 + ∑ j : ι, max (R0 j) 0 := le_add_of_nonneg_left (by norm_num)
  have hJi (i : ι) : J i ≤ Jall := Finset.le_sup (Finset.mem_univ i)
  have hsi (i : ι) (φ : SchwartzMap V ℂ) :
      (s i).sup (schwartzSeminormFamily ℝ V ℂ) φ ≤
        sall.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro j hj
    exact Seminorm.le_finset_sup_apply
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hj⟩)
  refine ⟨sall, Call, Rall, Jall, hCall, hRall, fun ν φ R hR i => ?_⟩
  have hν : 1 ≤ 1 + |ν| := by linarith [abs_nonneg ν]
  have hfactor : 0 ≤ Call * sall.sup (schwartzSeminormFamily ℝ V ℂ) φ :=
    mul_nonneg hCall (apply_nonneg _ _)
  calc
    _ ≤ C i * (s i).sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ (J i) * R.val ^ (-B) := hbound i ν φ R ((hRi i).trans hR)
    _ ≤ Call * sall.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ Jall * R.val ^ (-B) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul (hCi i) (hsi i φ) (apply_nonneg _ _) hCall)
          (pow_le_pow_right₀ hν (hJi i)) (pow_nonneg (zero_le_one.trans hν) _) hfactor)
        (Real.rpow_nonneg R.property.le _)

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "Ω" => Set.prod (traceArchRegular K) (traceArchRegular K)
local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- Actual moving-phase joint trace Fourier transform of the fixed-cutoff
orbital kernel. The moving phase is part of the function before Fourier
transformation, not a presumed derivative bound or a fixed infinity type. -/
def traceMovingCutoffOrbitalFourier
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupport : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    SchwartzMap (TraceJointEuclideanSpace K) ℂ :=
  traceJointProductFourierCLM K
    (traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport
      χ hχ hχsupport hχΩ ν φ R)

/-- Every target Fourier seminorm has a genuine polynomial moving-frequency
loss. The exponent is selected from the Fourier operator's finite input
seminorms, before the moving frequency and the test function. -/
theorem exists_traceMovingCutoffOrbitalFourier_seminorm_power_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupport : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ Lattice < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, ∃ J : ℕ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
        SchwartzMap.seminorm ℝ k n
          (traceMovingCutoffOrbitalFourier K S Γ ψ hψ hψsupport
            χ hχ hχsupport hχΩ ν φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B) := by
  obtain ⟨t, D, _hD, hFourier⟩ := traceJointProductFourier_real_seminorm_bound K k n
  let J0 : ℕ := t.sup (fun i => i.2)
  let P (i : ↥t) (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) : ℝ :=
    SchwartzMap.seminorm ℝ i.val.1 i.val.2
      (traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport
        χ hχ hχsupport hχΩ ν φ R)
  have hP (i : ↥t) :
      ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, ∃ J : ℕ, 0 ≤ C ∧ 1 ≤ R0 ∧
        ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
          P i ν φ R ≤
            C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B) := by
    obtain ⟨s, C, R0, hC, hR0, hb⟩ :=
      exists_traceMovingCutoffOrbitalSchwartz_seminorm_power_bound
        K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ B M hM hOrder i.val.1 J0
    refine ⟨s, C, R0, J0, hC, hR0, fun ν φ R hR => ?_⟩
    exact hb ν φ R hR i.val.2 (Finset.le_sup i.property)
  obtain ⟨s, C, R0, J, hC, hR0, hbound⟩ := finite_uniform_moving_bounds K P B hP
  refine ⟨s, (D : ℝ) * C, R0, J, mul_nonneg (NNReal.coe_nonneg D) hC,
    hR0, fun ν φ R hR => ?_⟩
  have hnonneg : 0 ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
      (1 + |ν|) ^ J * R.val ^ (-B) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (apply_nonneg _ _))
      (pow_nonneg (by positivity) _)) (Real.rpow_nonneg R.property.le _)
  have hsup : t.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
      (traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport
        χ hχ hχsupport hχΩ ν φ R) ≤
      C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B) :=
    Seminorm.finset_sup_apply_le hnonneg (fun i hi => hbound ν φ R hR ⟨i, hi⟩)
  calc
    _ ≤ (D : ℝ) * t.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
        (traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport
          χ hχ hχsupport hχΩ ν φ R) := hFourier _
    _ ≤ (D : ℝ) * (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ J * R.val ^ (-B)) :=
      mul_le_mul_of_nonneg_left hsup (NNReal.coe_nonneg D)
    _ = ((D : ℝ) * C) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ J * R.val ^ (-B) := by ring

local notation "Z" => SFiniteLocalGroup K S

/-- The literal moving phase and the literal annular η cutoffs from the same
original Γ, followed by the actual two-column trace Fourier transform. -/
def sUnitMovingAnnularPartitionJointFourier
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (ν : ℝ) (ζ ξ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    SchwartzMap (TraceJointEuclideanSpace K) ℂ :=
  traceMovingCutoffOrbitalFourier K S Γ ψ hψ hψsupport
    (sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ)
    (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ a0 b0 ha0 haSupport).1
    (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ a0 b0 ha0 haSupport).2.1
    (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ a0 b0 ha0 haSupport).2.2
    ν φ R

private theorem sUnitMovingAnnularPartitionJointFourier_congr
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (ζ ξ ζ' ξ' : Z)
    (h : sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ =
      sUnitAnnularPartitionJointCutoff K S Γ a ζ' ξ')
    (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    sUnitMovingAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν ζ ξ φ R =
      sUnitMovingAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν ζ' ξ' φ R := by
  unfold sUnitMovingAnnularPartitionJointFourier traceMovingCutoffOrbitalFourier
  apply congrArg (traceJointProductFourierCLM K)
  ext p
  simp only [traceMovingCutoffOrbitalSchwartz_apply, h]

/-- The complete actual partition family has a single polynomial ν loss and
a single finite original φ seminorm bound. Both finite coordinates range over
all local units, including the zero cutoffs off the original valuation box. -/
theorem exists_sUnitMovingAnnularPartitionJointFourier_seminorm_power_bound
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ Lattice < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, ∃ J : ℕ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ ν : ℝ, ∀ ζ ξ : Z, ∀ φ : SchwartzMap V ℂ,
      ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
        SchwartzMap.seminorm ℝ k n
          (sUnitMovingAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν ζ ξ φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B) := by
  let I := Set.range (fun p : Z × Z =>
    sUnitAnnularPartitionJointCutoff K S Γ a p.1 p.2)
  letI : Fintype I := (finite_range_sUnitAnnularPartitionJointCutoff K S Γ a).fintype
  let pick : I → Z × Z := fun i => Classical.choose i.property
  have hpick (i : I) :
      sUnitAnnularPartitionJointCutoff K S Γ a (pick i).1 (pick i).2 = i.val :=
    Classical.choose_spec i.property
  let P (i : I) (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) : ℝ :=
    SchwartzMap.seminorm ℝ k n
      (sUnitMovingAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν (pick i).1 (pick i).2 φ R)
  have hP (i : I) :
      ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, ∃ J : ℕ, 0 ≤ C ∧ 1 ≤ R0 ∧
        ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
          P i ν φ R ≤
            C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B) := by
    exact exists_traceMovingCutoffOrbitalFourier_seminorm_power_bound
      K S Γ ψ hψ hψsupport
      (sUnitAnnularPartitionJointCutoff K S Γ a (pick i).1 (pick i).2)
      (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
        (pick i).1 (pick i).2 a0 b0 ha0 haSupport).1
      (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
        (pick i).1 (pick i).2 a0 b0 ha0 haSupport).2.1
      (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
        (pick i).1 (pick i).2 a0 b0 ha0 haSupport).2.2
      B M hM hOrder k n
  obtain ⟨s, C, R0, J, hC, hR0, hbound⟩ := finite_uniform_moving_bounds K P B hP
  refine ⟨s, C, R0, J, hC, hR0, fun ν ζ ξ φ R hR => ?_⟩
  let i : I := ⟨sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ, ⟨(ζ, ξ), rfl⟩⟩
  have heq : sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ =
      sUnitAnnularPartitionJointCutoff K S Γ a (pick i).1 (pick i).2 := (hpick i).symm
  rw [sUnitMovingAnnularPartitionJointFourier_congr K S Γ a ha a0 b0 ha0 haSupport
    ψ hψ hψsupport ζ ξ (pick i).1 (pick i).2 heq ν φ R]
  exact hbound ν φ R hR i

end HeckeGeneral.Analysis
