import HeckeSkeleton.Moments.MOM_INV_STEP.SUnitSmallRadius
import HeckeGeneral.Analysis.SIntegerProfileTail
import HeckeGeneral.Arithmetic.SIntegerModulusNorm
import HeckeGeneral.Bridge.TraceSchwartzFourierBounds

/-!
# Absolute mass of the actual orbital profile

The small-radius estimate is combined with the genuine large-radius tail
and the proved linear count of all subgroup orbits. The finite family and
constant are chosen before the test function and the moving radius.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalOrbitalMass

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
  HeckeGeneral.Bridge
open SUnitSmallRadius
open scoped Classical BigOperators nonZeroDivisors NNReal

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "Q" => SIntegerOrbits K S Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

def rowProfile (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (ρ : {r : ℝ // 0 < r}) (q : Q) : ℂ :=
  sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
    ⟨ρ.val * (sIntegerOrbitNorm K S Γ q).val,
      mul_pos ρ.property (sIntegerOrbitNorm K S Γ q).property⟩

def absoluteRowMass (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (ρ : {r : ℝ // 0 < r}) : ℝ :=
  ∑' q : Q, ‖rowProfile K S Γ φ ψ ρ q‖

theorem one_le_orbitNorm (q : Q) :
    1 ≤ (sIntegerOrbitNorm K S Γ q).val := by
  rw [← sIntegerOrbitNorm_out]
  exact one_le_sIntegerElementNorm K S q.out

/-- The complete physical row, including the whole unit-conductor
contribution, is absolutely summable with an arbitrarily small extra
power of the radius. -/
theorem exists_absoluteRowMass_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (φ : SchwartzMap V ℂ) (ρ : {r : ℝ // 0 < r}),
        Summable (rowProfile K S Γ φ ψ ρ) ∧
        absoluteRowMass K S Γ φ ψ ρ ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
            (1 + ρ.val⁻¹) * (1 + ρ.val ^ (-ε)) := by
  let L := traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let M : ℕ := Module.finrank ℤ L + ⌈(Module.finrank ℚ K : ℝ) * 2⌉₊ + 1
  have hM : Module.finrank ℤ L < M := by dsimp only [M]; omega
  have hOrder : (Module.finrank ℚ K : ℝ) * 2 ≤ M := by
    have hc := Nat.le_ceil ((Module.finrank ℚ K : ℝ) * 2)
    have hm : ⌈(Module.finrank ℚ K : ℝ) * 2⌉₊ ≤ M := by dsimp only [M]; omega
    exact hc.trans (by exact_mod_cast hm)
  obtain ⟨t, A, hA, hsmall⟩ := exists_sLocalSchwartzProfile_smallPower_global_bound
    K S Γ ψ hψ hψsupport ε hε
  obtain ⟨B, hB, htail⟩ := exists_sIntegerSchwartzProfile_tail_bound
    K S Γ ψ hψ hψsupport 2 (by norm_num) M hM hOrder
  obtain ⟨D, hD, hcount⟩ := exists_card_boundedSIntegerOrbits_le K S Γ
  let s : Finset (ℕ × ℕ) := t ∪ {(M, 0)}
  have hsmallSup (φ : SchwartzMap V ℂ) :
      t.sup (schwartzSeminormFamily ℝ V ℂ) φ ≤
        s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    exact Seminorm.le_finset_sup_apply (Finset.mem_union_left _ hi)
  have hlargeSup (φ : SchwartzMap V ℂ) :
      SchwartzMap.seminorm ℂ M 0 φ ≤ s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    simpa only [SchwartzMap.schwartzSeminormFamily_apply, SchwartzMap.seminorm_apply] using
      (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ V ℂ) (x := φ)
        (show (M, 0) ∈ s by simp only [s, Finset.mem_union,
          Finset.mem_singleton, or_true]))
  refine ⟨s, D * A + B, add_nonneg (mul_nonneg hD.le hA) hB, ?_⟩
  intro φ ρ
  let f : Q → ℂ := rowProfile K S Γ φ ψ ρ
  let H : Set Q := {q | (sIntegerOrbitNorm K S Γ q).val ≤ ρ.val⁻¹}
  have hH : H.Finite := finite_setOf_sIntegerOrbitNorm_le K S Γ _
  have hcompl : Hᶜ = {q : Q | 1 < ρ.val * (sIntegerOrbitNorm K S Γ q).val} := by
    ext q
    simp only [H, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    simpa only [one_div] using
      (div_lt_iff₀' ρ.property : 1 / ρ.val < (sIntegerOrbitNorm K S Γ q).val ↔
        1 < ρ.val * (sIntegerOrbitNorm K S Γ q).val)
  obtain ⟨ht, hb⟩ := htail φ ρ 1 le_rfl
  have hhc : Summable (fun q : H => ‖f q.val‖) := by
    letI := hH.fintype
    exact Summable.of_finite
  have htc : Summable (fun q : ↥(Hᶜ) => ‖f q.val‖) := by
    rw [hcompl]
    exact ht.norm
  have hfn : Summable (fun q : Q => ‖f q‖) := summable_subtype_and_compl.mp ⟨hhc, htc⟩
  refine ⟨hfn.of_norm, ?_⟩
  let P : ℝ := s.sup (schwartzSeminormFamily ℝ V ℂ) φ
  have hP : 0 ≤ P := apply_nonneg _ _
  have hpoint (q : Q) : ‖f q‖ ≤ A * P * ρ.val ^ (-ε) := by
    have hq := one_le_orbitNorm K S Γ q
    have hr : ρ.val ≤ ρ.val * (sIntegerOrbitNorm K S Γ q).val := by
      nlinarith [ρ.property]
    exact (hsmall φ _).trans
      (mul_le_mul
        (mul_le_mul_of_nonneg_left (hsmallSup φ) hA)
        (Real.rpow_le_rpow_of_nonpos ρ.property hr (neg_nonpos.mpr hε.le))
        (Real.rpow_nonneg (mul_pos ρ.property (sIntegerOrbitNorm K S Γ q).property).le _)
        (mul_nonneg hA hP))
  have hcard : (hH.toFinset.card : ℝ) ≤ D * (1 + ρ.val⁻¹) := by
    letI := hH.fintype
    have hc : hH.toFinset.card = Nat.card H := by
      rw [hH.card_toFinset, Nat.card_eq_fintype_card]
    let e : H ≃ BoundedSIntegerOrbits K S Γ ρ.val⁻¹ :=
      { toFun := fun q => ⟨q.val, q.property⟩
        invFun := fun q => ⟨q.val, q.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [hc, Nat.card_congr e]
    exact hcount _ (inv_nonneg.mpr ρ.property.le)
  have hhead : ∑ q ∈ hH.toFinset, ‖f q‖ ≤
      D * (1 + ρ.val⁻¹) * (A * P * ρ.val ^ (-ε)) := by
    calc
      _ ≤ ∑ _q ∈ hH.toFinset, A * P * ρ.val ^ (-ε) :=
        Finset.sum_le_sum (fun q _ => hpoint q)
      _ = (hH.toFinset.card : ℝ) * (A * P * ρ.val ^ (-ε)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard
        (mul_nonneg (mul_nonneg hA hP) (Real.rpow_nonneg ρ.property.le _))
  have htail' : (∑' q : ↥(Hᶜ), ‖f q.val‖) ≤ B * P * (1 + ρ.val⁻¹) := by
    rw [hcompl]
    have hb' : (∑' q : {q : Q // 1 < ρ.val * (sIntegerOrbitNorm K S Γ q).val},
        ‖f q.val‖) ≤ B * SchwartzMap.seminorm ℂ M 0 φ * (1 + ρ.val⁻¹) := by
      simpa only [f, rowProfile, Real.one_rpow, mul_one] using hb
    exact hb'.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hlargeSup φ) hB)
        (add_nonneg zero_le_one (inv_nonneg.mpr ρ.property.le)))
  have hsplit := hfn.sum_add_tsum_subtype_compl hH.toFinset
  have hsplit' : (∑ q ∈ hH.toFinset, ‖f q‖) + (∑' q : ↥(Hᶜ), ‖f q.val‖) =
      ∑' q : Q, ‖f q‖ := by
    have he : (∑' q : {q : Q // q ∉ hH.toFinset}, ‖f q.val‖) =
        (∑' q : ↥(Hᶜ), ‖f q.val‖) :=
      tsum_congr_subtype (fun q : Q => ‖f q‖) (fun q => by
        simp only [Set.Finite.mem_toFinset, Set.mem_compl_iff])
    rwa [he] at hsplit
  change (∑' q : Q, ‖f q‖) ≤ _
  rw [← hsplit']
  apply (add_le_add hhead htail').trans
  have hrp : 0 ≤ ρ.val ^ (-ε) := Real.rpow_nonneg ρ.property.le _
  have hri : 0 ≤ 1 + ρ.val⁻¹ := add_nonneg zero_le_one (inv_nonneg.mpr ρ.property.le)
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hD.le hA) hP) hri,
    mul_nonneg (mul_nonneg (mul_nonneg hB hP) hri) hrp]

theorem rowScale_cost_le (Z M ε : ℝ) (hZ : 1 ≤ Z)
    (hM : 0 ≤ M) (hε : 0 ≤ ε) :
    (1 + (Z ^ (-M))⁻¹) * (1 + (Z ^ (-M)) ^ (-ε)) ≤
      4 * Z ^ ((1 + ε) * M) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hMpow : 1 ≤ Z ^ M := Real.one_le_rpow hZ hM
  have hεpow : 1 ≤ Z ^ (ε * M) := Real.one_le_rpow hZ (mul_nonneg hε hM)
  have hinv : (Z ^ (-M))⁻¹ = Z ^ M := by rw [Real.rpow_neg hz.le, inv_inv]
  have hp : (Z ^ (-M)) ^ (-ε) = Z ^ (ε * M) := by
    rw [← Real.rpow_mul hz.le]
    congr 1
    ring
  rw [hinv, hp]
  calc
    _ ≤ (2 * Z ^ M) * (2 * Z ^ (ε * M)) := by
      gcongr <;> linarith
    _ = 4 * Z ^ ((1 + ε) * M) := by
      rw [show (1 + ε) * M = M + ε * M by ring, Real.rpow_add hz]
      ring

/-- The field, fixed finite test and subgroup determine all constants
before the base and physical row length. -/
theorem exists_absoluteRowMass_rowScale_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (φ : SchwartzMap V ℂ) (Z M : ℝ) (hZ : 1 ≤ Z), 0 ≤ M →
        absoluteRowMass K S Γ φ ψ
          ⟨Z ^ (-M), Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _⟩ ≤
            C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * Z ^ ((1 + ε) * M) := by
  obtain ⟨s, C, hC, hb⟩ := exists_absoluteRowMass_bound K S Γ ψ hψ hψsupport ε hε
  refine ⟨s, 4 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro φ Z M hZ hM
  apply (hb φ _).2.trans
  calc
    _ = (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ) *
        ((1 + (Z ^ (-M))⁻¹) * (1 + (Z ^ (-M)) ^ (-ε))) := by ring
    _ ≤ (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ) *
        (4 * Z ^ ((1 + ε) * M)) :=
      mul_le_mul_of_nonneg_left (rowScale_cost_le Z M ε hZ hM hε.le)
        (mul_nonneg hC (apply_nonneg _ _))
    _ = _ := by ring

end HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalOrbitalMass

end

