import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionBlockBound
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionEnvelope

/-!
# The actual long completed contribution of every canonical node

The source is the literal `TerminalNodes.longEnergy`. Its all-ideal
Möbius completion is truncated by the proved original support, split
into its actual dyadic norm blocks, and estimated through the common
Mellin/provider construction. The two divisor/count small powers are
chosen before the source and included in the stated pi budget.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionLong

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open HeckeSkeleton.Moments.MOM_BASE (cubeIdealNorm)
open CanonicalNormPools FixedTripleEnergy
open ProviderNodes CubeCompletionGeometry CubeCompletionMellin CubeCompletionFinite
open CubeCompletionBlocks CubeCompletionEnvelope
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

include hΓ hallowed μv ν μ in
/-- A genuine uniform successor estimate for the complete long-cube
contribution. The recursive premise refers only to actual nodes with
the prescribed smaller row cap. No energy source is assumed. -/
theorem exists_uniform_long_cube_step
    (slotCap : ℕ) (A pi tauMin : ℝ) (hA : 1 ≤ A)
    (hpi : 0 < pi) (htauMin : 0 < tauMin) (t : Finset (ℕ × ℕ)) :
    ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
      ∀ {σ : Type u} [DecidableEq σ] (Θ : Subgroup (HeckeCharacter K))
        (ψ Λ G : HeckeCharacter K), G ∈ Θ →
      ∀ (Z Fcap c z lo hi d eta h tau eps Cih Rmax : ℝ)
        (x : Node K S Γ Θ ψ σ),
      2 ≤ Z → Fcap ≤ A → 0 ≤ c - eta / 2 → 0 ≤ z →
      x.Admissible D Λ G slotCap Z Fcap c z lo hi → x.rowLength ≤ Rmax →
      h ∈ Set.Icc (0 : ℝ) 1 → tau ∈ Set.Icc (0 : ℝ) A → tauMin ≤ tau →
      2 ≤ Z ^ h → h ≤ eta / 128 → eta ≤ d / 16 →
      0 ≤ eps → 1 ≤ Cih →
      UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
        (Fcap + 11 * eta) (c - 7 * eta) z lo hi eps (Rmax - d) Cih t →
      (∀ i : SchwartzTestPartition.Index, |Real.logb Z (annularScale i)| ≤ eta / 8) →
      TerminalNodes.longEnergy K S Γ D slotCap x (Z ^ d) ≤
        C * Cih * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
          Z ^ (x.totalLength + 40 * eta + tau + pi + eps) := by
  obtain ⟨q, CBlock, hCBlock, hblock⟩ := CubeCompletionBlockBound.exists_uniform_block_bound
    K S D Γ hΓ hallowed μv ν μ slotCap A (pi / 2) tauMin hA (by positivity) htauMin t
  obtain ⟨CCap, hCCap, hcap⟩ := exists_cap_square_bound K A (pi / 4)
    (zero_le_one.trans hA) (by positivity)
  obtain ⟨CCount, hCCount, hcount⟩ := exists_count_square_bound A (pi / 4)
    (zero_le_one.trans hA) (by positivity)
  refine ⟨q, CBlock * CCap * CCount,
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hCBlock hCCap) hCCount, ?_⟩
  intro σ _ Θ ψ Λ G hG Z Fcap c z lo hi d eta h tau eps Cih Rmax x
    hZ hFcap hc hz hx hM hh htau htau' hwidth hmesh hstepsize heps hCih hih hshift
  have hz1 : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hz0 := zero_lt_one.trans hz1
  have hb0 : 0 < x.family.base := hx.base_eq.symm ▸ hz0
  have heta : 0 ≤ eta := by linarith [hh.1]
  have hc0 : 0 ≤ c := by linarith
  have hlen := Node.Admissible.lengths_le x hx hz1 hc0 hz
  have hN : x.columnLength ≤ A := hlen.2.1.trans hFcap
  have hCih0 : 0 ≤ Cih := zero_le_one.trans hCih
  let X := Z ^ x.columnLength
  let B := longPool K S X (Z ^ d)
  let J := Finset.range (count (2 * X))
  let E := CBlock * CCap * Cih * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
    Z ^ (x.totalLength + 21 * eta + tau + 3 * pi / 4 + eps)
  have hX : 0 < X := Real.rpow_pos_of_pos hz0 _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hBd : ∀ b ∈ B, Z ^ d ≤ height K Sset b :=
    fun b hb => (longPool_norm_bounds K S X (Z ^ d) b hb).2.2.1
  have hBR : ∀ b ∈ B, height K Sset b ≤ 2 * X :=
    fun b hb => (longPool_norm_bounds K S X (Z ^ d) b hb).2.1
  have hdwidth : 2 ≤ Z ^ (d / 3) :=
    hwidth.trans (Real.rpow_le_rpow_of_exponent_le hz1.le (by linarith [hh.1]))
  have hpiece (j : ℕ) (hj : j ∈ J) :
      finiteEnergy K S D Γ slotCap x (fun H => Z ^ d ≤ cubeIdealNorm H)
        (block B (height K Sset) j) ≤ E := by
    by_cases hne : (block B (height K Sset) j).Nonempty
    · let Bj := block B (height K Sset) j
      let H := scale j
      have hH : 1 ≤ H := scale_one_le j
      have hH0 := scale_pos j
      have hsupport : H ^ 3 ≤ 2 * Z ^ x.columnLength := block_support K S X (Z ^ d) j hne
      have hbwin : ∀ b ∈ Bj, H ≤ height K Sset b ∧ height K Sset b ≤ 2 * H :=
        block_window B (height K Sset) j (fun b _ => height_one_le K Sset b)
      have hlong : 2 * d / 3 ≤ cubeLength Z H :=
        long_block_log_lower B (height K Sset) Z d j hz1 hdwidth
          (fun b _ => height_one_le K Sset b) hBd hne
      have hcapB : cubeCoefficientCap (CubeCompletionProvider.cubeIdeals K S Bj) ^ 2 ≤
          CCap * Z ^ (pi / 4) := by
        apply hcap Z x.columnLength hz1.le hx.column_nonneg hN
        intro I hI
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hI
        have hHcube : H ≤ H ^ 3 := by
          calc
            H = H * 1 := (mul_one H).symm
            _ ≤ H * H ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hH) hH0.le
            _ = _ := by ring
        have hh := (hbwin b hb).2
        change height K Sset b ≤ 4 * Z ^ x.columnLength
        linarith
      have hp := hblock Θ ψ Λ G hG Z Fcap c z lo hi d eta h tau eps Cih Rmax x
        hZ hFcap hc hz hx hM hh htau htau' hwidth hmesh hstepsize heps hCih hih hshift
        (fun H => Z ^ d ≤ cubeIdealNorm H) Bj H hH hsupport hbwin hlong
      calc
        _ ≤ CBlock * Cih * cubeCoefficientCap (CubeCompletionProvider.cubeIdeals K S Bj) ^ 2 *
            (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
              Z ^ (x.totalLength + 21 * eta + tau + pi / 2 + eps) := hp
        _ ≤ CBlock * Cih * (CCap * Z ^ (pi / 4)) *
            (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
              Z ^ (x.totalLength + 21 * eta + tau + pi / 2 + eps) := by gcongr
        _ = E := by
          dsimp only [E]
          have hpow : Z ^ (pi / 4) * Z ^ (x.totalLength + 21 * eta + tau + pi / 2 + eps) =
              Z ^ (x.totalLength + 21 * eta + tau + 3 * pi / 4 + eps) := by
            rw [← Real.rpow_add hz0]
            congr 1
            ring
          calc
            _ = (CBlock * CCap * Cih * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2) *
              (Z ^ (pi / 4) * Z ^ (x.totalLength + 21 * eta + tau + pi / 2 + eps)) := by ring
            _ = _ := by rw [hpow]
    · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
      have he : finiteEnergy K S D Γ slotCap x (fun H => Z ^ d ≤ cubeIdealNorm H)
          (block B (height K Sset) j) = 0 := by
        simp only [finiteEnergy, finiteValue, hempty, Finset.sum_empty, dite_eq_ite,
          ite_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero]
      rw [he]
      exact hE
  rw [longEnergy_eq_finiteEnergy K S D Γ slotCap x hb0 hx.test_support,
    hx.base_eq]
  have hsum := finiteEnergy_le_blocks K S D Γ slotCap x hb0.le
    (fun H => Z ^ d ≤ cubeIdealNorm H) B (2 * X) hBR
  have hcountB : (count (2 * X) : ℝ) ^ 2 ≤ CCount * Z ^ (pi / 4) :=
    hcount Z x.columnLength hz1.le hx.column_nonneg hN
  calc
    _ ≤ (count (2 * X) : ℝ) * ∑ j ∈ J,
        finiteEnergy K S D Γ slotCap x (fun H => Z ^ d ≤ cubeIdealNorm H)
          (block B (height K Sset) j) := hsum
    _ ≤ (count (2 * X) : ℝ) * ∑ _j ∈ J, E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpiece) (Nat.cast_nonneg _)
    _ = (count (2 * X) : ℝ) ^ 2 * E := by
      simp only [J, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    _ ≤ (CCount * Z ^ (pi / 4)) * E := mul_le_mul_of_nonneg_right hcountB hE
    _ = (CBlock * CCap * CCount) * Cih *
        (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
          Z ^ (x.totalLength + 21 * eta + tau + pi + eps) := by
      dsimp only [E]
      have hpow : Z ^ (pi / 4) * Z ^ (x.totalLength + 21 * eta + tau + 3 * pi / 4 + eps) =
          Z ^ (x.totalLength + 21 * eta + tau + pi + eps) := by
        rw [← Real.rpow_add hz0]
        congr 1
        ring
      calc
        _ = ((CBlock * CCap * CCount) * Cih *
          (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2) *
            (Z ^ (pi / 4) * Z ^ (x.totalLength + 21 * eta + tau + 3 * pi / 4 + eps)) := by ring
        _ = _ := by rw [hpow]
    _ ≤ _ := by gcongr <;> linarith

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionLong
