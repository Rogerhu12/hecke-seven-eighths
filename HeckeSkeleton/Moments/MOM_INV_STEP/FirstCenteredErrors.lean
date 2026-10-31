import HeckeSkeleton.Moments.MOM_INV_STEP.UniformSecondPrincipal
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveTail
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredMellinEnergy

/-!
# Actual centered-family errors, uniformly in both spectral frequencies

The second principal source and the source-local tail are evaluated on
the literal first centered family.  Its zero-order Schwartz seminorm is
independent of the spectral frequency.  A nonempty full squarefree pool
forces 1 <= 4U; empty pools contribute zero.  Thus centers below one are
handled without silently replacing their actual scale.

The finite local test and the archimedean majorant are fixed before all
constants.  No principal-source or tail estimate is an input.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredErrors

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalBlock CanonicalNormPools
  FirstCenteredFamily SecondAdaptiveCutoff ActualPoissonScale
open scoped Classical BigOperators nonZeroDivisors

private theorem clipped_power (Z U : ℝ) (hZ : 1 < Z) (hU : 0 < U) :
    Z ^ max 0 (Real.logb Z U) = max 1 U := by
  by_cases hu : 1 ≤ U
  · have hl : 0 ≤ Real.logb Z U :=
      (Real.le_logb_iff_rpow_le hZ hU).mpr (by simpa only [Real.rpow_zero] using hu)
    rw [max_eq_right hl, max_eq_right hu,
      Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) hU]
  · have hu' : U ≤ 1 := (lt_of_not_ge hu).le
    have hl : Real.logb Z U ≤ 0 :=
      (Real.logb_le_iff_le_rpow hZ hU).mpr (by simpa only [Real.rpow_zero] using hu')
    rw [max_eq_left hl, Real.rpow_zero, max_eq_left hu']

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
  [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

def testSize (a : ℝ) : ℝ := SchwartzMap.seminorm ℝ 0 0 (WideMellinTests.weightedTest a 0)

theorem testSize_nonneg (a : ℝ) : 0 ≤ testSize a := apply_nonneg _ _

variable {σ : Type*}

def principalCost (C : ColumnData K S σ)
    (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
    (J : Finset σ) (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)
    (U a t : ℝ) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) : ℝ :=
  let F := family K S C Θ ψ G hν hG J U a t
  2 * ‖SecondPoissonSplit.physicalPrincipal K S D Γ hΓ
      (DivisorInverseColumn.coefficient K S D F γ j d) (F.columns γ) φ h hlc hcs r‖ +
    ‖SecondPoissonSplit.additiveZeros K S D Γ hΓ μv
      (DivisorInverseColumn.coefficient K S D F γ j d) (F.columns γ) φ h hlc hcs r‖

theorem principalCost_nonneg (C : ColumnData K S σ)
    (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
    (J : Finset σ) (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)
    (U a t : ℝ) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) :
    0 ≤ principalCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a t φ h hlc hcs r := by
  unfold principalCost
  positivity

/-- The only bound on a center is its actual positive size and a fixed
upper exponent. In particular its logarithm need not be nonnegative. -/
theorem exists_uniform_principal_bound
    (slotCap : ℕ) (Hmax Umax loss a : ℝ)
    (hHmax : 0 ≤ Hmax) (hUmax : 0 ≤ Umax) (hloss : 0 < loss)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {σ : Type*} (C : ColumnData K S σ)
      (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
      (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
      (J : Finset σ) (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)
      (Z H U t : ℝ), ∀ hZ : 1 < Z,
      0 ≤ H → H ≤ Hmax → 0 < U → U ≤ Z ^ Umax →
      C.slots.card ≤ slotCap →
      (∀ i ∈ C.slots, ∀ P ∈ C.primeLists i, ‖C.primeWeights i P‖ ≤ 1) →
      principalCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a t φ h hlc hcs
        ⟨Z ^ (-H), Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _⟩ ≤
        A * U * Z ^ (H + loss) := by
  obtain ⟨s, A, hA, hp⟩ := UniformSecondPrincipal.exists_uniform_principal_bound
    K S D Γ hΓ μv slotCap Hmax Umax loss hHmax hUmax hloss h hlc hcs
  let B := A * (testSize a) ^ 2 * s.sup (schwartzSeminormFamily ℝ V ℂ) φ
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hA (sq_nonneg _)) (apply_nonneg _ _)
  refine ⟨4 * B, mul_nonneg (by norm_num) hB, ?_⟩
  intro σ C Θ ψ G hν hG J γ j d Z H U t hZ hH0 hH hU hUcap hslots hweights
  let F := family K S C Θ ψ G hν hG J U a t
  let L := max 0 (Real.logb Z U)
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hL : 0 ≤ L := le_max_left _ _
  have hLc : L ≤ Umax :=
    max_le hUmax ((Real.logb_le_iff_le_rpow hZ hU).mpr hUcap)
  have hpow : Z ^ L = max 1 U := clipped_power Z U hZ hU
  have hN (n : Ext) (hn : n ∈ F.columns γ) :
      (n.val.val.absNorm : ℝ) ≤ 4 * Z ^ L := by
    apply (FirstCenteredFamily.family_squarefree K S C Θ ψ G hν hG J U a t γ n hn).2.trans
    rw [hpow]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  by_cases hne : (squarefreePool K Sset (2 * U)).Nonempty
  · obtain ⟨n, hn⟩ := hne
    have hpool := (mem_squarefreePool K Sset (2 * U) n).mp hn
    have hfour : 1 ≤ 4 * U := by
      have hnorm := height_one_le K Sset n
      linarith [hpool.2]
    have hclip : Z ^ L ≤ 4 * U := by
      rw [hpow]
      exact max_le hfour (by linarith)
    have hp' := hp F γ j d Z H L φ hZ.le hH0 hH hL hLc hslots hweights hN
    change principalCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a t φ h hlc hcs
      ⟨Z ^ (-H), _⟩ ≤ A * (SchwartzMap.seminorm ℝ 0 0 (WideMellinTests.weightedTest a t)) ^ 2 *
        s.sup (schwartzSeminormFamily ℝ V ℂ) φ * Z ^ (H + L + loss) at hp'
    rw [WideMellinTests.weightedTest_seminorm_zero] at hp'
    change _ ≤ B * Z ^ (H + L + loss) at hp'
    have he : Z ^ (H + L + loss) = Z ^ L * Z ^ (H + loss) := by
      rw [← Real.rpow_add hz]
      congr 1
      ring
    apply hp'.trans
    rw [he]
    calc
      B * (Z ^ L * Z ^ (H + loss)) ≤ B * ((4 * U) * Z ^ (H + loss)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hclip (Real.rpow_nonneg hz.le _)) hB
      _ = _ := by ring
  · have hempty : squarefreePool K Sset (2 * U) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr (fun n hn => hne ⟨n, hn⟩)
    have hzero : principalCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a t
        φ h hlc hcs ⟨Z ^ (-H), Real.rpow_pos_of_pos hz _⟩ = 0 := by
      simp only [principalCost, family, FirstCompleteFamily.family, hempty,
        SecondPoissonSplit.physicalPrincipal, SecondPoissonSplit.principalPairs,
        SecondPoissonSplit.additiveZeros, Finset.empty_product, Finset.filter_empty,
        Finset.sum_empty, norm_zero, mul_zero, add_zero]
    rw [hzero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) hU.le)
      (Real.rpow_nonneg hz.le _)

def tailCost (C : ColumnData K S σ)
    (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
    (J : Finset σ) (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)
    (P : Finset (Ext × Ext)) (U a t Z tau : ℝ) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) : ℝ :=
  ‖tailSourceAt K S D Γ hΓ μv
    (DivisorInverseColumn.coefficient K S D (family K S C Θ ψ G hν hG J U a t) γ j d)
    P φ h hlc hcs r (fineCutoff K S r U Z tau)‖

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

include ν in
/-- The true cutoff remains 16rN(d₂)(U/N(g))²Z^tau with the actual U,
even when U<1. The principal subset and the full source use this same bound. -/
theorem exists_uniform_tail_bound
    (slotCap : ℕ) (Hmax Umax tauMin saving a : ℝ)
    (hHmax : 0 ≤ Hmax) (hUmax : 0 ≤ Umax) (htauMin : 0 < tauMin) (hsaving : 0 ≤ saving)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {σ : Type*} (C : ColumnData K S σ)
      (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
      (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
      (J : Finset σ) (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)
      (P : Finset (Ext × Ext)) (Z H U t tau : ℝ), ∀ hZ : 2 ≤ Z,
      0 ≤ H → H ≤ Hmax → 0 < U → U ≤ Z ^ Umax → tauMin ≤ tau →
      C.slots.card ≤ slotCap →
      (∀ i ∈ C.slots, ∀ Q ∈ C.primeLists i, ‖C.primeWeights i Q‖ ≤ 1) →
      P ⊆ squarefreePool K Sset (2 * U) ×ˢ squarefreePool K Sset (2 * U) →
      tailCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d P U a t Z tau φ h hlc hcs
        ⟨Z ^ (-H), Real.rpow_pos_of_pos (by linarith) _⟩ ≤
        A * U * Z ^ (-saving) := by
  let Rmax := 2 * Umax + 4
  let order := saving + Hmax + 6 * Umax
  have hRmax : 0 ≤ Rmax := by dsimp only [Rmax]; positivity
  have horder : 0 ≤ order := by dsimp only [order]; positivity
  obtain ⟨s, A, hA, ht⟩ := SecondAdaptiveTail.exists_inverse_tail_bound_uniform
    K S D Γ hΓ μv ν slotCap h hlc hcs Rmax tauMin order hRmax htauMin horder
  let B := A * (testSize a) ^ 2 * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
    fieldConstant K * (4 : ℝ) ^ 6
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg hA (sq_nonneg _)) (apply_nonneg _ _))
      (fieldConstant_nonneg K)) (by norm_num)
  refine ⟨4 * B, mul_nonneg (by norm_num) hB, ?_⟩
  intro σ C Θ ψ G hν hG J γ j d P Z H U t tau hZ hH0 hH hU hUcap htau hslots hweights hP
  have hz : 0 < Z := by linarith
  have hz1 : 1 ≤ Z := by linarith
  let r : {r : ℝ // 0 < r} := ⟨Z ^ (-H), Real.rpow_pos_of_pos hz _⟩
  let F := family K S C Θ ψ G hν hG J U a t
  have h16 : (16 : ℝ) ≤ Z ^ (4 : ℝ) := by
    calc
      (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ Z ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) hZ 4
      _ = _ := (Real.rpow_natCast Z 4).symm
  have hr : r.val ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hz1 (by linarith)
  have hbudget : 16 * r.val * U ^ 2 ≤ Z ^ Rmax := by
    calc
      16 * r.val * U ^ 2 ≤ Z ^ (4 : ℝ) * 1 * (Z ^ Umax) ^ 2 := by
        exact mul_le_mul
          (mul_le_mul h16 hr r.property.le (Real.rpow_nonneg hz.le _))
          (pow_le_pow_left₀ hU.le hUcap 2) (sq_nonneg _)
          (mul_nonneg (Real.rpow_nonneg hz.le _) zero_le_one)
      _ = Z ^ Rmax := by
        rw [mul_one, ← Real.rpow_natCast, ← Real.rpow_mul hz.le, ← Real.rpow_add hz]
        congr 1
        dsimp only [Rmax]
        norm_num
        ring
  by_cases hne : (squarefreePool K Sset (2 * U)).Nonempty
  · obtain ⟨n, hn⟩ := hne
    have hpool := (mem_squarefreePool K Sset (2 * U) n).mp hn
    have hfour : 1 ≤ 4 * U := by
      have hn1 := height_one_le K Sset n
      linarith [hpool.2]
    have hN (n : Ext) (hn : n ∈ F.columns γ) : height K Sset n ≤ 4 * U :=
      (FirstCenteredFamily.family_squarefree K S C Θ ψ G hν hG J U a t γ n hn).2
    have hraw := ht F γ j d P φ r U Z tau order hz1 htau horder le_rfl
      hU hslots hweights hN hP hbudget
    change tailCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d P U a t Z tau
      φ h hlc hcs r ≤
      A * (SchwartzMap.seminorm ℝ 0 0 (WideMellinTests.weightedTest a t)) ^ 2 *
        s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (fieldConstant K / r.val) * (max 1 (4 * U)) ^ 6 * Z ^ (-order) at hraw
    rw [WideMellinTests.weightedTest_seminorm_zero] at hraw
    have hY : max 1 (4 * U) ≤ 4 * Z ^ Umax := by
      apply max_le
      · have hpow := Real.one_le_rpow hz1 hUmax
        linarith
      · exact mul_le_mul_of_nonneg_left hUcap (by norm_num)
    have hpref : fieldConstant K / r.val = fieldConstant K * Z ^ H := by
      dsimp only [r]
      rw [div_eq_mul_inv, Real.rpow_neg hz.le, inv_inv]
    rw [hpref] at hraw
    have hmain : tailCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d P U a t Z tau
        φ h hlc hcs r ≤ B * Z ^ (-saving) := by
      apply hraw.trans
      calc
        _ ≤ A * (testSize a) ^ 2 * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
            (fieldConstant K * Z ^ H) * (4 * Z ^ Umax) ^ 6 * Z ^ (-order) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
          apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hY 6)
          exact mul_nonneg
            (mul_nonneg (mul_nonneg hA (sq_nonneg _)) (apply_nonneg _ _))
            (mul_nonneg (fieldConstant_nonneg K) (Real.rpow_nonneg hz.le _))
        _ = B * (Z ^ H * (Z ^ Umax) ^ 6 * Z ^ (-order)) := by
          rw [mul_pow]
          dsimp only [B, testSize]
          ring
        _ ≤ B * Z ^ (-saving) := by
          apply mul_le_mul_of_nonneg_left _ hB
          rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le,
            ← Real.rpow_add hz, ← Real.rpow_add hz]
          apply Real.rpow_le_rpow_of_exponent_le hz1
          dsimp only [order]
          norm_num
          linarith
    apply hmain.trans
    calc
      B * Z ^ (-saving) = B * 1 * Z ^ (-saving) := by ring
      _ ≤ B * (4 * U) * Z ^ (-saving) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfour hB)
          (Real.rpow_nonneg hz.le _)
      _ = _ := by ring
  · have hempty : squarefreePool K Sset (2 * U) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr (fun n hn => hne ⟨n, hn⟩)
    have hPempty : P = ∅ := by
      apply Finset.subset_empty.mp
      simpa only [hempty, Finset.empty_product] using hP
    have hzero : tailCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d P U a t Z tau
        φ h hlc hcs r = 0 := by
      simp only [tailCost, tailSourceAt, hPempty, Finset.sum_empty, norm_zero]
    rw [hzero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) hU.le)
      (Real.rpow_nonneg hz.le _)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredErrors

end
