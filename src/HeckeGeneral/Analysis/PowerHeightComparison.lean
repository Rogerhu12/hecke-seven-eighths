import HeckeGeneral.Analysis.PrincipalProbeClosure
import HeckeGeneral.Analysis.PhysicalComparisonAssembly

/-!
# Height comparisons at analysis heights `T₁ = Z^τ`

Q's detector, witness and single-bin estimates hold at analysis heights
`T₁ = Z^τ` for a fixed `τ > 0`, with lower thresholds depending on `τ`
(Q 4270--4279, Lemma 8.2 and 16391--16451).  `PowerHeightComparison` records
exactly this order: the height degree `A`, the tail scale exponent `R` and the
permitted ceiling precede `τ`; `τ` precedes the external tail order `N`; the
constant and the threshold may depend on both.  It is weaker than
`PhysicalHeightComparison`, which asks for one threshold for every height
`1 ≤ T ≤ Z^ceiling`.  The consumers below show that it still suffices for the
height removal of Q Lemma 11.1 and the actual principal Mellin closure.
-/

noncomputable section
namespace HeckeGeneral.Analysis

open Filter Asymptotics Set MeasureTheory
open scoped Topology

/-- The finite-height comparison at power heights `T₁ = Z^τ`. -/
def PowerHeightComparison (J f : ℝ → ℂ) (C σ : ℝ) : Prop :=
  ∃ A R ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∀ N : ℕ, ∃ k Z₀ : ℝ, 0 < k ∧ 1 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
        ‖J Z - f Z‖ ≤ k * (Z ^ (C - 2 * σ) * (1 + Z ^ τ) ^ A + Z ^ R * (Z ^ τ) ^ (-(N : ℝ)))

/-- An external tail bound at power heights. -/
def PowerHeightTailBound (E : ℝ → ℝ → ℂ) : Prop :=
  ∃ A R ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∀ N : ℕ, ∃ k Z₀ : ℝ, 0 < k ∧ 1 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
        ‖E Z (Z ^ τ)‖ ≤ k * Z ^ R * (1 + Z ^ τ) ^ A * (Z ^ τ) ^ (-(N : ℝ))

/-- The uniform-height comparison specializes to power heights. -/
theorem PhysicalHeightComparison.toPower {J f : ℝ → ℂ} {C σ : ℝ}
    (h : PhysicalHeightComparison J f C σ) : PowerHeightComparison J f C σ := by
  obtain ⟨A, R, ceiling, hA, hceiling, hbound⟩ := h
  refine ⟨A, R, ceiling, hA, hceiling, fun τ hτ hτc N => ?_⟩
  obtain ⟨k, Z₀, hk, hZ₀, hb⟩ := hbound N
  refine ⟨k, Z₀, hk, hZ₀, fun Z hZ => ?_⟩
  have hZ1 : 1 ≤ Z := hZ₀.trans hZ
  exact hb Z (Z ^ τ) hZ (Real.one_le_rpow hZ1 hτ.le)
    (Real.rpow_le_rpow_of_exponent_le hZ1 hτc)

/-- Q Lemma 11.1 at power heights: choose `τ` after the common saving and the
height degree, then `N` after `τ`. -/
theorem PowerHeightComparison.isBigO {J f : ℝ → ℂ} {C σ : ℝ}
    (hσ : 0 < σ) (h : PowerHeightComparison J f C σ) :
    (fun Z => J Z - f Z) =O[atTop] (fun Z : ℝ => Z ^ (C - σ)) := by
  obtain ⟨A, R, ceiling, hA, hceiling, hbound⟩ := h
  obtain ⟨τ, hτ, hτc, hfirst, N, htail⟩ :=
    exists_target_height_and_tail_order hσ hceiling A R C hA
  obtain ⟨k, Z₀, hk, hZ₀, hbound⟩ := hbound τ hτ hτc.le N
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨k * ((2 : ℝ) ^ A + 1), ?_⟩
  filter_upwards [eventually_ge_atTop Z₀] with Z hZ
  have hZ1 : 1 ≤ Z := hZ₀.trans hZ
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ1
  have hT1 : 1 ≤ Z ^ τ := Real.one_le_rpow hZ1 hτ.le
  have hTpos : 0 < Z ^ τ := Real.rpow_pos_of_pos hZpos _
  have hh := hbound Z hZ
  have hgrowth : (1 + Z ^ τ) ^ A ≤ (2 : ℝ) ^ A * Z ^ (A * τ) := by
    calc
      _ ≤ (2 * Z ^ τ) ^ A := Real.rpow_le_rpow (by positivity) (by linarith) hA
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hTpos.le,
          ← Real.rpow_mul hZpos.le]
        congr 2
        ring
  have hfirst' : Z ^ (C - 2 * σ) * (1 + Z ^ τ) ^ A ≤
      (2 : ℝ) ^ A * Z ^ (C - σ) := by
    calc
      _ ≤ Z ^ (C - 2 * σ) * ((2 : ℝ) ^ A * Z ^ (A * τ)) :=
        mul_le_mul_of_nonneg_left hgrowth (Real.rpow_nonneg hZpos.le _)
      _ = (2 : ℝ) ^ A * Z ^ (C - 2 * σ + A * τ) := by
        rw [Real.rpow_add hZpos]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1 hfirst) (Real.rpow_nonneg (by norm_num) _)
  have htail' : Z ^ R * (Z ^ τ) ^ (-(N : ℝ)) ≤ Z ^ (C - σ) := by
    rw [← Real.rpow_mul hZpos.le, ← Real.rpow_add hZpos]
    apply Real.rpow_le_rpow_of_exponent_le hZ1
    nlinarith [htail]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hZpos.le _)]
  calc
    _ ≤ k * (Z ^ (C - 2 * σ) * (1 + Z ^ τ) ^ A +
        Z ^ R * (Z ^ τ) ^ (-(N : ℝ))) := hh
    _ ≤ k * ((2 : ℝ) ^ A * Z ^ (C - σ) + Z ^ (C - σ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst' htail') hk.le
    _ = _ := by ring

/-- Assembly at power heights: for every admissible `τ`, an eventual exact
decomposition with a retained bound and a power-height tail. -/
theorem powerHeightComparison_of_decomposition {J f : ℝ → ℂ} {E Q : ℝ → ℝ → ℂ}
    {C σ A ceiling : ℝ} (hA : 0 ≤ A) (hceiling : 0 < ceiling)
    (hmain : ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ k Z₀ : ℝ, 0 ≤ k ∧
      ∀ Z : ℝ, Z₀ ≤ Z → J Z - f Z = E Z (Z ^ τ) + Q Z (Z ^ τ) ∧
        ‖E Z (Z ^ τ)‖ ≤ k * Z ^ (C - 2 * σ) * (1 + Z ^ τ) ^ A)
    (htail : PowerHeightTailBound Q) : PowerHeightComparison J f C σ := by
  obtain ⟨At, R, tailCeiling, hAt, htc, hQ⟩ := htail
  obtain ⟨M, hM⟩ := exists_nat_gt At
  refine ⟨A, R, min ceiling tailCeiling, hA, lt_min hceiling htc,
    fun τ hτ hτc N => ?_⟩
  obtain ⟨k, Z₀, hk, hmainτ⟩ := hmain τ hτ (hτc.trans (min_le_left _ _))
  obtain ⟨kt, Zt, hkt, hZt, ht⟩ :=
    hQ τ hτ (hτc.trans (min_le_right _ _)) (N + M)
  have h2At : 0 < (2 : ℝ) ^ At := Real.rpow_pos_of_pos (by norm_num) _
  have hkt' : 0 < kt * (2 : ℝ) ^ At := mul_pos hkt h2At
  refine ⟨k + kt * (2 : ℝ) ^ At, max (max Z₀ Zt) 1,
    add_pos_of_nonneg_of_pos hk hkt', le_max_right _ _, ?_⟩
  intro Z hZ
  have hZmain : Z₀ ≤ Z := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hZ
  have hZtail : Zt ≤ Z := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hZ
  have hZ1 : 1 ≤ Z := le_trans (le_max_right _ _) hZ
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ1
  have hT1 : 1 ≤ Z ^ τ := Real.one_le_rpow hZ1 hτ.le
  have hTpos : 0 < Z ^ τ := Real.rpow_pos_of_pos hZpos _
  obtain ⟨hdec, hE⟩ := hmainτ Z hZmain
  have hcost : (1 + Z ^ τ) ^ At ≤ (2 : ℝ) ^ At * (Z ^ τ) ^ At := by
    calc
      _ ≤ (2 * Z ^ τ) ^ At := Real.rpow_le_rpow (by positivity) (by linarith) hAt
      _ = _ := Real.mul_rpow (by norm_num) hTpos.le
  have hdecay : (Z ^ τ) ^ At * (Z ^ τ) ^ (-((N + M : ℕ) : ℝ)) ≤
      (Z ^ τ) ^ (-(N : ℝ)) := by
    rw [← Real.rpow_add hTpos]
    apply Real.rpow_le_rpow_of_exponent_le hT1
    simp only [Nat.cast_add]
    linarith
  have hRpos : 0 < Z ^ R := Real.rpow_pos_of_pos hZpos _
  have hQ' : ‖Q Z (Z ^ τ)‖ ≤
      kt * (2 : ℝ) ^ At * (Z ^ R * (Z ^ τ) ^ (-(N : ℝ))) := by
    calc
      _ ≤ kt * Z ^ R * (1 + Z ^ τ) ^ At * (Z ^ τ) ^ (-((N + M : ℕ) : ℝ)) :=
        ht Z hZtail
      _ ≤ kt * Z ^ R * ((2 : ℝ) ^ At * (Z ^ τ) ^ At) *
          (Z ^ τ) ^ (-((N + M : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcost (mul_pos hkt hRpos).le)
          (Real.rpow_nonneg hTpos.le _)
      _ = (kt * (2 : ℝ) ^ At * Z ^ R) *
          ((Z ^ τ) ^ At * (Z ^ τ) ^ (-((N + M : ℕ) : ℝ))) := by ring
      _ ≤ (kt * (2 : ℝ) ^ At * Z ^ R) * (Z ^ τ) ^ (-(N : ℝ)) :=
        mul_le_mul_of_nonneg_left hdecay (mul_pos hkt' hRpos).le
      _ = _ := by ring
  have hX : 0 ≤ Z ^ (C - 2 * σ) * (1 + Z ^ τ) ^ A :=
    mul_nonneg (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg (by linarith) _)
  have hW : 0 ≤ Z ^ R * (Z ^ τ) ^ (-(N : ℝ)) :=
    mul_nonneg hRpos.le (Real.rpow_nonneg hTpos.le _)
  rw [hdec]
  calc
    _ ≤ ‖E Z (Z ^ τ)‖ + ‖Q Z (Z ^ τ)‖ := norm_add_le _ _
    _ ≤ k * Z ^ (C - 2 * σ) * (1 + Z ^ τ) ^ A +
        kt * (2 : ℝ) ^ At * (Z ^ R * (Z ^ τ) ^ (-(N : ℝ))) := add_le_add hE hQ'
    _ ≤ (k + kt * (2 : ℝ) ^ At) *
        (Z ^ (C - 2 * σ) * (1 + Z ^ τ) ^ A + Z ^ R * (Z ^ τ) ^ (-(N : ℝ))) := by
      have h₁ : 0 ≤ k * (Z ^ R * (Z ^ τ) ^ (-(N : ℝ))) := mul_nonneg hk hW
      have h₂ : 0 ≤ kt * (2 : ℝ) ^ At * (Z ^ (C - 2 * σ) * (1 + Z ^ τ) ^ A) :=
        mul_nonneg hkt'.le hX
      nlinarith only [h₁, h₂]

/-- The low estimate and a power-height comparison give the physical probe
bound, exactly as in `physicalProbeBound_of_low_and_heightComparison`. -/
theorem physicalProbeBound_of_low_and_powerHeightComparison
    {J f : ℝ → ℂ} {B σ : ℝ}
    (hσ : 0 < σ) (hσsmall : σ < (B - 7 / 8) / 2)
    (hlow : ∀ ε : ℝ, 0 < ε → J =O[atTop] (fun Z : ℝ => Z ^ (3 / 16 + ε)))
    (hhigh : PowerHeightComparison J f (B - 11 / 16) σ)
    (hloc : LocallyIntegrableOn f (Ioi 0))
    (hsmall : ∀ N : ℝ, f =O[𝓝[>] 0] (fun Z : ℝ => Z ^ N)) :
    PhysicalProbeBound f (B - σ) := by
  have hlow' := hlow ((B - 7 / 8) / 2) (by linarith)
  have hp : (fun Z : ℝ => Z ^ (3 / 16 + (B - 7 / 8) / 2))
      =O[atTop] (fun Z : ℝ => Z ^ (B - σ - 11 / 16)) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Z hZ
    simp only [Real.norm_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one hZ) _), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hh : (fun Z => J Z - f Z) =O[atTop] (fun Z : ℝ => Z ^ (B - σ - 11 / 16)) := by
    simpa only [show B - 11 / 16 - σ = B - σ - 11 / 16 by ring] using
      PowerHeightComparison.isBigO hσ hhigh
  refine ⟨hloc, ?_, hsmall⟩
  simpa only [sub_sub_cancel] using (hlow'.trans hp).sub hh

end HeckeGeneral.Analysis

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
open Filter

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The actual principal closure from a power-height comparison. -/
theorem principal_zeroFree_of_powerHeightComparison
    (P : ProbeData K S) (ψ : HeckeCharacter K) (J : ℝ → ℂ) {B σ : ℝ}
    (hB : B ≤ 1) (hσ : 0 < σ) (hσsmall : σ < (B - 7 / 8) / 2)
    (hlow : ∀ ε : ℝ, 0 < ε → J =O[atTop] (fun Z : ℝ => Z ^ (3 / 16 + ε)))
    (hhigh : PowerHeightComparison J (principalLineProbe K S P ψ) (B - 11 / 16) σ)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hHbound : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2) :
    MeromorphicZeroFreeOn (heckeContinuation K ψ) (rightHalfPlane (B - σ)) := by
  exact heckeContinuation_zeroFreeOn_of_principalProbe_contraction K S P ψ
    (by linarith) (by linarith)
    (physicalProbeBound_of_low_and_powerHeightComparison hσ hσsmall hlow hhigh
      (locallyIntegrableOn_principalLineProbe K S P ψ hH hHbound)
      (principalLineProbe_isBigO_rpow_near_zero K S P ψ hH hHbound))
    hH hHbound

end HeckeGeneral.ThetaSkeleton.Physical
