import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderStateEnergy
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderProfile

/-!
# The original Schwartz test in the actual frozen-state energy

The two Euler seminorms from the retained block and reflected tail are
controlled by one finite Schwartz family.  Its indices and constant are
selected before the original node and all its arithmetic parameters.
The completed test is exactly the original square-root weighted profile.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalStateProfile

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualReflectionReindex
  HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.Moments.MOM_BASE
open GeneralReflectedEnergy ProviderTerminalConductor TerminalFrozenBlock
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)
local notation "Ext" => ExteriorIdeal K S

/-- The full reflected source has a uniform finite Schwartz bound in
the original profile, including both its retained rectangles and tail. -/
theorem exists_uniform_state_energy
    (backgrounds : Finset (HeckeCharacter K))
    (R : ReflectionFamily K S D backgrounds) (hE : Input K S D R.data backgrounds)
    (L cstar : ℝ) (hL : 1 ≤ L) (hcstar : 0 < cstar) :
    ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
      ∀ (θ : HeckeCharacter K), θ ∈ backgrounds →
      ∀ (P J f r : Ext) (hr : Squarefree r.val.val) (u : S.unit K)
        (inactive : Finset (ExteriorPrime K S))
        (haway : ∀ p ∈ inactive, ¬p.val.asIdeal ∣ (frozenIdeal K S P J f).val.val ∧
          ¬p.val.asIdeal ∣ r.val.val)
        (s : FrozenState K S (frozenIdeal K S P J f) r)
        (W : SchwartzMap ℝ ℂ), tsupport W ⊆ Set.Icc (1 : ℝ) 2 →
      ∀ (Z N V M Q z d c O H za h amp : ℝ),
      Z₀ ≤ Z → Powerful P.val →
      BoundedSource K S (fixedData K S P J f r hr u inactive haway) Z L (N - 3 * h) H za →
      0 ≤ O → O ≤ L → 0 ≤ za → za ≤ z → 0 ≤ h → h ≤ d → 0 ≤ amp →
      exteriorNorm K S f ≤ Z ^ V → exteriorNorm K S r ≤ Z ^ Q →
      0 ≤ M → 0 ≤ Q → 0 ≤ N + V → V ≤ d →
      HeckePort.Moments.CanonicalMargins (N + V) M Q z c →
      cstar / 2 ≤ c → d ≤ cstar / 1000 →
      ∀ (rows ps : Finset Ext) (a : Ext → ℂ),
      (∀ k ∈ rows, exteriorNorm K S (exteriorMul K S (exteriorMul K S P J) k) ≤ Z ^ M) →
      Z ^ O ≤ exteriorNorm K S P →
      (∀ k ∈ rows, InAnnulus K S Z H k) →
      (∀ p ∈ ps, InAnnulus K S Z za p) →
      (∀ p ∈ ps, ‖a p‖ ≤ amp) →
      (∑ k ∈ rows, ‖fullSource K S D (fixedData K S P J f r hr u inactive haway) s
        (R.data θ) θ a (canonicalVstar W) (Z ^ (N - 3 * h)) ps k‖ ^ 2) ≤
        C * amp ^ 2 * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
          ‖inactiveWeight K S (fixedData K S P J f r hr u inactive haway)‖ ^ 2 *
            Z ^ (N + V - cstar / 8 - O / 2) := by
  obtain ⟨C₀, Z₀, AB, AT, JB, JT, hC₀, hZ₀, hAB, hAT, hb⟩ :=
    TerminalStateEnergy.exists_uniform_state_energy K S D backgrounds R hE
      L 1 2 cstar hL (by norm_num) (by norm_num) hcstar
  obtain ⟨qB, CB, hCB, hbB⟩ := TerminalProfile.exists_finite_seminorm_control JB AB
  obtain ⟨qT, CT, hCT, hbT⟩ := TerminalProfile.exists_finite_seminorm_control JT AT
  let q := qB ∪ qT
  let C := C₀ * (CB + CT) ^ 2
  refine ⟨q, max 1 C, Z₀, le_max_left _ _, hZ₀, ?_⟩
  intro θ hθ P J f r hr u inactive haway s W hW Z N V M Q z d c O H za h amp
    hZ hP hsource hO hOL hza hz hh hhd hamp hf hpr hM hQ hF hV hinv hc hdsmall
    rows ps a hrows hpower hrowsWindow hps ha
  have hcompleted : (TerminalProfile.completedTest W hW).toFun = canonicalVstar W :=
    TerminalProfile.completionCLM_eq_vstar W hW
  have hs := hb θ hθ P J f r hr u inactive haway s (TerminalProfile.completedTest W hW)
    Z N V M Q z d c O H za h amp hZ hP hsource hO hOL hza hz hh hhd hamp hf hpr
    hM hQ hF hV hinv hc hdsmall (TerminalProfile.completedTest W hW).support
    rows ps a hrows hpower hrowsWindow hps ha
  rw [hcompleted] at hs
  have hqB : qB.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) W
  have hqT : qT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W
  have hq : testSeminorm (canonicalVstar W) JB AB + testSeminorm (canonicalVstar W) JT AT ≤
      (CB + CT) * q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    apply (add_le_add ((hbB W hW).trans (mul_le_mul_of_nonneg_left hqB hCB.le))
      ((hbT W hW).trans (mul_le_mul_of_nonneg_left hqT hCT.le))).trans_eq
    ring
  have htest : 0 ≤ testSeminorm (canonicalVstar W) JB AB + testSeminorm (canonicalVstar W) JT AT :=
    add_nonneg (ThetaGlobal.ReflectedAbsoluteProject.testSeminorm_nonneg _ _ _)
      (ThetaGlobal.ReflectedAbsoluteProject.testSeminorm_nonneg _ _ _)
  have hZp : 0 < Z := lt_of_lt_of_le (by norm_num) (hZ₀.trans hZ)
  calc
    _ ≤ C₀ * amp ^ 2 *
        (testSeminorm (canonicalVstar W) JB AB + testSeminorm (canonicalVstar W) JT AT) ^ 2 *
        ‖inactiveWeight K S (fixedData K S P J f r hr u inactive haway)‖ ^ 2 *
          Z ^ (N + V - cstar / 8 - O / 2) := hs
    _ ≤ C₀ * amp ^ 2 * ((CB + CT) * q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
        ‖inactiveWeight K S (fixedData K S P J f r hr u inactive haway)‖ ^ 2 *
          Z ^ (N + V - cstar / 8 - O / 2) := by gcongr
    _ = C * amp ^ 2 * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
        ‖inactiveWeight K S (fixedData K S P J f r hr u inactive haway)‖ ^ 2 *
          Z ^ (N + V - cstar / 8 - O / 2) := by dsimp only [C]; ring
    _ ≤ _ := by gcongr; exact le_max_right _ _

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalStateProfile

end
