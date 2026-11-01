import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SignedDirectFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFirstDualCalibration

/-!
# Direct first terminals from original windows

This entrance has no prime-pool parameter and no slot-count case split.
The same original whole-factor tuple and profile/mask windows compute
both terminal amplitudes. The pure dual zero uses the actual powerful
product diagonal; the original zero is handled by its whole Gram sign.

The final theorem supplies both the raw finite-row exit and its direct
normalized exit, on the same source and the same chosen cutoff. Neither
an aggregate terminal bound nor a vanishing-profile condition is given.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
local instance directFirstDualTerminalCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

/-- The direct source's two actual terminals are bounded from original
individual windows. The zero amplitude is calculated internally from
the original profile, norm and complete principal-mask data. -/
theorem actual_direct_first_dual_terminal_cost_bound
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ sZero : Finset (ℕ × ℕ), ∃ Czero : ℝ, 0 < Czero ∧
    ∀ (sTail : Finset (ℕ × ℕ)) (Ctail : ℝ), 0 ≤ Ctail →
    ∀ (Z : ℝ),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ (s : ActualDirectFirstSource (E := E) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
      (normBound Lmax Nsave decay : ℝ), 1 < decay →
    ∀ (T : FirstDualOriginalWindows (hΓ := hΓ) C s.columns s.ideal s.block s.profiles
      s.radius s.mask sTail sZero k Z X normBound Lmax Nsave decay)
      (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0),
      s.dualZeroCost hDiff + Ctail * X ^ (1 - decay) * s.tailCost sTail ≤
        T.cost hB δ hδ ε (Ctail * (2 * firstTailFieldConstant K * idealCountConstant K ^ k)) Czero := by
  obtain ⟨sZero, Czero, hCzero, hz⟩ :=
    first_dual_zero_diagonal_supported (σ := σ) (η := η) (hS := hS)
      (hΓ := hΓ) (μv := μv) finiteTest k ε hε
  refine ⟨sZero, Czero, hCzero, ?_⟩
  intro sTail Ctail hCtail Z ω ψ centered d a t Y₁ Y₂ X hX s
    normBound Lmax Nsave decay hdecay T hB δ hδ hDiff
  have hzero := hz C s.columns s.columns s.ideal s.ideal s.block s.profiles hDiff
    s.radius s.mask X hX T.windows.factors T.windows.factors_injective T.windows.factor_product
    (Z ^ T.zeroProductExponent) (T.zeroAmplitude hB δ hδ)
    (Real.one_le_rpow T.windows.base_ge_one T.zeroProductExponent_nonneg)
    (T.zeroAmplitude_nonneg hB δ hδ) T.zero_product_norm (T.zero_normalization hB δ hδ)
  change s.dualZeroCost hDiff ≤
    Czero * T.zeroAmplitude hB δ hδ * (Z ^ T.zeroProductExponent) ^ ε at hzero
  rw [← Real.rpow_mul (zero_le_one.trans T.windows.base_ge_one)] at hzero
  have htail := T.tailMass_bound hdecay Ctail hCtail
  change Ctail * X ^ (1 - decay) * s.tailCost sTail ≤ _ at htail
  exact add_le_add hzero htail

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- A direct, pool-free first producer with both original terminal
costs proved from primitive windows. This includes zero original slots
without choosing a different schema or an auxiliary pool. -/
theorem actual_parent_direct_first_dual_terminal_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (rowBallSize normBound : ℝ) (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (Lmax Nsave ξmax : ℝ) (hξmax : 0 < ξmax) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξmax ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξmax ∧
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Cerror Czero : ℝ,
      0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z : ℝ),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualDirectFirstSource (E := E) hΓ μv C Z
      (rowBallFiniteFamily K A.Sf rowBallSize) centered d a t Y₁ Y₂ X hX,
    ∀ (coefficient : s.Column → ℂ),
      (∀ i j, s.profiles i j = (coefficient i * star (coefficient j)) •
        CanonicalRowBall.archTest K A.Sf rowBallSize) →
    ∀ T : FirstDualOriginalWindows (hΓ := hΓ) C s.columns s.ideal s.block s.profiles
      s.radius s.mask sTail sZero k Z X normBound Lmax Nsave decay,
      X ≤ Z ^ ξmax ∧
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * (T.cost hB δ hδ ε Cerror Czero + s.rawRowCost hDiff) ∧
      ∀ N : s.Normalization,
        pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
          (s.fiber : ℝ) * (T.cost hB δ hδ ε Cerror Czero + s.linearizedCost hDiff N) := by
  let decay := tailDecayForWidth Lmax Nsave ξmax
  have hdecay : 1 < decay := tailDecayForWidth_gt_one Lmax Nsave ξmax hξmax
  have hq : firstTailCutoffExponent Lmax Nsave decay ≤ ξmax :=
    firstTailCutoffExponent_le_width Lmax Nsave ξmax Lmax hξmax le_rfl
  obtain ⟨order, hord⟩ := exists_nat_gt
    (max (Module.finrank ℤ Lattice : ℝ) ((Module.finrank ℚ K : ℝ) * decay))
  have horder : Module.finrank ℤ Lattice < order := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hord)
  have hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ (order : ℝ) :=
    (lt_of_le_of_lt (le_max_right _ _) hord).le
  obtain ⟨sTail, Ctail, hCtail, hparent⟩ :=
    actual_parent_first_direct_dual (E := E) (hΓ := hΓ) (μv := μv) (ν := ν) (μ := μ)
      C hDiff rowBallSize decay hdecay order horder hdegree
  obtain ⟨sZero, Czero, hCzero, hterminal⟩ :=
    actual_direct_first_dual_terminal_cost_bound (E := E) (C := C) (hΓ := hΓ) (μv := μv)
      (rowBallFiniteFamily K A.Sf rowBallSize) k ε hε
  let Cnum := 2 * firstTailFieldConstant K * idealCountConstant K ^ k
  have hCnum : 0 ≤ Cnum := mul_nonneg
    (mul_nonneg (by norm_num) firstTailFieldConstant_nonneg)
    (pow_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) k)
  refine ⟨decay, hdecay, rfl, hq, sTail, sZero, Ctail * Cnum, Czero,
    mul_nonneg hCtail hCnum, hCzero, ?_⟩
  intro Z ω ψ centered d a t Y₁ Y₂ X hX s coefficient hprofiles T
  have hp := (hparent Z centered d a t Y₁ Y₂ X hX s coefficient hprofiles).1
  have ht := hterminal sTail Ctail hCtail Z centered d a t Y₁ Y₂ X hX s
    normBound Lmax Nsave decay hdecay T hB δ hδ hDiff
  have hpaid : pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
      (s.fiber : ℝ) * (T.cost hB δ hδ ε (Ctail * Cnum) Czero + s.rawRowCost hDiff) := by
    apply hp.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
    calc
      _ = (s.dualZeroCost hDiff + Ctail * X ^ (1 - decay) * s.tailCost sTail) +
          s.rawRowCost hDiff := by ring
      _ ≤ _ := add_le_add ht le_rfl
  refine ⟨?_, hpaid, ?_⟩
  · rw [T.cutoff_eq]
    exact Real.rpow_le_rpow_of_exponent_le T.windows.base_ge_one hq
  · intro N
    exact hpaid.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (s.rawRowCost_le_linearized hDiff N)) (Nat.cast_nonneg s.fiber))

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_first_dual_terminal_cost_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_direct_first_dual_terminal_bound
