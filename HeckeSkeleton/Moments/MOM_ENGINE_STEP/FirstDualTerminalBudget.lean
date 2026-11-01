import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SignedActualFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDualZeroSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget

/-!
# The actual first dual-zero and tail terminals

The terminal windows retain the original factor tuple, original
common-support labels, principal masks, and physical cutoff.  Their
pointwise zero normalization now bounds the pure dual-frequency zero.
There is no hypothesis that the original row-ball profile vanishes at
zero, and no estimate for the sum of terminal terms is an input.

The signed original source provides both a raw finite-row exit and the
same pool's linearized exit.  All constants and seminorms are selected
before the source, scale, coefficients, and normalization.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

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
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters} {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
local instance firstDualTerminalCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualFirstSource

/-- Only original individual profile and norm windows. The full tuple
injection and actual principal-mask divisors are unchanged. -/
structure DualTerminalCalibration
    (s : ActualFirstSource (E := E) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Lmax Nsave decay : ℝ) where
  productExponent : ℝ
  /-- The pure-dual diagonal only uses pairs with a nonzero original
  profile. Zero cross-columns remain in the original carrier. -/
  zeroProductExponent : ℝ
  zeroProductExponent_nonneg : 0 ≤ zeroProductExponent
  zero_product_norm : ∀ ij ∈ s.columns ×ˢ s.columns,
    s.profiles ij.1 ij.2 ≠ 0 →
      (Ideal.absNorm ((s.ideal ij.1).val * (s.ideal ij.2).val) : ℝ) ≤
        Z ^ zeroProductExponent
  profileExponent : ℝ
  maskExponent : ℝ
  modulusExponent : ℝ
  tailAmplitude : ℝ
  zeroAmplitude : ℝ
  zeroAmplitude_nonneg : 0 ≤ zeroAmplitude
  windows : FirstTailWindows hΓ C s.columns s.columns s.ideal s.ideal s.block
    sTail s.profiles s.radius s.mask k Z productExponent profileExponent maskExponent
    modulusExponent tailAmplitude
  exponent_bound : firstTailExponent k productExponent profileExponent maskExponent
    modulusExponent ≤ Lmax
  cutoff_eq : X = Z ^ firstTailCutoffExponent Lmax Nsave decay
  zero_normalization : ∀ v ∈ firstZeroPairs s.columns s.columns s.ideal s.ideal,
    sZero.sup (schwartzSeminormFamily ℂ V ℂ) (s.profiles v.2.1 v.2.2) *
      (∑ D ∈ ((s.block v.1).mask s.mask).powerset, firstZeroDivisorWeight s.radius D) ≤
        zeroAmplitude / Real.sqrt (Z ^ zeroProductExponent)

namespace DualTerminalCalibration

variable {s : ActualFirstSource (E := E) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def cost (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (ε Cerror Czero : ℝ) : ℝ :=
  Czero * T.zeroAmplitude * Z ^ (T.zeroProductExponent * ε) +
    Cerror * T.tailAmplitude * Z ^ (-Nsave)

theorem tailCost_bound
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (hdecay : 1 < decay) (Ctail : ℝ) (hCtail : 0 ≤ Ctail) :
    Ctail * X ^ (1 - decay) * s.tailCost sTail ≤
      (Ctail * (2 * firstTailFieldConstant K * idealCountConstant K ^ k)) *
        T.tailAmplitude * Z ^ (-Nsave) := by
  let Cnum := 2 * firstTailFieldConstant K * idealCountConstant K ^ k
  let L := firstTailExponent k T.productExponent T.profileExponent T.maskExponent T.modulusExponent
  have hCnum : 0 ≤ Cnum := mul_nonneg
    (mul_nonneg (by norm_num) firstTailFieldConstant_nonneg)
    (pow_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) k)
  have hw := T.windows.power_bound
  change s.tailCost sTail ≤ Cnum * T.tailAmplitude * Z ^ L at hw
  calc
    _ ≤ Ctail * X ^ (1 - decay) * (Cnum * T.tailAmplitude * Z ^ L) :=
      mul_le_mul_of_nonneg_left hw (mul_nonneg hCtail (Real.rpow_nonneg (zero_le_one.trans hX) _))
    _ = (Ctail * Cnum) * T.tailAmplitude * (X ^ (1 - decay) * Z ^ L) := by ring
    _ ≤ (Ctail * Cnum) * T.tailAmplitude * Z ^ (-Nsave) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (mul_nonneg hCtail hCnum) T.windows.amplitude_nonneg)
      rw [T.cutoff_eq]
      exact first_tail_cutoff_power_of_le Z L Lmax Nsave decay
        T.windows.base_ge_one hdecay T.exponent_bound

end DualTerminalCalibration

/-- The original pool and normalization bound exactly the finite rows
that occur in the signed first-source exit. -/
theorem rawRowCost_le_linearized
    (s : ActualFirstSource (E := E) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (N : s.Normalization) : s.rawRowCost hDiff ≤ s.linearizedCost N := by
  unfold ActualFirstSource.rawRowCost ActualFirstSource.linearizedCost
  apply Finset.sum_le_sum
  intro v _
  change (∑ D : ((s.block v).mask s.mask).powerset,
      ‖∑ q ∈ (s.source v).divisorRows D.val,
        ∑ i ∈ (s.source v).leftColumns, ∑ j ∈ (s.source v).rightColumns,
          ((s.source v).pairs i j).transformedRow μv hDiff finiteTest s.radius D.val q‖) ≤ _
  apply Finset.sum_le_sum
  intro D _
  exact ((s.charts v D).kernel_bound_of_phase_one hDiff s.mask X hX (fun i j hc =>
    canonicalFirstCommonBlock_phase_one hΓ C s.columns s.columns s.ideal s.ideal
      v.val v.property i j hc)).trans
    ((s.pools v D).kernelCost_le_linearized hDiff (N.left v D) (N.right v D)
      (N.left_pos v D) (N.right_pos v D))

end ActualFirstSource

/-- The pure dual diagonal and the original tail windows control the
literal two first terminal costs; the zero test is allowed to be nonzero. -/
theorem actual_first_dual_terminal_cost_bound
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ sZero : Finset (ℕ × ℕ), ∃ Czero : ℝ, 0 < Czero ∧
    ∀ (sTail : Finset (ℕ × ℕ)) (Ctail : ℝ), 0 ≤ Ctail →
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ (s : ActualFirstSource (E := E) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX)
      (Lmax Nsave decay : ℝ), 1 < decay →
    ∀ (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0),
      s.dualZeroCost hDiff + Ctail * X ^ (1 - decay) * s.tailCost sTail ≤
        T.cost ε (Ctail * (2 * firstTailFieldConstant K * idealCountConstant K ^ k)) Czero := by
  obtain ⟨sZero, Czero, hCzero, hz⟩ :=
    first_dual_zero_diagonal_supported (σ := σ) (η := η) (hS := hS)
      (hΓ := hΓ) (μv := μv) finiteTest k ε hε
  refine ⟨sZero, Czero, hCzero, ?_⟩
  intro sTail Ctail hCtail Z ell eps bad P ω ψ centered d a t Y₁ Y₂ X hX s
    Lmax Nsave decay hdecay T hDiff
  have hzero := hz C s.columns s.columns s.ideal s.ideal s.block s.profiles hDiff
    s.radius s.mask X hX T.windows.factors T.windows.factors_injective T.windows.factor_product
    (Z ^ T.zeroProductExponent) T.zeroAmplitude
    (Real.one_le_rpow T.windows.base_ge_one T.zeroProductExponent_nonneg)
    T.zeroAmplitude_nonneg T.zero_product_norm T.zero_normalization
  change s.dualZeroCost hDiff ≤
    Czero * T.zeroAmplitude * (Z ^ T.zeroProductExponent) ^ ε at hzero
  rw [← Real.rpow_mul (zero_le_one.trans T.windows.base_ge_one)] at hzero
  exact add_le_add hzero (T.tailCost_bound hdecay Ctail hCtail)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- Fixed decay, fixed seminorms and fixed constants give both genuine
first-source exits, with the two terminal terms already paid. -/
theorem actual_parent_first_dual_terminal_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (rowBallSize : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (Lmax Nsave ξmax : ℝ) (hξmax : 0 < ξmax) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξmax ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξmax ∧
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Cerror Czero : ℝ,
      0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualFirstSource (E := E) hΓ μv C P
      (rowBallFiniteFamily K A.Sf rowBallSize) centered d a t Y₁ Y₂ X hX,
    ∀ (coefficient : s.Column → ℂ),
      (∀ i j, s.profiles i j = (coefficient i * star (coefficient j)) •
        CanonicalRowBall.archTest K A.Sf rowBallSize) →
    ∀ T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay,
      X ≤ Z ^ ξmax ∧
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * (T.cost ε Cerror Czero + s.rawRowCost hDiff) ∧
      ∀ N : s.Normalization,
        pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
          (s.fiber : ℝ) * (T.cost ε Cerror Czero + s.linearizedCost N) := by
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
    actual_parent_first_dual_raw (E := E) (hΓ := hΓ) (μv := μv) (ν := ν) (μ := μ)
      C hDiff rowBallSize decay hdecay order horder hdegree
  obtain ⟨sZero, Czero, hCzero, hterminal⟩ :=
    actual_first_dual_terminal_cost_bound (E := E) (C := C) (hΓ := hΓ) (μv := μv)
      (rowBallFiniteFamily K A.Sf rowBallSize) k ε hε
  let Cnum := 2 * firstTailFieldConstant K * idealCountConstant K ^ k
  have hCnum : 0 ≤ Cnum := mul_nonneg
    (mul_nonneg (by norm_num) firstTailFieldConstant_nonneg)
    (pow_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) k)
  refine ⟨decay, hdecay, rfl, hq, sTail, sZero, Ctail * Cnum, Czero,
    mul_nonneg hCtail hCnum, hCzero, ?_⟩
  intro Z ell eps bad P ω ψ centered d a t Y₁ Y₂ X hX s coefficient hprofiles T
  have hp := hparent Z ell eps bad P centered d a t Y₁ Y₂ X hX s coefficient hprofiles
  have ht := hterminal sTail Ctail hCtail Z ell eps bad P
    centered d a t Y₁ Y₂ X hX s Lmax Nsave decay hdecay T hDiff
  have hpaid : pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
      (s.fiber : ℝ) * (T.cost ε (Ctail * Cnum) Czero + s.rawRowCost hDiff) := by
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

#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.DualTerminalCalibration.tailCost_bound
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.rawRowCost_le_linearized
#print axioms HeckeSkeleton.Moments.EngineStep.actual_first_dual_terminal_cost_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_first_dual_terminal_bound
