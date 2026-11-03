import ActualOriginalJointFactor
import ActualClearedSIntegerPairReindex
import ActualJointAnnularAllScalePoisson
import HeckeGeneral.Analysis.CompactSchwartzLatticeBound

/-!
UNCOMPILED / native 0. One actual cleared-residue fiber of the original
annular S-integer pair sum is exactly the actual ordinary product-lattice
periodic sum. The genuine joint profile is pulled back by multiplication
by d/D^M in both columns. This coordinate change is retained explicitly.
No coprimality, coefficient identity or complete-sum identity is an input.

This is a single refined fiber, not the whole coarser periodChart family.
Uniform estimates for the moving pullback profile remain separate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Analysis.ActualClearedJointPeriodicDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramCoefficientBoundDraft ActualGramClearedColumnDraft ActualGramFamilyDraft
open ActualClearedPairReindexDraft ActualTraceProductResidueQuotientDraft
open ActualTraceProductFourierDilationDraft ActualMeanZeroProductPoissonDraft
open scoped Classical BigOperators ContDiff nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "OS" => S.integer K
local notation "NZ" => NonzeroRingElements OS
local notation "NO" => NonzeroRingElements (𝓞 K)
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => traceProductSpace K
local notation "Z" => SFiniteLocalGroup K S

/-- The actual nonzero field multiplier d/D^M, obtained from the same
S-integer denominator unit as the arithmetic reindexing. -/
def clearedDivisorFieldUnit (M : ℕ) (d : NZ) : Kˣ :=
  nonzeroSIntegerFieldUnit K S d *
    Units.map (algebraMap OS K).toMonoidHom (commonDenominatorUnit K S M)⁻¹

theorem clearedDivisorFieldUnit_mul_integer (M : ℕ) (d : NZ) (z : NO) :
    (clearedDivisorFieldUnit K S M d : K) * (z.val : K) =
      ((divisorColumn K S d (unclearedInteger K S M z)).val : K) := by
  change (d.val : K) * ((↑(commonDenominatorUnit K S M)⁻¹ : OS) : K) * (z.val : K) =
    (d.val : K) * (((↑(commonDenominatorUnit K S M)⁻¹ : OS) : K) * (z.val : K))
  ring

def clearedDivisorTraceEquiv (M : ℕ) (d : NZ) : V ≃L[ℝ] V :=
  traceUnitMulEquiv K
    (Units.map (mixedEmbedding K).toMonoidHom (clearedDivisorFieldUnit K S M d))

theorem clearedDivisorTraceEquiv_trace (M : ℕ) (d : NZ) (x : K) :
    clearedDivisorTraceEquiv K S M d (traceEmbedding K x) =
      traceEmbedding K ((clearedDivisorFieldUnit K S M d : K) * x) := by
  apply (traceToMixed K).injective
  rw [clearedDivisorTraceEquiv, traceToMixed_traceUnitMulEquiv]
  simp only [Units.coe_map, traceEmbedding, ContinuousLinearEquiv.apply_symm_apply]
  exact (map_mul (mixedEmbedding K) _ _).symm

variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

/-- The original joint Schwartz profile, with its necessary actual
cleared-divisor coordinate change. The joint kernel is never split. -/
def clearedJointTraceSchwartz (M : ℕ) (d : NZ) (ν : ℝ) (z₁ z₂ : Z)
    (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) : SchwartzMap W ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((traceProductEquiv K).trans
      ((clearedDivisorTraceEquiv K S M d).prodCongr (clearedDivisorTraceEquiv K S M d)))
    (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport ν z₁ z₂ φ R)

theorem clearedJointTraceSchwartz_integer_apply (M : ℕ) (d : NZ) (ν : ℝ) (z₁ z₂ : Z)
    (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (r : ℝ) (x y : 𝓞 K) :
    clearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport
      M d ν z₁ z₂ φ R (r⁻¹ • (traceProductIntegerEquiv K (x, y) : W)) =
    sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport ν z₁ z₂ φ R
      (r⁻¹ • traceEmbedding K ((clearedDivisorFieldUnit K S M d : K) * (x : K)),
       r⁻¹ • traceEmbedding K ((clearedDivisorFieldUnit K S M d : K) * (y : K))) := by
  change sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
    ψ hψ hψsupport ν z₁ z₂ φ R
    ((clearedDivisorTraceEquiv K S M d).prodCongr (clearedDivisorTraceEquiv K S M d)
      (traceProductEquiv K (r⁻¹ • (traceProductIntegerEquiv K (x, y) : W)))) = _
  rw [ContinuousLinearEquiv.map_smul]
  change sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
    ψ hψ hψsupport ν z₁ z₂ φ R
    (clearedDivisorTraceEquiv K S M d (r⁻¹ • traceEmbedding K (x : K)),
     clearedDivisorTraceEquiv K S M d (r⁻¹ • traceEmbedding K (y : K))) = _
  rw [ContinuousLinearEquiv.map_smul, ContinuousLinearEquiv.map_smul,
    clearedDivisorTraceEquiv_trace, clearedDivisorTraceEquiv_trace]

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "D" => finiteSIntegerDenominator K S
local notation "H" => finiteIndexSUnitBoxWidth K S Γ
local notation:max "active" m:max => Prod.snd (sLocalNonzeroIntegerDiagonal K S m) ∈
  finiteLocalValuationBox K S H

/-- One complete genuine cleared S fiber, with the actual original
raw*R*residual coefficient and both original annular columns, is the
actual periodic lattice sum. No residual coprimality premise is used. -/
theorem tsum_cleared_original_joint_eq_productPeriodicSum
    (c k d m₀₁ m₀₂ : NZ) (M L : ℕ) (b z₀₁ z₀₂ : 𝓞 K)
    (hd : algebraMap (𝓞 K) OS (D ^ L) * d.val = algebraMap (𝓞 K) OS b)
    (h₀₁ : algebraMap (𝓞 K) OS (D ^ M) * m₀₁.val = algebraMap (𝓞 K) OS z₀₁)
    (h₀₂ : algebraMap (𝓞 K) OS (D ^ M) * m₀₂.val = algebraMap (𝓞 K) OS z₀₂)
    (hb₁ : active (divisorColumn K S d m₀₁))
    (hb₂ : active (divisorColumn K S d m₀₂))
    (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (N : ℝ) :
    let r := traceNormScale K N
    let z₁ := (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀₁)).2
    let z₂ := (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀₂)).2
    (∑' m : NZ × NZ, clearedPairSummand K S ζ hζ M (M + L) z₀₁ z₀₂
      (annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a a r r
        (originalJointFactor K S ψ d ν z₁ z₂ φ R r)) m) =
    productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k (M + L))
      (fixedChartLatticeWeight K S ζ hζ σ hS6 c k (M + L) M
        (Ideal.Quotient.mk _ z₀₁) (Ideal.Quotient.mk _ z₀₂) d
        (divisorColumn K S d m₀₁) (divisorColumn K S d m₀₂))
      (clearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport
        M d ν z₁ z₂ φ R) N 0 := by
  dsimp only
  let r := traceNormScale K N
  let z₁ := (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀₁)).2
  let z₂ := (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀₂)).2
  let f := annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a a r r
    (originalJointFactor K S ψ d ν z₁ z₂ φ R r)
  let F := clearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport
    ψ hψ hψsupport M d ν z₁ z₂ φ R
  let w := fixedChartLatticeWeight K S ζ hζ σ hS6 c k (M + L) M
    (Ideal.Quotient.mk _ z₀₁) (Ideal.Quotient.mk _ z₀₂) d
    (divisorColumn K S d m₀₁) (divisorColumn K S d m₀₂)
  let I := fixedChartPeriodIdeal K S ζ hζ c k (M + L)
  have hpoint (z : 𝓞 K × 𝓞 K) :
      ordinaryPairExtension K S ζ hζ M (M + L) z₀₁ z₀₂ f z =
        w (latticeQuotientMap (ordinaryProductLattice K) (integralProductLattice K I)
          (traceProductIntegerEquiv K z)) *
          F (r⁻¹ • (traceProductIntegerEquiv K z : W)) := by
    rcases z with ⟨x, y⟩
    have hF := clearedJointTraceSchwartz_integer_apply K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport M d ν z₁ z₂ φ R r x y
    by_cases hx : x ≠ 0
    · by_cases hy : y ≠ 0
      · let m₁ := unclearedInteger K S M ⟨x, hx⟩
        let m₂ := unclearedInteger K S M ⟨y, hy⟩
        have h₁ := unclearedInteger_clear K S M ⟨x, hx⟩
        have h₂ := unclearedInteger_clear K S M ⟨y, hy⟩
        have hweight := fixedChartLatticeWeight_mk_integer K S ζ hζ σ hS6 c k
          (M + L) M (Ideal.Quotient.mk _ z₀₁) (Ideal.Quotient.mk _ z₀₂) d
          (divisorColumn K S d m₀₁) (divisorColumn K S d m₀₂) x y
        rw [clearedDivisorFieldUnit_mul_integer K S M d ⟨x, hx⟩,
          clearedDivisorFieldUnit_mul_integer K S M d ⟨y, hy⟩] at hF
        simp only [ordinaryPairExtension, dif_pos hx, dif_pos hy,
          clearedPairSummand, unclearedInteger_mem_fiber_iff]
        change (if x - z₀₁ ∈ clearedSModulus K S ζ hζ (M + L) ∧
          y - z₀₂ ∈ clearedSModulus K S ζ hζ (M + L) then f (m₁, m₂) else 0) = _
        by_cases hz : x - z₀₁ ∈ clearedSModulus K S ζ hζ (M + L) ∧
            y - z₀₂ ∈ clearedSModulus K S ζ hζ (M + L)
        · rw [if_pos hz]
          have hann := annularOriginalSummand_eq_cleared_weight_fixedFibre
            K S ζ hζ Γ σ hS6 c k d m₀₁ m₀₂ m₁ m₂ M L b z₀₁ z₀₂ x y
            hd h₀₁ h₀₂ h₁ h₂ hb₁ hb₂ hz.1 hz.2 a a r r
            (originalJointFactor K S ψ d ν z₁ z₂ φ R r)
          change f (m₁, m₂) = _ at hann
          rw [hann]
          dsimp only [w, F, I]
          rw [hweight, hF, sUnitMellinAnnularPartitionJointSchwartz_apply]
          simp only [sUnitAnnularPartitionJointCutoff, Complex.ofReal_mul]
          change _ = _
          dsimp only [originalJointFactor]
          ring
        · rw [if_neg hz]
          dsimp only [w, F, I]
          rw [hweight]
          have hmask :
              ((chartCRT K S ζ hζ (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
                (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)
                (actualFrequencyIdeal_exterior K S c) (actualFrequencyIdeal_exterior K S k)
                (M + L) (Ideal.Quotient.mk _ x)).1,
               (chartCRT K S ζ hζ (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
                (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)
                (actualFrequencyIdeal_exterior K S c) (actualFrequencyIdeal_exterior K S k)
                (M + L) (Ideal.Quotient.mk _ y)).1) ≠
                (Ideal.Quotient.mk _ z₀₁, Ideal.Quotient.mk _ z₀₂) := by
            intro he
            apply hz
            exact ⟨Ideal.Quotient.eq.mp (congrArg Prod.fst he),
              Ideal.Quotient.eq.mp (congrArg Prod.snd he)⟩
          simp only [fixedChartPeriodWeight, if_neg hmask, zero_mul]
      · have hy0 : y = 0 := not_ne_iff.mp hy
        rw [hF, sUnitMellinAnnularPartitionJointSchwartz_apply]
        simp only [ordinaryPairExtension, dif_pos hx, dif_neg hy, hy0,
          ZeroMemClass.coe_zero, mul_zero, traceEmbedding, map_zero, smul_zero,
          sUnitAnnularPartitionJointCutoff, sUnitAnnularPartitionCutoff_origin,
          zero_mul, Complex.ofReal_zero, ne_eq, not_true_eq_false, dite_false]
    · have hx0 : x = 0 := not_ne_iff.mp hx
      rw [hF, sUnitMellinAnnularPartitionJointSchwartz_apply]
      simp only [ordinaryPairExtension, dif_neg hx, hx0,
        ZeroMemClass.coe_zero, mul_zero, traceEmbedding, map_zero, smul_zero,
        sUnitAnnularPartitionJointCutoff, sUnitAnnularPartitionCutoff_origin,
        zero_mul, Complex.ofReal_zero, mul_zero, ne_eq, not_true_eq_false, dite_false]
  calc
    _ = ∑' z : 𝓞 K × 𝓞 K, ordinaryPairExtension K S ζ hζ M (M + L) z₀₁ z₀₂ f z :=
      tsum_clearedPair_eq_ordinary K S ζ hζ M (M + L) z₀₁ z₀₂ f
    _ = ∑' z : 𝓞 K × 𝓞 K,
        w (latticeQuotientMap (ordinaryProductLattice K) (integralProductLattice K I)
          (traceProductIntegerEquiv K z)) * F (r⁻¹ • (traceProductIntegerEquiv K z : W)) :=
      tsum_congr hpoint
    _ = _ := by
      change _ = ∑' l : ordinaryProductLattice K,
        w (latticeQuotientMap (ordinaryProductLattice K) (integralProductLattice K I) l) *
          F (r⁻¹ • (0 + (l : W)))
      simp only [zero_add]
      exact Equiv.tsum_eq (traceProductIntegerEquiv K).toEquiv
        (fun l : ordinaryProductLattice K =>
          w (latticeQuotientMap (ordinaryProductLattice K) (integralProductLattice K I) l) *
            F (r⁻¹ • (l : W)))

/-- Actual fixed-box data construct the clearing coordinates at H and
the period depth 2H. The complete fiber sum is genuinely summable before
its exact identification with the periodic lattice sum. -/
theorem exists_fixedDepth_cleared_original_joint_transport
    (c k d m₀₁ m₀₂ : NZ) (hd : active d)
    (hb₁ : active (divisorColumn K S d m₀₁))
    (hb₂ : active (divisorColumn K S d m₀₂)) :
    ∃ b z₀₁ z₀₂ : 𝓞 K,
      algebraMap (𝓞 K) OS (D ^ H) * d.val = algebraMap (𝓞 K) OS b ∧
      algebraMap (𝓞 K) OS (D ^ H) * m₀₁.val = algebraMap (𝓞 K) OS z₀₁ ∧
      algebraMap (𝓞 K) OS (D ^ H) * m₀₂.val = algebraMap (𝓞 K) OS z₀₂ ∧
      ∀ (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (N : ℝ), 0 < N →
      let r := traceNormScale K N
      let z₁ := (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀₁)).2
      let z₂ := (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀₂)).2
      let f := annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a a r r
        (originalJointFactor K S ψ d ν z₁ z₂ φ R r)
      Summable (clearedPairSummand K S ζ hζ H (H + H) z₀₁ z₀₂ f) ∧
      (∑' m, clearedPairSummand K S ζ hζ H (H + H) z₀₁ z₀₂ f m) =
      productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k (H + H))
        (fixedChartLatticeWeight K S ζ hζ σ hS6 c k (H + H) H
          (Ideal.Quotient.mk _ z₀₁) (Ideal.Quotient.mk _ z₀₂) d
          (divisorColumn K S d m₀₁) (divisorColumn K S d m₀₂))
        (clearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport
          H d ν z₁ z₂ φ R) N 0 := by
  obtain ⟨b, z₀₁, z₀₂, hdb, h₀₁, h₀₂⟩ :=
    ActualGramFixedDenominatorDraft.fixed_clearing_triple K S H d m₀₁ m₀₂ hd hb₁ hb₂
  refine ⟨b, z₀₁, z₀₂, hdb, h₀₁, h₀₂, ?_⟩
  intro ν φ R N hN
  refine ⟨?_, ?_⟩
  · exact summable_cleared_original_annularPair K S ζ hζ Γ σ hS6 H (H + H)
      z₀₁ z₀₂ c k d a a0 b0 ha0 haSupport (traceNormScale K N)
      (traceNormScale_pos K N hN).ne' _
  · exact tsum_cleared_original_joint_eq_productPeriodicSum K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport ζ hζ σ hS6 c k d m₀₁ m₀₂ H H b z₀₁ z₀₂
      hdb h₀₁ h₀₂ hb₁ hb₂ ν φ R N

end HeckeGeneral.Analysis.ActualClearedJointPeriodicDraft
