import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S3ExpansionData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The sharp original row cutoff and the sixth-power insertion

The original Cauchy rows satisfy the physical cutoff before the direct
padding.  This sharper bound leaves exactly the main branch's two sigma
padding after multiplying by the sixth power of the earlier pool prime.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

theorem originalFrequencyIdeal_neg {A : SArithmeticData K}
    [IsPrincipalIdealRing A.R] (h : A.R) :
    originalFrequencyIdeal (-h) = originalFrequencyIdeal h := by
  by_cases hh : h = 0
  · simp only [hh, neg_zero]
  apply A.exteriorIdealEquiv.injective
  apply Subtype.ext
  change A.extendIdeal (originalFrequencyIdeal (-h)) =
    A.extendIdeal (originalFrequencyIdeal h)
  rw [← (originalFrequencyIdeal_generates (-h) (neg_ne_zero.mpr hh)).2,
    ← (originalFrequencyIdeal_generates h hh).2]
  simp

theorem originalFrequencyIdeal_out_norm {A : SArithmeticData K}
    [IsPrincipalIdealRing A.R] {Γ : Subgroup A.U}
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    A.exteriorNorm (originalFrequencyIdeal q.out.val) =
      (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ q).val := by
  rw [originalFrequencyIdeal, dif_pos q.out.property]
  have hnorm := generates_sIntegerElementNorm
    (ProbeOrbitNormSum.principalExterior A q.out) q.out.val
    (ProbeOrbitNormSum.principalExterior_generates A q.out)
  exact hnorm.symm.trans (congrArg Subtype.val
    (sIntegerOrbitNorm_out K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ q))

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

theorem gaussRows_of_heq {ι κ : Type}
    (G : ActualGaussSource (Arithmetic.context c) ι)
    (H : ActualGaussSource (Arithmetic.context c) κ)
    (hcol : ι = κ) (hsource : HEq G H) : G.rows = H.rows := by
  cases hcol
  exact congrArg ActualGaussSource.rows (eq_of_heq hsource)

theorem original_row_sharp (hF : F.Realizes) (hfamily : family.Realizes)
    (i : Fin family.count) (h : (Arithmetic.data c).R)
    (hh : h ∈ (family.source i).source.rows) :
    (Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h) ≤
      (family.source i).first.retainedScale := by
  rw [gaussRows_of_heq _ _ (hfamily.column i) (hfamily.source i)] at hh
  change h ∈ (FirstCauchyKey.data (family.index i)).rows at hh
  rw [hfamily.retained i]
  apply le_trans _ (le_max_right _ _)
  by_cases hs : FirstCauchyKey.side (family.index i) = true
  · simp only [FirstCauchyKey.data, hs, if_true] at hh
    rw [hF.rightRows (family.index i).1 (family.index i).2.1] at hh
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hh
    rw [originalFrequencyIdeal_neg, originalFrequencyIdeal_out_norm]
    exact ((F.source.source (family.index i).1).mem_divisorRows
      (family.index i).2.1.val q).mp hq
  · simp only [FirstCauchyKey.data, hs, Bool.false_eq_true, if_false] at hh
    rw [hF.leftRows (family.index i).1 (family.index i).2.1] at hh
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hh
    rw [originalFrequencyIdeal_out_norm]
    exact ((F.source.source (family.index i).1).mem_divisorRows
      (family.index i).2.1.val q).mp hq

theorem amplified_row_norm (h : (Arithmetic.data c).R) (hh : h ≠ 0)
    (q : ExteriorPrime (Arithmetic.data c)) :
    (Arithmetic.data c).exteriorNorm
        (originalFrequencyIdeal (actualFrequencyAmplify (Arithmetic.context c) (h, q))) =
      (Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h) * Q q ^ 6 := by
  have hg := amplifiedExterior_generates (Arithmetic.context c)
    (originalFrequencyIdeal h) q h (originalFrequencyIdeal_generates h hh)
  have he := generatedIdeal_unique
    (originalFrequencyIdeal_generates
      (actualFrequencyAmplify (Arithmetic.context c) (h, q)) hg.1) hg
  rw [he]
  change (Ideal.absNorm (amplifiedExterior (originalFrequencyIdeal h) q).val : ℝ) = _
  rw [amplifiedExterior_val, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
  exact mul_comm _ _

theorem pool_prime_sixth (P : PoolPresentation family)
    (q : ExteriorPrime (Arithmetic.data c)) (hq : q ∈ P.pool.primes) :
    Q q ^ 6 ≤ call.base ^ (2 * recipeInductionSigma c) := by
  calc
    _ ≤ (call.base ^ (recipeInductionSigma c / 3)) ^ 6 :=
      pow_le_pow_left₀ (primeNorm_pos q).le (P.pool.norm_upper q hq) 6
    _ = call.base ^ ((recipeInductionSigma c / 3) * (6 : ℝ)) := by
      rw [Real.rpow_mul call.base_pos.le]
      exact (Real.rpow_natCast (call.base ^ (recipeInductionSigma c / 3)) 6).symm
    _ = _ := by congr 1 <;> ring

theorem rpow_prime_multiple (q : ExteriorPrime (Arithmetic.data c)) (n : ℕ) :
    call.base ^ ((n : ℝ) * idealLogLength call.base q.val.asIdeal) = Q q ^ n := by
  rw [mul_comm (n : ℝ), Real.rpow_mul call.base_pos.le,
    rpow_idealLogLength call.base call.domain.scale _ q.val.ne_bot,
    Real.rpow_natCast]
  rfl

theorem rpow_sub_prime_multiple (q : ExteriorPrime (Arithmetic.data c))
    (n : ℕ) (x : ℝ) :
    call.base ^ (x - (n : ℝ) * idealLogLength call.base q.val.asIdeal) =
      call.base ^ x / Q q ^ n := by
  rw [Real.rpow_sub call.base_pos, rpow_prime_multiple]

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3
