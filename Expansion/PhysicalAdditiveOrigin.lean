import Expansion.PhysicalFourierNormalization

/-!
# The original additive zero term vanishes

The lower product-norm support condition of the actual `AdditiveProbeTest`
forces its value at the additive origin to vanish.  Local constancy lets
the finite coordinates be chosen nonzero with their original value at
zero.  Positive archimedean dilations approaching zero then contradict
the fixed lower norm whenever the origin value were nonzero.

This proves the missing zero term from existing test data.  It adds no
vanishing field and does not change the test or its Haar normalization.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.PhysicalFourierNormalization

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical Topology BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "G" => sLocalMultiplicativeGroup K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => mixedEmbedding.mixedSpace K

/-- No extra origin hypothesis is needed for a legal physical additive test. -/
theorem additiveValueAtZero_eq_zero (test : AdditiveProbeTest K Sset) :
    additiveValueAtZero K S test = 0 := by
  by_contra hzero
  have hφ : test.infiniteTest 0 ≠ 0 := (mul_ne_zero_iff.mp hzero).1
  have hψ : (∏ v : Sset, test.finiteTest v 0) ≠ 0 := (mul_ne_zero_iff.mp hzero).2
  have hchoose (v : Sset) : ∃ a : v.val.adicCompletion K,
      a ≠ 0 ∧ test.finiteTest v a = test.finiteTest v 0 := by
    have he := (test.finite_locallyConstant v).eventually_eq 0
    have hn : ∀ᶠ a : v.val.adicCompletion K in 𝓝[≠] 0,
        a ≠ 0 ∧ test.finiteTest v a = test.finiteTest v 0 := by
      filter_upwards [eventually_mem_nhdsWithin,
        he.filter_mono nhdsWithin_le_nhds] with a ha heq
      exact ⟨by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ha, heq⟩
    exact hn.exists
  choose a ha heq using hchoose
  let arch : ℝ → ℂ := fun r =>
    test.infiniteTest ((traceToMixed K).symm (algebraMap ℝ W r))
  have harch : Continuous arch := by
    apply test.infiniteTest.continuous.comp
    apply (traceToMixed K).symm.continuous.comp
    simp only [Algebra.algebraMap_eq_smul_one]
    exact continuous_id.smul continuous_const
  have harch0 : arch 0 ≠ 0 := by simpa only [arch, map_zero] using hφ
  let Cf : ℝ := ∏ v : Sset, ‖a v‖
  let radius : ℝ → ℝ := fun r => |r| ^ Module.finrank ℚ K * Cf
  have hradius : Continuous radius := (continuous_abs.pow _).mul continuous_const
  have hradius0 : radius 0 < test.lowerNorm := by
    simpa only [radius, abs_zero, zero_pow Module.finrank_pos.ne', zero_mul]
      using test.lowerNorm_pos
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] 0,
      0 < r ∧ arch r ≠ 0 ∧ radius r < test.lowerNorm := by
    filter_upwards [eventually_mem_nhdsWithin,
      (harch.continuousAt.eventually_ne harch0).filter_mono nhdsWithin_le_nhds,
      (hradius.continuousAt.eventually_lt_const hradius0).filter_mono nhdsWithin_le_nhds]
      with r hr har hrad
    exact ⟨hr, har, hrad⟩
  obtain ⟨r, hr, har, hrad⟩ := hevent.exists
  let x : G := (realScaleMixedUnit K r hr.ne', fun v => Units.mk0 (a v) (ha v))
  have hvalue : additiveTest K Sset test x = arch r * ∏ v : Sset, test.finiteTest v 0 := by
    simp only [additiveTest, sLocalTensorTestFunction, x, realScaleMixedUnit_val,
      Units.val_mk0, heq, arch]
  have hnorm : sLocalProductNorm K Sset x = radius r := by
    simp only [x, sLocalProductNorm, realScaleMixedUnit_val, Units.val_mk0,
      Algebra.algebraMap_eq_smul_one, mixedEmbedding.norm_smul, map_one, mul_one, radius, Cf]
  have hnonzero : additiveTest K Sset test x ≠ 0 := by
    rw [hvalue]
    exact mul_ne_zero har hψ
  have hsupport := test.norm_support x hnonzero
  rw [hnorm] at hsupport
  exact (not_lt_of_ge hsupport) hrad

end Expansion.PhysicalFourierNormalization

#print axioms Expansion.PhysicalFourierNormalization.additiveValueAtZero_eq_zero
