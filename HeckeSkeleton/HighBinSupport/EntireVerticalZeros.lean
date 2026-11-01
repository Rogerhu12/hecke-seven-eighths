import HeckeGeneral.Analysis.FiniteEulerRational
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Entire functions on three vertical lines

A nonzero entire function of three complex variables is nonzero almost
everywhere on every product of vertical real lines. One nonzero complex
value supplies the base points for all three successive one-variable
slices. No nonvanishing condition on an individual vertical slice is
assumed. The measure is the literal product volume on `ℝ × (ℝ × ℝ)`.

The final lemma checks that the repository's finite Euler polynomials,
and hence the numerators and denominators of its finite rational tables,
are jointly entire when the norm base is positive. These facts alone do
not identify any two Euler products or construct an actual presentation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinContinuation

open Set Filter MeasureTheory Complex
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical Topology BigOperators

/-- The zeros of a nonzero entire function in one complex variable are
countable. The nonzero value rules out the identically-zero alternative. -/
theorem entire_zero_set_countable {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) {z : ℂ} (hz : f z ≠ 0) :
    (f ⁻¹' ({0} : Set ℂ)).Countable := by
  have hdiscrete : IsDiscrete (f ⁻¹' ({0} : Set ℂ)) := by
    apply (compl_mem_codiscrete_iff.mp ?_).2
    simpa only [preimage_compl] using hf.preimage_zero_mem_codiscrete hz
  letI : DiscreteTopology (f ⁻¹' ({0} : Set ℂ)) :=
    isDiscrete_iff_discreteTopology.mp hdiscrete
  exact TopologicalSpace.separableSpace_iff_countable.mp inferInstance

/-- Restricting a nonzero entire function to any vertical real line
leaves only a countable, hence null, set of zeros. -/
theorem entire_ne_zero_ae_vertical {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) {z : ℂ} (hz : f z ≠ 0) (σ : ℝ) :
    ∀ᵐ t : ℝ, f ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
  have hinj : Function.Injective (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) := by
    intro x y hxy
    have him := congrArg Complex.im hxy
    simpa using him
  have hc := (entire_zero_set_countable hf hz).preimage hinj
  simpa only [mem_preimage, mem_singleton_iff] using
    hc.ae_notMem (volume : Measure ℝ)

/-- A single nonzero complex value suffices for almost-everywhere
nonvanishing on the full three-dimensional vertical real parameter space.
The proof successively fixes the other coordinates at that value, then
uses Fubini to assemble the three one-variable statements. -/
theorem entire_triple_ne_zero_ae_vertical {f : (ℂ × ℂ × ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) {v : ℂ × ℂ × ℂ} (hv : f v ≠ 0)
    (σ : ℝ × ℝ × ℝ) :
    ∀ᵐ t : ℝ × (ℝ × ℝ),
      f ((σ.1 : ℂ) + (t.1 : ℂ) * I,
        (σ.2.1 : ℂ) + (t.2.1 : ℂ) * I,
        (σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) ≠ 0 := by
  have hc : Continuous f := continuousOn_univ.mp hf.continuousOn
  have hmap : Continuous (fun t : ℝ × (ℝ × ℝ) =>
      ((σ.1 : ℂ) + (t.1 : ℂ) * I,
        (σ.2.1 : ℂ) + (t.2.1 : ℂ) * I,
        (σ.2.2 : ℂ) + (t.2.2 : ℂ) * I)) := by
    fun_prop
  have hm : MeasurableSet {t : ℝ × (ℝ × ℝ) |
      f ((σ.1 : ℂ) + (t.1 : ℂ) * I,
        (σ.2.1 : ℂ) + (t.2.1 : ℂ) * I,
        (σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) ≠ 0} :=
    (isClosed_eq (hc.comp hmap) continuous_const).measurableSet.compl
  apply (Measure.ae_prod_iff_ae_ae hm).2
  have hs : AnalyticOnNhd ℂ (fun s : ℂ => f (s, v.2)) univ := by
    intro s _
    have hslice : AnalyticAt ℂ (fun x : ℂ => (x, v.2)) s :=
      analyticAt_id.prod analyticAt_const
    exact (hf (s, v.2) (mem_univ _)).comp (f := fun x : ℂ => (x, v.2)) hslice
  filter_upwards [entire_ne_zero_ae_vertical hs hv σ.1] with ts hts
  have hw : AnalyticOnNhd ℂ
      (fun w : ℂ => f ((σ.1 : ℂ) + (ts : ℂ) * I, w, v.2.2)) univ := by
    intro w _
    have hslice : AnalyticAt ℂ
        (fun x : ℂ => ((σ.1 : ℂ) + (ts : ℂ) * I, x, v.2.2)) w :=
      analyticAt_const.prod (analyticAt_id.prod analyticAt_const)
    exact (hf ((σ.1 : ℂ) + (ts : ℂ) * I, w, v.2.2) (mem_univ _)).comp
      (f := fun x : ℂ => ((σ.1 : ℂ) + (ts : ℂ) * I, x, v.2.2)) hslice
  have hmap₂ : Continuous (fun t : ℝ × ℝ =>
      ((σ.1 : ℂ) + (ts : ℂ) * I,
        (σ.2.1 : ℂ) + (t.1 : ℂ) * I,
        (σ.2.2 : ℂ) + (t.2 : ℂ) * I)) := by
    fun_prop
  have hm₂ : MeasurableSet {t : ℝ × ℝ |
      f ((σ.1 : ℂ) + (ts : ℂ) * I,
        (σ.2.1 : ℂ) + (t.1 : ℂ) * I,
        (σ.2.2 : ℂ) + (t.2 : ℂ) * I) ≠ 0} :=
    (isClosed_eq (hc.comp hmap₂) continuous_const).measurableSet.compl
  apply (Measure.ae_prod_iff_ae_ae hm₂).2
  filter_upwards [entire_ne_zero_ae_vertical hw hts σ.2.1] with tw htw
  have hz : AnalyticOnNhd ℂ (fun z : ℂ =>
      f ((σ.1 : ℂ) + (ts : ℂ) * I, (σ.2.1 : ℂ) + (tw : ℂ) * I, z)) univ := by
    intro z _
    have hslice : AnalyticAt ℂ
        (fun x : ℂ => ((σ.1 : ℂ) + (ts : ℂ) * I,
          (σ.2.1 : ℂ) + (tw : ℂ) * I, x)) z :=
      analyticAt_const.prod (analyticAt_const.prod analyticAt_id)
    exact (hf ((σ.1 : ℂ) + (ts : ℂ) * I,
      (σ.2.1 : ℂ) + (tw : ℂ) * I, z) (mem_univ _)).comp
      (f := fun x : ℂ => ((σ.1 : ℂ) + (ts : ℂ) * I,
        (σ.2.1 : ℂ) + (tw : ℂ) * I, x)) hslice
  exact entire_ne_zero_ae_vertical hz htw σ.2.2

/-- In particular, restricting to any real height box gives a null zero
set, with the original product volume and without a box-dependent premise. -/
theorem entire_triple_vertical_zero_measure {f : (ℂ × ℂ × ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) {v : ℂ × ℂ × ℂ} (hv : f v ≠ 0)
    (σ : ℝ × ℝ × ℝ) (box : Set (ℝ × (ℝ × ℝ))) :
    (volume.restrict box) {t : ℝ × (ℝ × ℝ) |
      f ((σ.1 : ℂ) + (t.1 : ℂ) * I,
        (σ.2.1 : ℂ) + (t.2.1 : ℂ) * I,
        (σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) = 0} = 0 := by
  have h := ae_restrict_of_ae (s := box) (entire_triple_ne_zero_ae_vertical hf hv σ)
  simpa only [ae_iff, Classical.not_not] using h

/-- The literal finite Laurent table is an entire function of all three
complex variables. Apply this separately to the numerator and denominator
of any `FiniteEulerRational`; no denominator nonvanishing is asserted. -/
theorem finiteEulerPolynomialValue_entire (A : FiniteEulerPolynomial)
    {q : ℝ} (hq : 0 < q) :
    AnalyticOnNhd ℂ
      (fun v : ℂ × ℂ × ℂ => finiteEulerPolynomialValue A q v.1 v.2.1 v.2.2)
      univ := by
  intro v _
  unfold finiteEulerPolynomialValue
  apply Finset.analyticAt_fun_sum
  intro e _
  apply analyticAt_const.mul
  have hs : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.1) v := analyticAt_fst
  have hw : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.2.1) v :=
    analyticAt_fst.comp analyticAt_snd
  have hz : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.2.2) v :=
    analyticAt_snd.comp analyticAt_snd
  have hlinear : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ =>
      -((e.1 : ℂ) * x.1 + (e.2.1 : ℂ) * x.2.1 + (e.2.2 : ℂ) * x.2.2)) v :=
    (((analyticAt_const.mul hs).add (analyticAt_const.mul hw)).add
      (analyticAt_const.mul hz)).neg
  have hq' : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  simp only [Complex.cpow_def_of_ne_zero hq']
  exact ((analyticAt_const :
    AnalyticAt ℂ (fun _ : ℂ × ℂ × ℂ => Complex.log (q : ℂ)) v).mul hlinear).cexp'

#print axioms entire_zero_set_countable
#print axioms entire_ne_zero_ae_vertical
#print axioms entire_triple_ne_zero_ae_vertical
#print axioms entire_triple_vertical_zero_measure
#print axioms finiteEulerPolynomialValue_entire

end HeckeSkeleton.HighBinContinuation
