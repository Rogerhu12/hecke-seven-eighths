import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualReflectionRows
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.FixedLineKernel
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.PrimitiveReflectionCalibration

/-!
# The genuine ordinary reflection on one common positive measure

The common children are literal normalized power-window models of the
original row family. The genuine functional equation supplies every
complex row identity. Its row-dependent contour choice is retained only
in a scalar coefficient on the two fixed branches. Weighted Cauchy then
gives the full original moment on one common positive measure.

The scalar density majorant is kept visible so the uniform analytic
envelope can be inserted without hiding a moment estimate. Neither the
parent energy bound nor a child moment bound is an input.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeConductorNorm
open HeckePort.Moments HeckePort.Moments.ReflectionMass
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]

/-- Both the dyadic exponent and the contour line are common to all
original rows of this actual child. -/
def Node.fixedLineReflectionChild (node : Node K ω ψ) (first : Bool)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder : ℕ) (x : (ℕ × Bool) × ℝ) :
    Node K ω ψ :=
  node.normalizedOrdinaryPowerChildNode first (reflectionFixedLine x.1.2)
    (-x.2) (reflectionDyadicExponent U x.1.1) E0 hE0 childOrder

theorem Node.fixedLineReflectionChild_width (node : Node K ω ψ) (first : Bool)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder : ℕ) (x : (ℕ × Bool) × ℝ) :
    (node.fixedLineReflectionChild first U E0 hE0 childOrder x).width = node.width := rfl

def actualReflectionSelectedLine (d : MomentData K ω ψ) (a : RealParameters)
    (first : Bool) (U : ℝ) (u : NonzeroIdeal K) (j : ℕ) : Bool :=
  reflectionLineChoice ((2 : ℝ) ^ j * U ^ (if first then a.n₁ else a.n₂) /
    heckeConductorScale K (d.plainBackground * d.rowCharacter u))

/-- The actual normalized density uses the complete pruned deletion set
and actual conductor of this original row. -/
def actualReflectionDensity
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (d : MomentData K ω ψ) (a : RealParameters) (first : Bool)
    (extra : NonzeroIdeal K → NonzeroIdeal K) (V : NonzeroIdeal K → SmoothAnnularTest)
    (U E0 : ℝ) (childOrder : ℕ) (u : NonzeroIdeal K) (j : ℕ) (line : Bool) : ℝ → ℂ :=
  let χ := d.plainBackground * d.rowCharacter u
  normalizedOrdinaryReflectionDensity K E0 childOrder d.geometry.slotCount χ (V u)
    (idealCoefficient (primeCoefficient K χ)) (idealCoefficient (primeCoefficient K χ⁻¹))
    (rowRestorationDeletion S d extra u) (heckeConductorScale K χ)
    (U ^ (if first then a.n₁ else a.n₂)) ((2 : ℝ) ^ j) (reflectionFixedLine line)

/-- Actual child energies are numerically integrable in the common
kernel. No measurable structure on the type of models is used. -/
theorem Node.fixedLineReflectionChild_integrable
    (node : Node K ω ψ) (first : Bool) (U E0 : ℝ) (hU : 0 < U)
    (hE0 : 1 ≤ E0) (childOrder cutoff : ℕ) (weight : ℝ → ℝ)
    (hw : ∀ t, 0 ≤ weight t) (hi : Integrable weight) :
    Integrable (fun x =>
      (node.fixedLineReflectionChild first U E0 hE0 childOrder x).normalizedEnergy U 0)
      (reflectionCommonKernel volume weight cutoff) := by
  letI := rowEnergyKernel_finite volume hw hi
  apply reflectionCommonKernel_integrable
  intro b _hb
  have h := normalizedOrdinaryPowerChild_energy_integrable node.data node.parameters first
    (reflectionFixedLine b.2) (reflectionDyadicExponent U b.1) U 0 E0 hE0 childOrder
    hU (rowEnergyKernel volume weight)
  simpa only [Node.fixedLineReflectionChild, Node.normalizedOrdinaryPowerChildNode,
    Node.normalizedEnergy, Node.ordinary_energy, Node.width, Node.ordinary,
    ordinaryPowerParameters] using h.div_const (U ^ node.width)

/-- Genuine reflection of the original ordinary moment. Every premise
is a primitive row/profile/scale fact or the actual scalar Mellin-density
majorant; the integral energy inequality is produced here. -/
theorem pairedEnergy_reflection_commonKernel
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (d : MomentData K ω ψ) (a : RealParameters) (first : Bool)
    (extra : NonzeroIdeal K → NonzeroIdeal K) (V : NonzeroIdeal K → SmoothAnnularTest)
    {δ U E0 Ymax : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 4)
    (hU : 1 < U) (hE0 : 1 ≤ E0) (hYmax : 0 < Ymax) (childOrder cutoff : ℕ)
    (hmask : ∀ u ∈ pairedRows d a U, ∀ I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val)))
    (hcharacter : ∀ u ∈ pairedRows d a U, ∀ t : ℝ,
      d.plainBackground * d.rowCharacter u ≠ heckeNormTwist K t)
    (hprofile : ∀ u ∈ pairedRows d a U,
      (V u).toFun = (if first then d.plainTest₁ else d.plainTest₂).profile u 0)
    (hscale : ∀ u ∈ pairedRows d a U, ∀ D ∈ (rowRestorationDeletion S d extra u).powerset,
      ∀ H : SmoothIdeal (rowRestorationDeletion S d extra u),
        heckeConductorScale K (d.plainBackground * d.rowCharacter u) *
          (Ideal.absNorm (∏ P ∈ D, P) : ℝ) /
            (U ^ (if first then a.n₁ else a.n₂) * inorm H.val) ≤ Ymax)
    (weight : ℝ → ℝ) (hm : Measurable weight) (hw : ∀ t, 0 ≤ weight t)
    (hi : Integrable weight)
    (hdensity : ∀ j ∈ Finset.range (cutoff + 1), ∀ u ∈ pairedRows d a U, ∀ t,
      ‖actualReflectionDensity S d a first extra V U E0 childOrder u j
        (actualReflectionSelectedLine d a first U u j) t‖ ≤ weight t) :
    (Node.ordinary d a).normalizedEnergy U 0 ≤
      2 * rowRestorationEnergy true S (Node.ordinary d a) extra V
        (if first then d.plainTest₂ else d.plainTest₁) δ U
        (if first then a.n₁ else a.n₂) (if first then a.n₂ else a.n₁) cutoff +
      ∫ x, ((Node.ordinary d a).fixedLineReflectionChild first U E0 hE0 childOrder x).normalizedEnergy
        U 0 ∂reflectionCommonKernel volume weight cutoff := by
  have hU0 : 0 < U := zero_lt_one.trans hU
  let rows := pairedRows d a U
  let selected := actualReflectionSelectedLine d a first U
  let long := if first then a.n₁ else a.n₂
  let short := if first then a.n₂ else a.n₁
  let Wshort := if first then d.plainTest₂ else d.plainTest₁
  let parent : NonzeroIdeal K → ℂ := fun u =>
    plainPolynomial d d.plainTest₁ u (U ^ a.n₁) 0 *
      plainPolynomial d d.plainTest₂ u (U ^ a.n₂) 0 * slotProduct d u U 0
  let rest : NonzeroIdeal K → ℂ := fun u =>
    rowRestorationPiece true S d extra V δ U long cutoff u *
      plainPolynomial d Wshort u (U ^ short) 0 * slotProduct d u U 0
  let density := actualReflectionDensity S d a first extra V U E0 childOrder
  let f : ℕ → Bool → NonzeroIdeal K → ℝ → ℂ := fun j line u =>
    normalizedOrdinaryDualRow d a first (reflectionFixedLine line)
      (reflectionDyadicExponent U j) U 0 E0 childOrder u
  have hphase (u : NonzeroIdeal K) (hu : u ∈ rows) :
      ∃ G : ℂ, ‖G‖ = 1 ∧ parent u = G * rest u +
        ∑ j ∈ Finset.range (cutoff + 1), ∫ t : ℝ,
          (G * density u j (selected u j) t) * f j (selected u j) u t := by
    have h := pairedRow_commonFrequency_normalized hcomplex S d a first extra V u
      (hmask u hu) (hcharacter u hu) (hprofile u hu) hδ hδsmall hU0 hYmax hE0 childOrder
      cutoff (hscale u hu) (fun j => reflectionFixedLine (selected u j))
      (reflectionDyadicExponent U)
      (fun j _ => reflectionFixedLine_bounds (selected u j))
      (fun j _ => reflectionDyadicExponent_scale hU j)
    obtain ⟨G, hG, h⟩ := h
    refine ⟨G, hG, ?_⟩
    have hs : (if first then plainPolynomial d d.plainTest₂ u (U ^ a.n₂) 0
        else plainPolynomial d d.plainTest₁ u (U ^ a.n₁) 0) =
        plainPolynomial d Wshort u (U ^ short) 0 := by
      cases first <;> rfl
    simpa only [parent, rest, long, density, actualReflectionDensity, f, hs,
      mul_assoc] using h
  let G : NonzeroIdeal K → ℂ := fun u => if hu : u ∈ rows then (hphase u hu).choose else 1
  have hG (u : NonzeroIdeal K) (hu : u ∈ rows) : ‖G u‖ = 1 := by
    dsimp only [G]
    rw [dif_pos hu]
    exact (hphase u hu).choose_spec.1
  have hparent (u : NonzeroIdeal K) (hu : u ∈ rows) : parent u = G u * rest u +
      ∑ j ∈ Finset.range (cutoff + 1), ∫ t : ℝ,
        (G u * density u j (selected u j) t) * f j (selected u j) u t := by
    dsimp only [G]
    rw [dif_pos hu]
    exact (hphase u hu).choose_spec.2
  let coefficient : ℕ → Bool → NonzeroIdeal K → ℝ → ℂ :=
    fun j line u t => G u * density u j line t
  letI := kernelWeightedMeasure_finite volume hw hi
  have hf (j : ℕ) (_hj : j ∈ Finset.range (cutoff + 1)) (line : Bool)
      (u : NonzeroIdeal K) (_hu : u ∈ rows) :
      MemLp (f j line u) 2 (kernelWeightedMeasure volume weight) :=
    normalizedOrdinaryDualRow_memLp d a first (reflectionFixedLine line)
      (reflectionDyadicExponent U j) U 0 E0 hE0 childOrder hU0 u _
  have hint (j : ℕ) (_hj : j ∈ Finset.range (cutoff + 1))
      (u : NonzeroIdeal K) (_hu : u ∈ rows) :
      Integrable (fun t => coefficient j (selected u j) u t * f j (selected u j) u t) := by
    have h := integrable_normalizedOrdinaryDualRow_integrand hcomplex d a first
      (reflectionFixedLine (selected u j)) (reflectionDyadicExponent U j) U 0 E0 hE0 childOrder
      hU0 u (d.plainBackground * d.rowCharacter u) (V u)
      (heckeIdealCoeff_for_deletion _) (heckeIdealCoeff_for_deletion _)
      (rowRestorationDeletion S d extra u) (rowRestorationDeletion_prime S d extra u)
      hδ (conductorScale_pos K _) (Real.rpow_pos_of_pos hU0 long)
      (pow_pos (by norm_num : (0 : ℝ) < 2) j)
      (reflectionFixedLine_bounds (selected u j)).1
      (reflectionFixedLine_bounds (selected u j)).2
    simpa only [coefficient, density, actualReflectionDensity, f, long, mul_assoc]
      using h.const_mul (G u)
  have hc (j : ℕ) (hj : j ∈ Finset.range (cutoff + 1))
      (u : NonzeroIdeal K) (hu : u ∈ rows) (t : ℝ) :
      ‖coefficient j (selected u j) u t‖ ≤ weight t := by
    dsimp only [coefficient]
    rw [norm_mul, hG u hu, one_mul]
    exact hdensity j hj u hu t
  have hmain := fixedLine_rows_energy_le volume cutoff rows weight hm hw hi selected
    coefficient f hf hint hc parent (fun u => G u * rest u) hparent
  have htail : (∑ u ∈ rows, ‖G u * rest u‖ ^ 2) = ∑ u ∈ rows, ‖rest u‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [norm_mul, hG u hu, one_mul]
  rw [htail] at hmain
  let value : (ℕ × Bool) × ℝ → ℝ := fun x =>
    ((Node.ordinary d a).fixedLineReflectionChild first U E0 hE0 childOrder x).energy U 0
  have hvalue (b : ℕ × Bool) (t : ℝ) :
      (∑ u ∈ rows, ‖f b.1 b.2 u t‖ ^ 2) = value (b, t) := by
    simpa only [value, Node.fixedLineReflectionChild, Node.normalizedOrdinaryPowerChildNode,
      Node.ordinary_energy, Node.ordinary, rows, f] using
      normalizedOrdinaryDualRow_energy d a first (reflectionFixedLine b.2)
        (reflectionDyadicExponent U b.1) U 0 E0 hE0 childOrder t
  simp_rw [hvalue] at hmain
  letI := rowEnergyKernel_finite volume hw hi
  have hv (b : ℕ × Bool) (_hb : b ∈ reflectionBranches cutoff) :
      Integrable (fun t => value (b, t)) (rowEnergyKernel volume weight) := by
    simpa only [value, Node.fixedLineReflectionChild, Node.normalizedOrdinaryPowerChildNode,
      Node.ordinary_energy, Node.ordinary] using
      normalizedOrdinaryPowerChild_energy_integrable d a first (reflectionFixedLine b.2)
        (reflectionDyadicExponent U b.1) U 0 E0 hE0 childOrder hU0 (rowEnergyKernel volume weight)
  rw [← integral_reflectionCommonKernel volume weight cutoff value hv] at hmain
  have hnormalized := div_le_div_of_nonneg_right hmain
    (Real.rpow_pos_of_pos hU0 (a.m + a.q)).le
  have hnormalizedValue (x : (ℕ × Bool) × ℝ) :
      ((Node.ordinary d a).fixedLineReflectionChild first U E0 hE0 childOrder x).normalizedEnergy
          U 0 = value x / U ^ (a.m + a.q) := rfl
  simp_rw [hnormalizedValue]
  rw [integral_div]
  simpa only [Node.normalizedEnergy, Node.ordinary_energy, Node.width, Node.ordinary,
    pairedEnergy, parent, rowRestorationEnergy, rest, rows, long, short, Wshort,
    add_div, mul_div_assoc] using hnormalized

/-- The whole-series branch is an exact equality of the original
normalized moment and the literal restoration terminal energy. -/
theorem pairedEnergy_wholeRestoration_eq
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (d : MomentData K ω ψ) (a : RealParameters) (first : Bool)
    (extra : NonzeroIdeal K → NonzeroIdeal K) (V : NonzeroIdeal K → SmoothAnnularTest)
    {δ U : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 4) (hU : 0 < U) (cutoff : ℕ)
    (hmask : ∀ u ∈ pairedRows d a U, ∀ I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val)))
    (hcharacter : ∀ u ∈ pairedRows d a U, ∀ t : ℝ,
      d.plainBackground * d.rowCharacter u ≠ heckeNormTwist K t)
    (hprofile : ∀ u ∈ pairedRows d a U,
      (V u).toFun = (if first then d.plainTest₁ else d.plainTest₂).profile u 0) :
    (Node.ordinary d a).normalizedEnergy U 0 =
      rowRestorationEnergy false S (Node.ordinary d a) extra V
        (if first then d.plainTest₂ else d.plainTest₁) δ U
        (if first then a.n₁ else a.n₂) (if first then a.n₂ else a.n₁) cutoff := by
  unfold Node.normalizedEnergy rowRestorationEnergy
  rw [Node.ordinary_energy]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  obtain ⟨G, hG, h⟩ := pairedRow_wholeReflection hcomplex S d a first extra V u
    (hmask u hu) (hcharacter u hu) (hprofile u hu) hδ hδsmall hU cutoff
  change ‖_‖ ^ 2 = ‖_‖ ^ 2
  rw [h]
  cases first <;> simp only [Bool.false_eq_true, if_false, if_true, norm_mul, hG, one_mul]

end HeckeSkeleton.Moments.EngineInduction
