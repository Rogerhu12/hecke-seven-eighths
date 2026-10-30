import HeckeGeneral.Analysis.RowwiseIntervalSobolev
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Positive anchored integral functionals for a rectangular Sobolev bound.
All majorants below are actual integrals of derivative-square energies.
No supremum bound or arbitrary majorant is assumed. -/

noncomputable section

namespace HeckeGeneral.Analysis

open MeasureTheory Set
open scoped BigOperators Topology

def anchoredIntegral (a b : ℝ) (g : ℝ → ℝ) : ℝ :=
  g a + ∫ x in Icc a b, g x

theorem anchoredIntegral_eq_interval {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) :
    anchoredIntegral a b g = g a + ∫ x in a..b, g x := by
  rw [anchoredIntegral, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

theorem anchoredIntegral_nonneg (a b : ℝ) (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x) :
    0 ≤ anchoredIntegral a b g := by
  exact add_nonneg (hg a) (integral_nonneg (fun x => hg x))

theorem anchoredIntegral_mono {a b : ℝ} (hab : a ≤ b)
    {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h)
    (hle : ∀ x ∈ Icc a b, g x ≤ h x) :
    anchoredIntegral a b g ≤ anchoredIntegral a b h := by
  apply add_le_add (hle a ⟨le_rfl, hab⟩)
  exact setIntegral_mono_on (hg.integrableOn_Icc) (hh.integrableOn_Icc)
    measurableSet_Icc hle

theorem anchoredIntegral_add (a b : ℝ) {g h : ℝ → ℝ}
    (hg : Continuous g) (hh : Continuous h) :
    anchoredIntegral a b (fun x => g x + h x) =
      anchoredIntegral a b g + anchoredIntegral a b h := by
  simp only [anchoredIntegral, integral_add hg.integrableOn_Icc hh.integrableOn_Icc]
  ring

theorem anchoredIntegral_const_mul (a b c : ℝ) {g : ℝ → ℝ} :
    anchoredIntegral a b (fun x => c * g x) = c * anchoredIntegral a b g := by
  simp only [anchoredIntegral, integral_const_mul]
  ring

theorem anchoredIntegral_const {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    anchoredIntegral a b (fun _ => c) = (1 + b - a) * c := by
  rw [anchoredIntegral_eq_interval hab]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem anchoredIntegral_finsetSum {ι : Type*} (F : Finset ι) (a b : ℝ)
    (g : ι → ℝ → ℝ) (hg : ∀ i ∈ F, Continuous (g i)) :
    anchoredIntegral a b (fun x => ∑ i ∈ F, g i x) =
      ∑ i ∈ F, anchoredIntegral a b (g i) := by
  simp only [anchoredIntegral]
  rw [integral_finsetSum F (fun i hi => (hg i hi).integrableOn_Icc)]
  exact (Finset.sum_add_distrib).symm

theorem continuous_anchoredIntegral
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    (a b : ℝ) {g : X → ℝ → ℝ} (hg : Continuous g.uncurry) :
    Continuous (fun p => anchoredIntegral a b (g p)) := by
  exact (hg.comp (continuous_id.prodMk continuous_const)).add
    (continuous_parametric_integral_of_continuous hg isCompact_Icc)

theorem norm_sq_le_anchoredIntegral (f f' : ℝ → ℂ) {a b x : ℝ}
    (hx : x ∈ Icc a b) (hderiv : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hcont : Continuous f') :
    ‖f x‖ ^ 2 ≤ anchoredIntegral a b (fun t => ‖f t‖ ^ 2 + ‖f' t‖ ^ 2) := by
  rw [anchoredIntegral_eq_interval (hx.1.trans hx.2)]
  have h := norm_sq_le_endpoint_add_integral f f' hx hderiv hcont.continuousOn
  nlinarith [sq_nonneg ‖f' a‖]

/-- Integrate log-scale first, then real and imaginary Mellin parameters. -/
def boxAnchoredIntegral (a b c d e f : ℝ) (g : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  anchoredIntegral e f (fun z => anchoredIntegral c d
    (fun y => anchoredIntegral a b (fun x => g x y z)))

theorem continuous_inner_anchoredIntegral (a b : ℝ) {g : ℝ → ℝ → ℝ → ℝ}
    (hg : Continuous (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) :
    Continuous (fun p : ℝ × ℝ => anchoredIntegral a b (fun x => g x p.1 p.2)) := by
  apply continuous_anchoredIntegral
  exact hg.comp (continuous_snd.prodMk (continuous_fst.fst.prodMk continuous_fst.snd))

theorem continuous_middle_anchoredIntegral (a b c d : ℝ) {g : ℝ → ℝ → ℝ → ℝ}
    (hg : Continuous (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) :
    Continuous (fun z => anchoredIntegral c d
      (fun y => anchoredIntegral a b (fun x => g x y z))) := by
  apply continuous_anchoredIntegral
  exact (continuous_inner_anchoredIntegral a b hg).comp
    (continuous_snd.prodMk continuous_fst)

theorem boxAnchoredIntegral_nonneg (a b c d e f : ℝ) (g : ℝ → ℝ → ℝ → ℝ)
    (hg : ∀ x y z, 0 ≤ g x y z) : 0 ≤ boxAnchoredIntegral a b c d e f g := by
  apply anchoredIntegral_nonneg
  intro z
  apply anchoredIntegral_nonneg
  intro y
  exact anchoredIntegral_nonneg a b _ (fun x => hg x y z)

theorem boxAnchoredIntegral_mono {a b c d e f : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f)
    {g h : ℝ → ℝ → ℝ → ℝ}
    (hg : Continuous (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2))
    (hh : Continuous (fun p : ℝ × ℝ × ℝ => h p.1 p.2.1 p.2.2))
    (hle : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, ∀ z ∈ Icc e f, g x y z ≤ h x y z) :
    boxAnchoredIntegral a b c d e f g ≤ boxAnchoredIntegral a b c d e f h := by
  apply anchoredIntegral_mono hef (continuous_middle_anchoredIntegral a b c d hg)
    (continuous_middle_anchoredIntegral a b c d hh)
  intro z hz
  apply anchoredIntegral_mono hcd
    ((continuous_inner_anchoredIntegral a b hg).comp (continuous_id.prodMk continuous_const))
    ((continuous_inner_anchoredIntegral a b hh).comp (continuous_id.prodMk continuous_const))
  intro y hy
  apply anchoredIntegral_mono hab
    (hg.comp (continuous_id.prodMk continuous_const))
    (hh.comp (continuous_id.prodMk continuous_const))
  exact fun x hx => hle x hx y hy z hz

theorem boxAnchoredIntegral_const {a b c d e f : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f) (M : ℝ) :
    boxAnchoredIntegral a b c d e f (fun _ _ _ => M) =
      (1 + f - e) * ((1 + d - c) * ((1 + b - a) * M)) := by
  simp only [boxAnchoredIntegral, anchoredIntegral_const hab,
    anchoredIntegral_const hcd, anchoredIntegral_const hef]

theorem boxAnchoredIntegral_le_const {a b c d e f : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hg : Continuous (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2))
    (M : ℝ) (hM : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, ∀ z ∈ Icc e f, g x y z ≤ M) :
    boxAnchoredIntegral a b c d e f g ≤
      (1 + f - e) * ((1 + d - c) * ((1 + b - a) * M)) := by
  exact (boxAnchoredIntegral_mono hab hcd hef hg continuous_const hM).trans_eq
    (boxAnchoredIntegral_const hab hcd hef M)

theorem boxAnchoredIntegral_finsetSum {ι : Type*} (F : Finset ι)
    (a b c d e f : ℝ) (g : ι → ℝ → ℝ → ℝ → ℝ)
    (hg : ∀ i ∈ F, Continuous (fun p : ℝ × ℝ × ℝ => g i p.1 p.2.1 p.2.2)) :
    boxAnchoredIntegral a b c d e f (fun x y z => ∑ i ∈ F, g i x y z) =
      ∑ i ∈ F, boxAnchoredIntegral a b c d e f (g i) := by
  have hi y z := anchoredIntegral_finsetSum F a b (fun i x => g i x y z)
    (fun i hI => (hg i hI).comp (continuous_id.prodMk
      (show Continuous (fun _ : ℝ => (y, z)) from continuous_const)))
  have hm z := anchoredIntegral_finsetSum F c d
    (fun i y => anchoredIntegral a b (fun x => g i x y z))
    (fun i hI => (continuous_inner_anchoredIntegral a b (hg i hI)).comp
      (continuous_id.prodMk continuous_const))
  simp only [boxAnchoredIntegral]
  simp_rw [hi, hm]
  exact anchoredIntegral_finsetSum F e f _
    (fun i hI => continuous_middle_anchoredIntegral a b c d (hg i hI))

abbrev SixTestFamily := Fin 2 → Fin 3 → ℝ → ℝ → ℝ → ℂ

def threeTestEnergy (g : SixTestFamily) (i : Fin 2) (x y z : ℝ) : ℝ :=
  ‖g i 0 x y z‖ ^ 2 + 2 * ‖g i 1 x y z‖ ^ 2 + ‖g i 2 x y z‖ ^ 2

def sixTestEnergy (g : SixTestFamily) (x y z : ℝ) : ℝ :=
  threeTestEnergy g 0 x y z + threeTestEnergy g 1 x y z

theorem continuous_threeTestEnergy (g : SixTestFamily)
    (hg : ∀ i m, Continuous (fun p : ℝ × ℝ × ℝ => g i m p.1 p.2.1 p.2.2))
    (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ × ℝ => threeTestEnergy g i p.1 p.2.1 p.2.2) :=
  (((hg i 0).norm.pow 2).add (continuous_const.mul ((hg i 1).norm.pow 2))).add
    ((hg i 2).norm.pow 2)

theorem continuous_sixTestEnergy (g : SixTestFamily)
    (hg : ∀ i m, Continuous (fun p : ℝ × ℝ × ℝ => g i m p.1 p.2.1 p.2.2)) :
    Continuous (fun p : ℝ × ℝ × ℝ => sixTestEnergy g p.1 p.2.1 p.2.2) :=
  (continuous_threeTestEnergy g hg 0).add (continuous_threeTestEnergy g hg 1)

/-- The six tests suffice. Differentiate in the order imaginary parameter,
real parameter, then log scale. No parameter derivative of an Euler test
is required. The only phase is the literal i in the imaginary derivative. -/
theorem norm_sq_le_sixTest_box
    (g : SixTestFamily)
    (hg : ∀ i m, Continuous (fun p : ℝ × ℝ × ℝ => g i m p.1 p.2.1 p.2.2))
    (hxderiv : ∀ m x y z, HasDerivAt (fun u => g 0 m u y z) (g 1 m x y z) x)
    (hy0 : ∀ x y z, HasDerivAt (fun v => g 0 0 x v z) (g 0 1 x y z) y)
    (hy1 : ∀ x y z, HasDerivAt (fun v => g 0 1 x v z) (g 0 2 x y z) y)
    (hz0 : ∀ x y z, HasDerivAt (fun w => g 0 0 x y w) (Complex.I * g 0 1 x y z) z)
    {a b c d e f x y z : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (hz : z ∈ Icc e f) :
    ‖g 0 0 x y z‖ ^ 2 ≤ boxAnchoredIntegral a b c d e f (sixTestEnergy g) := by
  have hcX i m y z : Continuous (fun u => g i m u y z) :=
    (hg i m).comp (continuous_id.prodMk
      (show Continuous (fun _ : ℝ => (y, z)) from continuous_const))
  have hcY i m x z : Continuous (fun v => g i m x v z) :=
    (hg i m).comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  have hcZ i m x y : Continuous (fun w => g i m x y w) :=
    (hg i m).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hX y z : threeTestEnergy g 0 x y z ≤
      anchoredIntegral a b (fun u => sixTestEnergy g u y z) := by
    have h0 := norm_sq_le_anchoredIntegral (fun u => g 0 0 u y z)
      (fun u => g 1 0 u y z) hx (fun u _ => hxderiv 0 u y z) (hcX 1 0 y z)
    have h1 := norm_sq_le_anchoredIntegral (fun u => g 0 1 u y z)
      (fun u => g 1 1 u y z) hx (fun u _ => hxderiv 1 u y z) (hcX 1 1 y z)
    have h2 := norm_sq_le_anchoredIntegral (fun u => g 0 2 u y z)
      (fun u => g 1 2 u y z) hx (fun u _ => hxderiv 2 u y z) (hcX 1 2 y z)
    let E : Fin 3 → ℝ → ℝ := fun m u => ‖g 0 m u y z‖ ^ 2 + ‖g 1 m u y z‖ ^ 2
    have hEc m : Continuous (E m) := ((hcX 0 m y z).norm.pow 2).add ((hcX 1 m y z).norm.pow 2)
    have heq : anchoredIntegral a b (fun u => sixTestEnergy g u y z) =
        anchoredIntegral a b (E 0) + 2 * anchoredIntegral a b (E 1) +
          anchoredIntegral a b (E 2) := by
      have hfun : (fun u => sixTestEnergy g u y z) =
          (fun u => E 0 u + 2 * E 1 u + E 2 u) := by
        funext u
        simp only [sixTestEnergy, threeTestEnergy, E]
        ring
      rw [hfun, anchoredIntegral_add a b
        (g := fun u => E 0 u + 2 * E 1 u) (h := E 2)
        ((hEc 0).add (continuous_const.mul (hEc 1))) (hEc 2),
        anchoredIntegral_add a b (g := E 0) (h := fun u => 2 * E 1 u)
          (hEc 0) (continuous_const.mul (hEc 1)),
        anchoredIntegral_const_mul]
    rw [heq]
    change ‖g 0 0 x y z‖ ^ 2 + 2 * ‖g 0 1 x y z‖ ^ 2 + ‖g 0 2 x y z‖ ^ 2 ≤ _
    dsimp [E]
    linarith
  have hY w : ‖g 0 0 x y w‖ ^ 2 + ‖g 0 1 x y w‖ ^ 2 ≤
      anchoredIntegral c d (fun v => threeTestEnergy g 0 x v w) := by
    have h0 := norm_sq_le_anchoredIntegral (fun v => g 0 0 x v w)
      (fun v => g 0 1 x v w) hy (fun v _ => hy0 x v w) (hcY 0 1 x w)
    have h1 := norm_sq_le_anchoredIntegral (fun v => g 0 1 x v w)
      (fun v => g 0 2 x v w) hy (fun v _ => hy1 x v w) (hcY 0 2 x w)
    have heq : anchoredIntegral c d (fun v => threeTestEnergy g 0 x v w) =
        anchoredIntegral c d (fun v => ‖g 0 0 x v w‖ ^ 2 + ‖g 0 1 x v w‖ ^ 2) +
        anchoredIntegral c d (fun v => ‖g 0 1 x v w‖ ^ 2 + ‖g 0 2 x v w‖ ^ 2) := by
      rw [← anchoredIntegral_add c d
        (g := fun v => ‖g 0 0 x v w‖ ^ 2 + ‖g 0 1 x v w‖ ^ 2)
        (h := fun v => ‖g 0 1 x v w‖ ^ 2 + ‖g 0 2 x v w‖ ^ 2)
        (((hcY 0 0 x w).norm.pow 2).add ((hcY 0 1 x w).norm.pow 2))
        (((hcY 0 1 x w).norm.pow 2).add ((hcY 0 2 x w).norm.pow 2))]
      congr 1
      funext v
      simp only [threeTestEnergy]
      ring
    rw [heq]
    exact add_le_add h0 h1
  have hZ := norm_sq_le_anchoredIntegral (fun w => g 0 0 x y w)
    (fun w => Complex.I * g 0 1 x y w) hz (fun w _ => hz0 x y w)
    (continuous_const.mul (hcZ 0 1 x y))
  simp only [norm_mul, Complex.norm_I, one_mul] at hZ
  apply hZ.trans
  apply anchoredIntegral_mono (hz.1.trans hz.2)
    (((hcZ 0 0 x y).norm.pow 2).add ((hcZ 0 1 x y).norm.pow 2))
    (continuous_middle_anchoredIntegral a b c d (continuous_sixTestEnergy g hg))
  intro w _
  apply (hY w).trans
  apply anchoredIntegral_mono (hy.1.trans hy.2)
    ((continuous_threeTestEnergy g hg 0).comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const)))
    ((continuous_inner_anchoredIntegral a b (continuous_sixTestEnergy g hg)).comp
      (continuous_id.prodMk continuous_const))
  exact fun v _ => hX v w

/-- Explicit rowwise majorants, with row sums controlled by the six genuine
derivative-square moments. The constants are the rectangle lengths only. -/
theorem exists_sixTest_box_majorants {ι : Type*} (F : Finset ι)
    (g : ι → SixTestFamily)
    (hg : ∀ q i m, Continuous (fun p : ℝ × ℝ × ℝ => g q i m p.1 p.2.1 p.2.2))
    (hxderiv : ∀ q m x y z, HasDerivAt (fun u => g q 0 m u y z) (g q 1 m x y z) x)
    (hy0 : ∀ q x y z, HasDerivAt (fun v => g q 0 0 x v z) (g q 0 1 x y z) y)
    (hy1 : ∀ q x y z, HasDerivAt (fun v => g q 0 1 x v z) (g q 0 2 x y z) y)
    (hz0 : ∀ q x y z, HasDerivAt (fun w => g q 0 0 x y w) (Complex.I * g q 0 1 x y z) z)
    {a b c d e f : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f)
    (M : ℝ)
    (hM : ∀ i m, ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, ∀ z ∈ Icc e f,
      (∑ q ∈ F, ‖g q i m x y z‖ ^ 2) ≤ M) :
    ∃ B : ι → ℝ, (∀ q, 0 ≤ B q) ∧
      (∀ q, ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, ∀ z ∈ Icc e f,
        ‖g q 0 0 x y z‖ ^ 2 ≤ B q) ∧
      (∑ q ∈ F, B q) ≤ (1 + f - e) * ((1 + d - c) * ((1 + b - a) * (8 * M))) := by
  refine ⟨fun q => boxAnchoredIntegral a b c d e f (sixTestEnergy (g q)), ?_, ?_, ?_⟩
  · intro q
    apply boxAnchoredIntegral_nonneg
    intro x y z
    simp only [sixTestEnergy, threeTestEnergy]
    positivity
  · intro q x hx y hy z hz
    exact norm_sq_le_sixTest_box (g q) (hg q) (hxderiv q) (hy0 q) (hy1 q) (hz0 q) hx hy hz
  · rw [← boxAnchoredIntegral_finsetSum F a b c d e f
      (fun q => sixTestEnergy (g q)) (fun q _ => continuous_sixTestEnergy (g q) (hg q))]
    apply boxAnchoredIntegral_le_const hab hcd hef
      (continuous_finsetSum F (fun q _ => continuous_sixTestEnergy (g q) (hg q)))
    intro x hx y hy z hz
    have h00 := hM 0 0 x hx y hy z hz
    have h01 := hM 0 1 x hx y hy z hz
    have h02 := hM 0 2 x hx y hy z hz
    have h10 := hM 1 0 x hx y hy z hz
    have h11 := hM 1 1 x hx y hy z hz
    have h12 := hM 1 2 x hx y hy z hz
    simp only [sixTestEnergy, threeTestEnergy, Finset.sum_add_distrib, ← Finset.mul_sum]
    linarith

end HeckeGeneral.Analysis
