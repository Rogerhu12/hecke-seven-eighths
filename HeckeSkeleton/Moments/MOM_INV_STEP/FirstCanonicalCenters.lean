import HeckeSkeleton.Moments.MOM_INV_STEP.FirstOuterCenters

/-!
# The fixed first center grid used by the canonical step

The grid uses the uniform parent cap and the fixed allowance one. Its
counting constant is chosen before the base and every arithmetic source.
The fine mesh only proves that the same fixed grid contains every real
extracted factor. The assignment itself is the original deterministic
dyadic assignment from `FirstOuterCenters.canonical`.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstCanonicalCenters

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open FirstParentRows
open scoped Classical

abbrev Index (Z A : ℝ) := FirstParentCentering.CenterIndex Z A 1

abbrev grid (Z A : ℝ) : Index Z A → {r : ℝ // 0 < r} :=
  FirstParentCentering.grid Z A 1

theorem grid_one_le (Z A : ℝ) (k : Index Z A) : 1 ≤ (grid Z A k).val :=
  FirstParentCentering.grid_one_le Z A 1 k

def countConstant (A pi : ℝ) (hA : 1 ≤ A) (hpi : 0 < pi) : ℝ :=
  Classical.choose (FirstParentCentering.exists_grid_count_bound A 1 pi (by linarith) hpi)

theorem countConstant_one_le (A pi : ℝ) (hA : 1 ≤ A) (hpi : 0 < pi) :
    1 ≤ countConstant A pi hA hpi :=
  (Classical.choose_spec
    (FirstParentCentering.exists_grid_count_bound A 1 pi (by linarith) hpi)).1

theorem card_le (A pi : ℝ) (hA : 1 ≤ A) (hpi : 0 < pi) (Z : ℝ) (hZ : 1 ≤ Z) :
    (Fintype.card (Index Z A) : ℝ) ≤ countConstant A pi hA hpi * Z ^ pi :=
  (Classical.choose_spec
    (FirstParentCentering.exists_grid_count_bound A 1 pi (by linarith) hpi)).2 Z hZ

theorem fixed_width (Z h : ℝ) (hZ : 1 ≤ Z) (hh : h ≤ 1) (hwidth : 2 ≤ Z ^ h) :
    2 ≤ Z ^ (1 : ℝ) :=
  hwidth.trans (Real.rpow_le_rpow_of_exponent_le hZ hh)

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable {σ : Type*} (T : FirstParentEnergy.Data K S (σ := σ))

/-- Constructed first centers for any actual parent column scale in
the bounded logarithmic window. -/
def centers (Z A h : ℝ) (hZ : 1 < Z) (hh : h ≤ 1) (hwidth : 2 ≤ Z ^ h)
    (hscale : T.scale.val ≤ Z ^ A) : FirstOuterCenters.Centering K S D T (grid Z A) :=
  FirstOuterCenters.canonical K S D Z A 1 (zero_lt_one.trans hZ)
    (fixed_width Z h hZ.le hh hwidth) T hscale

/-- The public exact-power version accepts the actual column exponent;
no center window or assignment is an additional hypothesis. -/
def centers_of_power (Z A h r : ℝ) (hZ : 1 < Z) (hh : h ≤ 1) (hwidth : 2 ≤ Z ^ h)
    (hscale : T.scale.val = Z ^ r) (hr : r ≤ A) :
    FirstOuterCenters.Centering K S D T (grid Z A) :=
  centers K S D T Z A h hZ hh hwidth
    (hscale.le.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hr))

theorem centers_bounds (Z A h : ℝ) (hZ : 1 < Z) (hh : h ≤ 1) (hwidth : 2 ≤ Z ^ h)
    (hscale : T.scale.val ≤ Z ^ A) (side : Bool) (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) :
    let C := centers K S D T Z A h hZ hh hwidth hscale
    (grid Z A (C.assignment side o e)).val ≤ FirstOuterCenters.extractedNorm K S D T side o e ∧
      FirstOuterCenters.extractedNorm K S D T side o e ≤
        2 * (grid Z A (C.assignment side o e)).val :=
  ⟨(centers K S D T Z A h hZ hh hwidth hscale).lower side o e,
    (centers K S D T Z A h hZ hh hwidth hscale).upper side o e⟩

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstCanonicalCenters

end
