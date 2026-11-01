import Mathlib.Analysis.Complex.Basic

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

/-- A sufficient open region containing the central moderate, small-row,
principal-residue and absolute-large contours used here. The two mixed
conditions control the actual error monomials `W * V` and `D * V` in the
cancelled local rational factor. Omitting them does not give an absolutely
convergent prime product. This is not a claim that the local correction has
no continuation outside this region. -/
def rowEulerRegion : Set (ℂ × ℂ × ℂ) :=
  {v | 1 / 2 < v.1.re ∧ 0 < v.2.1.re ∧ 0 < v.2.2.re ∧
    1 < v.1.re + v.2.1.re ∧ 5 / 6 < v.1.re + v.2.2.re ∧
      2 < v.1.re + v.2.1.re + 6 * v.2.2.re ∧
      1 < v.2.1.re + 6 * v.2.2.re ∧ 1 < v.1.re + 6 * v.2.2.re}


end HeckeGeneral.ThetaSkeleton.Physical
