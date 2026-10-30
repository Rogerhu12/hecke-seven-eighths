import HeckeGeneral.Analysis.AnnularTest

/-!
# The canonical prime-window geometry

The geometry and scale are moved verbatim from `PhysicalProbeData`.
Their names and data remain unchanged; the actual prime window and
physical-probe expressions continue to be defined in that module.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open Set HeckeGeneral.ThetaSkeleton.Global

/-- Pretarget choices: J0, the disjoint annuli and all prime scale exponents
are chosen independently of a later target character. -/
structure PrimeWindowGeometry where
  slots : ℕ
  slots_pos : 0 < slots
  slots_even : Even slots
  weight : Fin slots → SmoothAnnularTest
  nonnegative : ∀ i y, 0 ≤ ((weight i).toFun y).re
  real_valued : ∀ i y, ((weight i).toFun y).im = 0
  nonzero : ∀ i, ∃ y, (weight i).toFun y ≠ 0
  support_annular : ∀ i, Function.support (weight i).toFun ⊆ Ioo (1 : ℝ) 2
  disjoint : ∀ i j, i ≠ j →
    Disjoint (Function.support (weight i).toFun) (Function.support (weight j).toFun)

def primeScale (g : PrimeWindowGeometry) (Z : ℝ) : ℝ :=
  Z ^ ((1 / 6 : ℝ) / g.slots)

end HeckeGeneral.ThetaSkeleton.Physical
