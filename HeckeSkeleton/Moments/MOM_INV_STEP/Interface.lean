import HeckeSkeleton.Moments.MOM_INV_STEP.FixedTripleEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.Normalization
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalStep
import Batteries.Tactic.Alias

/-!
# Quantitative interface of the actual canonical inverse step

`canonical_inverse_step` starts with the literal original canonical
parent. It constructs both true Poisson transforms and their actual
sources, masks, old and new labels, fixed-triple fibers, norm boxes,
physical radii and Mellin tests. The complete principal and localized
infinite-tail errors are included in its energy inequality.

For F = r + 3 ell + V, its normalized parent bound is

  C Aw qArch(φ) qW(W)^2
    ((Cih + 1) Z^(F + 40 eta + tau + pi + eps) + Z^(M + 5 h + pi)).

The constant and finite seminorms precede the original parent, its prime
lists, base, lengths and tests. The only recursive energy hypothesis is
`ActualUniformProduction.AllSmallerPieces`, on the actual generated
canonical children. Those same children are proved to have complete
norm pools, tests supported in [1,2], the c−5 eta and c−7 eta margins,
row descent 3d/2, and Fchild ≤ F+11 eta. The first center assignment and
first physical cap are constructed internally from the original source.

The original hypotheses are the fixed bounded length window, the
canonical parent margins, the fine mesh h ≤ eta/32, eta ≤ d/16 and
d ≤ ell+V, the exact parent scales, the original coefficient and prime
weight bounds, and the actual background and Gauss calibration data.
The empty extra orbital mask does not restrict the nonzero coefficient
puncture, which is retained throughout both transformations.

`fixed_triple_energy_step` exposes the finite packet estimate used
inside that construction. Full tree induction and finite termination
belong to MOM_INV_INDUCTION.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOMInvStep

open NumberField IsDedekindDomain
open FixedTripleFibers FixedTripleEnergy
open scoped BigOperators Classical NumberField

/-- The three distinct-triple norm bounds obtained from the original
cube, common-factor, and divisor annuli. -/
def tripleNormQ (Z ell R j eta : ℝ) : ℝ := Z ^ (ell + R / 2 - j + 5 * eta / 2)

def tripleNormT (Z t eta : ℝ) : ℝ := Z ^ (t + eta)

def tripleNormR (Z g theta eta : ℝ) : ℝ := Z ^ (g - theta + 2 * eta)

theorem tripleNorm_product (Z : ℝ) (hZ : 0 < Z)
    (ell R j t g theta eta : ℝ) :
    tripleNormQ Z ell R j eta * tripleNormT Z t eta * tripleNormR Z g theta eta =
      Z ^ (secondCount ell R j t g theta + 11 * eta / 2) := by
  unfold tripleNormQ tripleNormT tripleNormR secondCount
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  ring

/-- Literal first prefactor and second Poisson scalar, before charging
any frozen-triple mass or restoring any child normalization. -/
def physicalStepScalar (Z M r ell V delta A B R j t g theta v eta tau : ℝ)
    (ray : ℂ) : ℝ :=
  Z ^ firstKappa M r ell V delta A B R *
    Real.exp ((9 / 2 : ℝ) * (eta * Real.log Z)) *
    (Real.exp (6 * (eta * Real.log Z)) *
      ‖((Z ^ (firstPhysicalHeight M r ell V delta B j + 12 * eta + tau) : ℝ) : ℂ) * ray *
        ((Z ^ theta * Z ^ v * Z ^ secondFormalColumn r A B t g v : ℝ) : ℂ)⁻¹‖)

theorem physicalStepScalar_nonneg (Z M r ell V delta A B R j t g theta v eta tau : ℝ)
    (hZ : 0 ≤ Z) (ray : ℂ) :
    0 ≤ physicalStepScalar Z M r ell V delta A B R j t g theta v eta tau ray := by
  unfold physicalStepScalar
  positivity

variable {K : Type*} [Field K] [NumberField K] {Sector : Type*}
variable (sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector))

/-- The finite part of the canonical inverse single step, with every
scalar loss exposed. The constant is chosen before the source, original
prime lists, ranges, columns, and physical parameters. Only smaller-child
energy bounds are premises. The whole triple mass is charged once. -/
theorem fixed_triple_energy_step (slotCap : ℕ) (massEps : ℝ) (hmassEps : 0 < massEps) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Jo Jn : ℕ}
      (P : ReconstructionPacket (K := K) (Sector := Sector) sectorTransport slotCap Jo Jn)
      (Z M r ell V delta A B R j t g theta v eta tau pi eps : ℝ)
      (ray : ℂ) (Cchild : ℝ),
      1 ≤ Z → 0 ≤ Cchild →
      max 0 (secondFormalColumn r A B t g v) - secondFormalColumn r A B t g v ≤ 6 * eta →
      massEps * (secondCount ell R j t g theta + 11 * eta / 2) ≤ pi →
      (∀ x ∈ originalSource P.source P.oldLists P.newLists P.keep,
        (Ideal.absNorm x.outer.q0 : ℝ) ≤ tripleNormQ Z ell R j eta ∧
        (Ideal.absNorm x.outer.quotient : ℝ) ≤ tripleNormT Z t eta ∧
        (Ideal.absNorm x.outer.residual : ℝ) ≤ tripleNormR Z g theta eta) →
      ∀ (F G : SecondChild K Sector → ℂ),
      (∀ γ ∈ P.triples,
        normalizedChildEnergy Z (max 0 (secondFormalColumn r A B t g v))
          (secondFormalLabel B theta v j) slotCap P.labels P.rows F γ ≤
        Cchild * Z ^ (max 0 (secondFormalColumn r A B t g v) +
          secondFormalLabel B theta v j + eps)) →
      (∀ γ ∈ P.triples,
        normalizedChildEnergy Z (max 0 (secondFormalColumn r A B t g v))
          (secondFormalLabel B theta v j) slotCap P.labels P.rows G γ ≤
        Cchild * Z ^ (max 0 (secondFormalColumn r A B t g v) +
          secondFormalLabel B theta v j + eps)) →
      physicalStepScalar Z M r ell V delta A B R j t g theta v eta tau ray *
          ‖P.signedValue F G‖ ≤
        C * Cchild * ‖ray‖ * Z ^ (r + 3 * ell + V + 40 * eta + tau + pi + eps) := by
  obtain ⟨C, hC, hmass⟩ := ReconstructionPacket.exists_tripleMass_bound_of_norm_box
    (K := K) (Sector := Sector) (sectorTransport := sectorTransport)
    (slotCap := slotCap) massEps hmassEps
  refine ⟨C, hC, ?_⟩
  intro Jo Jn P Z M r ell V delta A B R j t g theta v eta tau pi eps ray Cchild
    hZ hCchild hclip hloss hsource F G hF hG
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hmass' : P.tripleMass ≤
      C * Z ^ ((secondCount ell R j t g theta + 11 * eta / 2) * (1 + massEps)) := by
    have hb := hmass P (tripleNormQ Z ell R j eta) (tripleNormT Z t eta)
      (tripleNormR Z g theta eta)
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
      (Real.rpow_pos_of_pos hZpos _) hsource
    rw [tripleNorm_product Z hZpos, ← Real.rpow_mul hZpos.le] at hb
    exact hb
  let H := Cchild * Z ^ (2 * (max 0 (secondFormalColumn r A B t g v) +
    secondFormalLabel B theta v j) + eps)
  have hH : 0 ≤ H := mul_nonneg hCchild (Real.rpow_nonneg hZpos.le _)
  have hFraw : ∀ γ ∈ P.triples, P.energy F γ ≤ H := by
    intro γ hγ
    exact childEnergy_bound_of_normalized Z _ _ eps Cchild hZpos
      slotCap P.labels P.rows F γ (hF γ hγ)
  have hGraw : ∀ γ ∈ P.triples, P.energy G γ ≤ H := by
    intro γ hγ
    exact childEnergy_bound_of_normalized Z _ _ eps Cchild hZpos
      slotCap P.labels P.rows G γ (hG γ hγ)
  have hs := P.signedValue_le F G H hH hFraw hGraw
  have hscaled := mul_le_mul_of_nonneg_left
    (hs.trans (mul_le_mul_of_nonneg_left hmass' hH))
    (physicalStepScalar_nonneg Z M r ell V delta A B R j t g theta v eta tau hZpos.le ray)
  have hbudget := physical_block_scalar_budget Z hZ M r ell V delta A B R j t g theta v
    eta tau pi eps massEps ray (C * Cchild) (mul_nonneg hC.le hCchild) hclip hloss
  apply hscaled.trans
  convert hbudget using 1 <;> dsimp only [physicalStepScalar, H] <;> ring

/-- An induction can consume the proved numerical conclusion with the
same original slot cap. These are the sharp c−5η and c−7η margins together
with a strict 3d/2 row decrease. -/
theorem canonical_child_geometry {F M Q z c d eta : ℝ}
    (x : ChildGeometry F M Q z c d eta)
    (hparent : HeckePort.Moments.CanonicalMargins F M Q z c)
    (heta : 0 ≤ eta) (hstep : eta ≤ d / 16) :
    c - 5 * eta ≤ x.Fchild - x.Mchild - x.Qnew - z ∧
    c - 7 * eta ≤ 4 * x.Fchild - 3 * x.Mchild - 6 * z ∧
    3 * d / 2 ≤ M - x.Mchild ∧ x.Fchild ≤ F + 11 * eta :=
  x.step hparent heta hstep

end HeckeSkeleton.Moments.MOMInvStep

namespace HeckeSkeleton.Moments.MOMInvStep

/-- Complete actual-parent inverse single step, with source-independent
constants and the geometric closure of its precise induction class.
The full quantified statement is `CanonicalStep.exists_uniform_step`. -/
alias canonical_inverse_step :=
  HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalStep.exists_uniform_step

end HeckeSkeleton.Moments.MOMInvStep

end
