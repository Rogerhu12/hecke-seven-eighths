import HeckeGeneral.Arithmetic.SIntegerOrbitEnumeration

/-!
Simultaneous translation of the three actual nonzero
S-integer indices. Every sum below has one product index. No interchange
of infinite sums, summability assertion, or deletion of associates is used.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup (S.unit K))

def sIntegerTranslateEquiv (u : Γ) :
    NonzeroRingElements (S.integer K) ≃ NonzeroRingElements (S.integer K) where
  toFun := sIntegerOrbitTranslate K S Γ u
  invFun := sIntegerOrbitTranslate K S Γ u⁻¹
  left_inv a := by
    rw [← sIntegerOrbitTranslate_mul, inv_mul_cancel, sIntegerOrbitTranslate_one]
  right_inv a := by
    rw [← sIntegerOrbitTranslate_mul, mul_inv_cancel, sIntegerOrbitTranslate_one]

@[simp] theorem sIntegerTranslateEquiv_apply (u : Γ)
    (a : NonzeroRingElements (S.integer K)) :
    sIntegerTranslateEquiv K S Γ u a = sIntegerOrbitTranslate K S Γ u a := rfl

/-- Enumeration coordinates transform in the original subgroup, not in a
torsion-free quotient. -/
theorem sIntegerOrbitProduct_translate_symm (u γ : Γ)
    (q : SIntegerOrbits K S Γ) :
    nonzeroSIntegerEquivOrbitProduct K S Γ
        (sIntegerOrbitTranslate K S Γ u
          ((nonzeroSIntegerEquivOrbitProduct K S Γ).symm (q, γ))) =
      (q, u * γ) := by
  apply (nonzeroSIntegerEquivOrbitProduct K S Γ).symm.injective
  rw [Equiv.symm_apply_apply, nonzeroSIntegerEquivOrbitProduct_symm_apply,
    nonzeroSIntegerEquivOrbitProduct_symm_apply, sIntegerOrbitTranslate_mul]

theorem nonzeroSIntegerEquivOrbitProduct_translate (u : Γ)
    (a : NonzeroRingElements (S.integer K)) :
    nonzeroSIntegerEquivOrbitProduct K S Γ (sIntegerOrbitTranslate K S Γ u a) =
      ((nonzeroSIntegerEquivOrbitProduct K S Γ a).1,
        u * (nonzeroSIntegerEquivOrbitProduct K S Γ a).2) := by
  have h := sIntegerOrbitProduct_translate_symm K S Γ u
    (nonzeroSIntegerEquivOrbitProduct K S Γ a).2
    (nonzeroSIntegerEquivOrbitProduct K S Γ a).1
  simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using h

/-- The literal change (k,m₁,m₂) ↦ (uvk,um₁,vm₂). -/
def sIntegerTripleTranslateEquiv (u v : Γ) :
    (NonzeroRingElements (S.integer K) ×
      (NonzeroRingElements (S.integer K) × NonzeroRingElements (S.integer K))) ≃
    (NonzeroRingElements (S.integer K) ×
      (NonzeroRingElements (S.integer K) × NonzeroRingElements (S.integer K))) :=
  (sIntegerTranslateEquiv K S Γ (u * v)).prodCongr
    ((sIntegerTranslateEquiv K S Γ u).prodCongr
      (sIntegerTranslateEquiv K S Γ v))

@[simp] theorem sIntegerTripleTranslateEquiv_apply (u v : Γ)
    (k m₁ m₂ : NonzeroRingElements (S.integer K)) :
    sIntegerTripleTranslateEquiv K S Γ u v (k, m₁, m₂) =
      (sIntegerOrbitTranslate K S Γ (u * v) k,
        sIntegerOrbitTranslate K S Γ u m₁,
        sIntegerOrbitTranslate K S Γ v m₂) := rfl

/-- The frequency is k/(m₁m₂), with no conjugation or norm substitution. -/
theorem sIntegerTripleTranslate_frequency (u v : Γ)
    (k m₁ m₂ : NonzeroRingElements (S.integer K)) :
    ((sIntegerOrbitTranslate K S Γ (u * v) k).val : K) /
        (((sIntegerOrbitTranslate K S Γ u m₁).val : K) *
          ((sIntegerOrbitTranslate K S Γ v m₂).val : K)) =
      (k.val : K) / ((m₁.val : K) * (m₂.val : K)) := by
  simp only [sIntegerOrbitTranslate_val, Subgroup.coe_mul, Units.val_mul]
  have hu : ((u.val : Kˣ) : K) ≠ 0 := (u.val : Kˣ).ne_zero
  have hv : ((v.val : Kˣ) : K) ≠ 0 := (v.val : Kˣ).ne_zero
  have h₁ : (m₁.val : K) ≠ 0 := (nonzeroSIntegerFieldUnit K S m₁).ne_zero
  have h₂ : (m₂.val : K) ≠ 0 := (nonzeroSIntegerFieldUnit K S m₂).ne_zero
  field_simp [hu, hv, h₁, h₂]
  <;> ring

/-- One product-indexed sum, with all three subgroup coordinates retained. -/
theorem tsum_sIntegerTriple_translate (u v : Γ)
    (f : NonzeroRingElements (S.integer K) ×
      (NonzeroRingElements (S.integer K) × NonzeroRingElements (S.integer K)) → ℂ) :
    (∑' p, f (sIntegerTripleTranslateEquiv K S Γ u v p)) = ∑' p, f p :=
  (sIntegerTripleTranslateEquiv K S Γ u v).tsum_eq f

/-- Simultaneously enumerate all three indices as orbit × original Γ.
This is still a single sum, rather than six iterated sums. -/
theorem tsum_sIntegerTriple_eq_tsum_orbitProducts
    (f : NonzeroRingElements (S.integer K) ×
      (NonzeroRingElements (S.integer K) × NonzeroRingElements (S.integer K)) → ℂ) :
    (∑' p, f p) =
      ∑' p : (SIntegerOrbits K S Γ × Γ) ×
        ((SIntegerOrbits K S Γ × Γ) × (SIntegerOrbits K S Γ × Γ)),
        f (sIntegerOrbitTranslate K S Γ p.1.2 p.1.1.out,
          sIntegerOrbitTranslate K S Γ p.2.1.2 p.2.1.1.out,
          sIntegerOrbitTranslate K S Γ p.2.2.2 p.2.2.1.out) := by
  let e := (nonzeroSIntegerEquivOrbitProduct K S Γ).symm.prodCongr
    ((nonzeroSIntegerEquivOrbitProduct K S Γ).symm.prodCongr
      (nonzeroSIntegerEquivOrbitProduct K S Γ).symm)
  exact (e.tsum_eq f).symm

end HeckeGeneral.Arithmetic
