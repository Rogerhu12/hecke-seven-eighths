import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussPairTransform
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentSource
import HeckeGeneral.Analysis.SUnitProfileFunctional

/-!
# Genuine periodic sources for the second orbital transform

Each Gauss column descends to all orbits of the original subgroup.  The
pair source uses its own product modulus, and its profile is the original
common test multiplied by the two whole coefficients.  Thus both the
periodic pair identity and the source Gram identity are proved from the
actual columns; neither is a second-transform input.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.CommonSupport

theorem sixth_character_unit_power {R : Type*} [CommRing R]
    (χ : MulChar R ℂ) (hχ : χ ^ 6 = 1) (u : Rˣ) : χ ((u : R) ^ 6) = 1 := by
  rw [map_pow, ← MulChar.pow_apply_coe, hχ, MulChar.one_apply_coe]

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- An actual complete multiplicative column and its original subgroup
invariance.  Nonprimitive characters and non-squarefree moduli are allowed. -/
structure OrbitalGaussColumn where
  modulus : OS
  nonzero : modulus ≠ 0
  character : MulChar (OS ⧸ Ideal.span ({modulus} : Set OS)) ℂ
  invariant : ∀ u : Γ,
    character (Ideal.Quotient.mk _
      (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val)) = 1

/-- The usual common sixth-power subgroup supplies the invariance of
every actual sextic column simultaneously. -/
def OrbitalGaussColumn.ofSixth
    (hΓ : ∀ u : Γ, ∃ v : OSˣ,
      ((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val) = v ^ 6)
    (a : OS) (ha : a ≠ 0)
    (χ : MulChar (OS ⧸ Ideal.span ({a} : Set OS)) ℂ) (hχ : χ ^ 6 = 1) :
    OrbitalGaussColumn K S Γ where
  modulus := a
  nonzero := ha
  character := χ
  invariant u := by
    obtain ⟨v, hv⟩ := hΓ u
    rw [hv, Units.val_pow_eq_pow_val, map_pow]
    exact sixth_character_unit_power χ hχ
      (Units.map (Ideal.Quotient.mk (Ideal.span ({a} : Set OS))).toMonoidHom v)

variable {K S Γ}
variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)

def OrbitalGaussColumn.residue (c : OrbitalGaussColumn K S Γ)
    (h : OS ⧸ Ideal.span ({c.modulus} : Set OS)) : ℂ := by
  letI : Finite (OS ⧸ Ideal.span ({c.modulus} : Set OS)) :=
    finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) c.modulus c.nonzero
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({c.modulus} : Set OS))
  exact completeResidueGauss (R := OS) (actualSIntegerTrace K (S : Set (HeightOneSpectrum (𝓞 K))) hS)
    c.modulus c.character h

theorem OrbitalGaussColumn.residue_invariant (c : OrbitalGaussColumn K S Γ)
    (u : Γ) (x : OS ⧸ Ideal.span ({c.modulus} : Set OS)) :
    c.residue hS (Ideal.Quotient.mk _
        (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val) * x) =
      c.residue hS x := by
  letI : Finite (OS ⧸ Ideal.span ({c.modulus} : Set OS)) :=
    finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) c.modulus c.nonzero
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({c.modulus} : Set OS))
  unfold OrbitalGaussColumn.residue
  rw [← sIntegerResidueUnitHom_val K (S : Set (HeightOneSpectrum (𝓞 K))) c.modulus u.val,
    completeResidueGauss_unit_dilate, MulChar.inv_apply_eq_inv',
    sIntegerResidueUnitHom_val, c.invariant u, inv_one, one_mul]

def OrbitalGaussColumn.orbit (c : OrbitalGaussColumn K S Γ) : Q → ℂ :=
  sIntegerPeriodicOrbitWeight K (S : Set (HeightOneSpectrum (𝓞 K))) Γ c.modulus (c.residue hS)
    (fun u a => by rw [map_mul]; exact c.residue_invariant hS u _)

@[simp] theorem OrbitalGaussColumn.orbit_mk (c : OrbitalGaussColumn K S Γ)
    (h : NonzeroRingElements OS) :
    c.orbit hS (Quotient.mk _ h) = c.residue hS (Ideal.Quotient.mk _ h.val) := rfl

/-- The periodic source for a column pair uses the genuine product
modulus and the complete two-column Gauss product. -/
def OrbitalGaussColumn.pair (c d : OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap V ℂ) : ParentPeriodicPair K S Γ where
  modulus := c.modulus * d.modulus
  modulus_ne_zero := mul_ne_zero c.nonzero d.nonzero
  residue x := c.residue hS
      (completeFrequencyReduction c.modulus (c.modulus * d.modulus)
        (dvd_mul_right _ _) x) *
    star (d.residue hS
      (completeFrequencyReduction d.modulus (c.modulus * d.modulus)
        (dvd_mul_left _ _) x))
  invariant u a := by
    simp only [completeFrequencyReduction_mk, map_mul,
      OrbitalGaussColumn.residue_invariant]
  profile := φ

theorem OrbitalGaussColumn.pair_orbitWeight (c d : OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap V ℂ) (q : Q) :
    (c.pair hS d φ).orbitWeight q = c.orbit hS q * star (d.orbit hS q) := by
  refine Quotient.inductionOn q ?_
  intro a
  simp only [ParentPeriodicPair.orbitWeight, OrbitalGaussColumn.pair,
    sIntegerPeriodicOrbitWeight_mk, completeFrequencyReduction_mk,
    OrbitalGaussColumn.orbit_mk]

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

/-- Scalar coefficients factor through the actual Haar integral, so the
second source Gram profile is derived from one common original test. -/
theorem OrbitalGaussColumn.pair_profile (c d : OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap V ℂ) (b e : ℂ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (r : {r : ℝ // 0 < r}) (q : Q) :
    (c.pair hS d ((b * star e) • φ)).orbitProfile ψ r q =
      (b * star e) * (c.pair hS d φ).orbitProfile ψ r q := by
  unfold ParentPeriodicPair.orbitProfile OrbitalGaussColumn.pair
  exact sUnitOrbitalProfile_tensor_smul K (S : Set (HeightOneSpectrum (𝓞 K))) ψ (b * star e) φ _

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OrbitalGaussColumn.ofSixth
#print axioms HeckeSkeleton.Moments.EngineStep.OrbitalGaussColumn.pair_orbitWeight
#print axioms HeckeSkeleton.Moments.EngineStep.OrbitalGaussColumn.pair_profile

