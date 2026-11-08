module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolGaussDecomposition
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentOrbitFibre
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.TailFiberCount

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Physical orbit fibres of the original direct and amplified sources

The first carriers are images of actual subgroup-orbit representatives.
The direct source and every valuation correction therefore have fibres
of size at most one. In the main source, a fixed output orbit determines
the input orbit once its actual pool prime is fixed. The distinct prime
labels divide the same output ideal, so the original large-prime count
bounds this fibre by the already explicit arithmetic multiplicity.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

namespace T3b

variable {A : SArithmeticData K} {Γ : Subgroup A.U}

theorem engineElementOrbit_out
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    engineElementOrbit (Γ := Γ) q.out.val = q := by
  rw [engineElementOrbit, dif_pos q.out.property]
  exact Quotient.out_eq q

theorem engineElementOrbit_mul (d a : A.R) (hd : d ≠ 0) (ha : a ≠ 0) :
    engineElementOrbit (Γ := Γ) (d * a) =
      sIntegerOrbitDilation K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
        ⟨d, hd⟩ (engineElementOrbit (Γ := Γ) a) := by
  rw [engineElementOrbit, dif_pos (mul_ne_zero hd ha),
    engineElementOrbit, dif_pos ha]
  rfl

theorem engineElementOrbit_mul_cancel (d a b : A.R)
    (hd : d ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (he : engineElementOrbit (Γ := Γ) (d * a) =
      engineElementOrbit (Γ := Γ) (d * b)) :
    engineElementOrbit (Γ := Γ) a = engineElementOrbit (Γ := Γ) b := by
  rw [engineElementOrbit_mul d a hd ha, engineElementOrbit_mul d b hd hb] at he
  exact sIntegerOrbitDilation_injective K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ ⟨d, hd⟩ he

theorem engineElementOrbit_neg_cancel (a b : A.R) (ha : a ≠ 0) (hb : b ≠ 0)
    (he : engineElementOrbit (Γ := Γ) (-a) = engineElementOrbit (Γ := Γ) (-b)) :
    engineElementOrbit (Γ := Γ) a = engineElementOrbit (Γ := Γ) b := by
  apply engineElementOrbit_mul_cancel (-1) a b (neg_ne_zero.mpr one_ne_zero) ha hb
  simpa only [neg_one_mul] using he

theorem representative_image_orbit_injective
    (rows : Finset (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)) :
    Set.InjOn (engineElementOrbit (Γ := Γ))
      (rows.image (fun q => q.out.val) : Set A.R) := by
  intro a ha b hb he
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hb
  have hqr : q = r := by simpa only [engineElementOrbit_out] using he
  rw [hqr]

theorem negative_representative_image_orbit_injective
    (rows : Finset (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)) :
    Set.InjOn (engineElementOrbit (Γ := Γ))
      (rows.image (fun q => -q.out.val) : Set A.R) := by
  intro a ha b hb he
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hb
  have hqr : q = r := by
    simpa only [engineElementOrbit_out] using
      (engineElementOrbit_neg_cancel q.out.val r.out.val q.out.property r.out.property he)
  rw [hqr]

theorem generatedIdeal_eq_of_engineElementOrbit_eq
    {I J : A.Exterior} {a b : A.R} (ha : A.Generates I a) (hb : A.Generates J b)
    (he : engineElementOrbit (Γ := Γ) a = engineElementOrbit (Γ := Γ) b) : I = J := by
  have hI : ProbeOrbitNormSum.principalExterior A
      (engineElementOrbit (Γ := Γ) a).out = I := by
    simpa only [engineElementOrbit, dif_pos ha.1, parentGeneratorOrbit] using
      parentGeneratorOrbit_originalIdeal A Γ I a ha
  have hJ : ProbeOrbitNormSum.principalExterior A
      (engineElementOrbit (Γ := Γ) b).out = J := by
    simpa only [engineElementOrbit, dif_pos hb.1, parentGeneratorOrbit] using
      parentGeneratorOrbit_originalIdeal A Γ J b hb
  have hrepresentatives :
      ProbeOrbitNormSum.principalExterior A
          (engineElementOrbit (Γ := Γ) a).out =
        ProbeOrbitNormSum.principalExterior A
          (engineElementOrbit (Γ := Γ) b).out :=
    congrArg
      (fun q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ =>
        ProbeOrbitNormSum.principalExterior A q.out) he
  exact hI.symm.trans (hrepresentatives.trans hJ)

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}

/-- The prime-label injection works for equality of original subgroup
orbits, without replacing any selected generator by another one. -/
theorem amplified_orbit_fibre_count
    (C : A.GeneralArithmeticContext σ η hS)
    (pairs : Finset (A.R × ExteriorPrime A)) (rows : Finset A.R)
    (rowIdeal : A.R → A.Exterior)
    (hrows : ∀ x ∈ pairs, x.1 ∈ rows ∧ A.Generates (rowIdeal x.1) x.1)
    (hinj : Set.InjOn (engineElementOrbit (Γ := Γ)) (rows : Set A.R))
    (I : A.Exterior) (y : A.R) (hy : A.Generates I y)
    (houtput : ∀ x ∈ pairs,
      engineElementOrbit (Γ := Γ) (actualFrequencyAmplify C x) =
        engineElementOrbit (Γ := Γ) y)
    (Z ell B : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ x ∈ pairs, Z ^ ell ≤ (Ideal.absNorm x.2.val.asIdeal : ℝ))
    (hupper : (Ideal.absNorm I.val : ℝ) ≤ Z ^ B) :
    (pairs.card : ℝ) ≤ B / ell := by
  refine indexed_large_prime_ideal_count pairs (fun x => x.2.val.asIdeal) ?_
    (fun x _ => x.2.val.prime) I.val I.property.1 ?_ Z ell B hZ hell hlower hupper
  · intro x hx x' hx' heq
    have hp : x.2 = x'.2 := Subtype.ext (HeightOneSpectrum.asIdeal_injective heq)
    have he : engineElementOrbit (Γ := Γ) (actualFrequencyAmplify C x) =
        engineElementOrbit (Γ := Γ) (actualFrequencyAmplify C x') :=
      (houtput x hx).trans (houtput x' hx').symm
    have he' : engineElementOrbit (Γ := Γ) x.1 =
        engineElementOrbit (Γ := Γ) x'.1 := by
      apply engineElementOrbit_mul_cancel (generator C x.2 ^ 6) x.1 x'.1
        (pow_ne_zero _ (generator_generates C x.2).1)
        (hrows x hx).2.1 (hrows x' hx').2.1
      simpa only [actualFrequencyAmplify, ← hp, mul_comm] using he
    exact Prod.ext (hinj (hrows x hx).1 (hrows x' hx').1 he') hp
  · intro x hx
    have hg := amplifiedExterior_generates C (rowIdeal x.1) x.2 x.1 (hrows x hx).2
    have heq := generatedIdeal_eq_of_engineElementOrbit_eq hg hy (houtput x hx)
    rw [← congrArg Subtype.val heq, amplifiedExterior_val]
    exact (dvd_pow_self x.2.val.asIdeal (by decide : 6 ≠ 0)).trans (dvd_mul_right _ _)

variable {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

/-- The main source's actual element carrier has at most the original
large-prime multiplicity many elements in any one subgroup orbit. -/
theorem mainRows_orbit_fibre_le (d : FirstGaussPoolData C P ι)
    (hinj : Set.InjOn (engineElementOrbit (Γ := Γ)) (d.rows : Set A.R))
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    ((d.mainRows.filter (fun y => engineElementOrbit (Γ := Γ) y = q)).card : ℝ) ≤
      d.multiplicity := by
  let fibre := d.mainRows.filter (fun y => engineElementOrbit (Γ := Γ) y = q)
  let pairs := d.eligible.filter (fun x =>
    engineElementOrbit (Γ := Γ) (actualFrequencyAmplify C x) = q)
  have hmem (x : A.R × ExteriorPrime A) (hx : x ∈ d.eligible) :
      x.1 ∈ d.rows ∧ x.2 ∈ P.primes :=
    Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  by_cases hnonempty : fibre.Nonempty
  · obtain ⟨y, hy⟩ := hnonempty
    obtain ⟨hymain, hyq⟩ := Finset.mem_filter.mp hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hymain
    have hxq : engineElementOrbit (Γ := Γ) (actualFrequencyAmplify C x) = q := by
      rw [hxy]
      exact hyq
    have hfibre : fibre ⊆ pairs.image (actualFrequencyAmplify C) := by
      intro z hz
      obtain ⟨hzmain, hzq⟩ := Finset.mem_filter.mp hz
      obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hzmain
      refine Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, ?_⟩, hwz⟩
      rwa [hwz]
    have hcount : (pairs.card : ℝ) ≤ d.multiplicity := by
      apply amplified_orbit_fibre_count C pairs d.rows d.rowIdeal
        (fun w hw => ⟨(hmem w (Finset.mem_filter.mp hw).1).1,
          d.row_generates w.1 (hmem w (Finset.mem_filter.mp hw).1).1⟩) hinj
        (amplifiedExterior (d.rowIdeal x.1) x.2) (actualFrequencyAmplify C x)
        (amplifiedExterior_generates C (d.rowIdeal x.1) x.2 x.1
          (d.row_generates x.1 (hmem x hx).1))
        (fun w hw => (Finset.mem_filter.mp hw).2.trans hxq.symm)
        Z (ell / 2) (d.rowExponent + 6 * ell) P.base_gt_one
        (half_pos P.exponent_pos)
        (fun w hw => P.norm_lower w.2 (hmem w (Finset.mem_filter.mp hw).1).2)
      have hn := idealAmplify_norm ((d.rowIdeal x.1).val, x.2.val.asIdeal)
        Z d.rowExponent ell (zero_lt_one.trans P.base_gt_one)
        (d.row_norm x.1 (hmem x hx).1) (P.norm_upper x.2 (hmem x hx).2)
      simpa only [idealAmplify, amplifiedExterior_val] using hn
    exact (show (fibre.card : ℝ) ≤ pairs.card by
      exact_mod_cast (Finset.card_le_card hfibre).trans (Finset.card_image_le)).trans hcount
  · change (fibre.card : ℝ) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty, Finset.card_empty, Nat.cast_zero]
    exact d.multiplicity_nonneg

end T3b

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.mainRows_orbit_fibre_le
