import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalRowBallChart
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolSecondStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstGaussData

/-!
# The actual orbital fibres of the original Gauss rows

The finite multiplicity is computed from the literal element-to-orbit
map.  Direct rows are the original quotient representatives, with a
fixed nonzero multiplier (in particular either sign), and have unit
fibres.  Sixth-power amplified rows retain their genuine multiplicity:
each orbital fibre injects into the large prime divisors of its output
ideal.  No injectivity assertion about an arbitrary enlarged row set is
used.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {Γ : Subgroup A.U}

local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

@[simp] theorem engineElementOrbit_out (q : Q) :
    engineElementOrbit (Γ := Γ) q.out.val = q := by
  rw [engineElementOrbit, dif_pos q.out.property]
  exact Quotient.out_eq q

theorem engineElementOrbit_mul (a b : A.R) (ha : a ≠ 0) (hb : b ≠ 0) :
    engineElementOrbit (Γ := Γ) (a * b) =
      sIntegerOrbitDilation K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
        ⟨b, hb⟩ (engineElementOrbit (Γ := Γ) a) := by
  rw [engineElementOrbit, dif_pos (mul_ne_zero ha hb),
    engineElementOrbit, dif_pos ha, sIntegerOrbitDilation_mk]
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  exact mul_comm a b

theorem engineElementOrbit_cancel_mul {a a' b : A.R}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0)
    (he : engineElementOrbit (Γ := Γ) (a * b) =
      engineElementOrbit (Γ := Γ) (a' * b)) :
    engineElementOrbit (Γ := Γ) a = engineElementOrbit (Γ := Γ) a' := by
  rw [engineElementOrbit_mul a b ha hb, engineElementOrbit_mul a' b ha' hb] at he
  exact sIntegerOrbitDilation_injective K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ ⟨b, hb⟩ he

/-- The quotient map of actual signed representatives is injective;
the representatives themselves are not replaced by allowed generators. -/
theorem engineElementOrbit_out_mul_injective (b : A.R) (hb : b ≠ 0) :
    Function.Injective (fun q : Q => engineElementOrbit (Γ := Γ) (q.out.val * b)) := by
  intro q q' he
  simpa only [engineElementOrbit_out] using
    engineElementOrbit_cancel_mul q.out.property q'.out.property hb he

theorem engineElementOrbit_generatedIdeal (I : A.Exterior)
    (h : A.R) (hh : A.Generates I h) :
    ProbeOrbitNormSum.principalExterior A (engineElementOrbit (Γ := Γ) h).out = I := by
  simpa only [engineElementOrbit, dif_pos hh.1, parentGeneratorOrbit] using
    parentGeneratorOrbit_originalIdeal A Γ I h hh

theorem engineElementOrbit_norm_of_generates (I : A.Exterior)
    (h : A.R) (hh : A.Generates I h) :
    (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
      (engineElementOrbit (Γ := Γ) h)).val = (Ideal.absNorm I.val : ℝ) := by
  rw [engineElementOrbit, dif_pos hh.1, sIntegerOrbitNorm_mk]
  rw [← natCard_sIntegerPrincipalResidue_eq_productNorm K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) h hh.1, hh.2, A.exteriorResidue_card]

theorem originalFrequencyIdeal_out_norm (q : Q) :
    A.exteriorNorm (originalFrequencyIdeal q.out.val) =
      (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ q).val :=
  (originalFrequencyIdeal_norm q.out.val q.out.property).trans
    (congrArg Subtype.val (sIntegerOrbitNorm_out K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ q))

theorem originalFrequencyIdeal_neg_out_norm (q : Q) :
    A.exteriorNorm (originalFrequencyIdeal (-q.out.val)) =
      (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ q).val := by
  have hg := originalFrequencyIdeal_generates q.out.val q.out.property
  have hn : A.Generates (originalFrequencyIdeal q.out.val) (-q.out.val) :=
    ⟨neg_ne_zero.mpr q.out.property, by simpa only [Ideal.span_singleton_neg] using hg.2⟩
  rw [generatedIdeal_unique
    (originalFrequencyIdeal_generates (-q.out.val) (neg_ne_zero.mpr q.out.property)) hn]
  exact originalFrequencyIdeal_out_norm q

/-- The exact maximum of the actual finite orbital fibre sizes. -/
def engineOrbitMultiplicity (rows : Finset A.R) : ℕ :=
  rows.sup (fun h => (rows.filter (fun h' =>
    engineElementOrbit (Γ := Γ) h' = engineElementOrbit (Γ := Γ) h)).card)

theorem engineOrbit_fibre_le_multiplicity (rows : Finset A.R) (q : Q) :
    (rows.filter (fun h => engineElementOrbit (Γ := Γ) h = q)).card ≤
      engineOrbitMultiplicity (Γ := Γ) rows := by
  by_cases he : (rows.filter (fun h => engineElementOrbit (Γ := Γ) h = q)).Nonempty
  · obtain ⟨h, hh⟩ := he
    obtain ⟨hr, hq⟩ := Finset.mem_filter.mp hh
    rw [← hq]
    exact Finset.le_sup hr
  · rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.card_empty]
    exact Nat.zero_le _

theorem engineOrbitMultiplicity_le (rows : Finset A.R) (B : ℕ)
    (hB : ∀ q : Q,
      (rows.filter (fun h => engineElementOrbit (Γ := Γ) h = q)).card ≤ B) :
    engineOrbitMultiplicity (Γ := Γ) rows ≤ B :=
  Finset.sup_le (fun _ _ => hB _)

/-- Every subset of the original representative image has unit fibres.
Taking `b = 1` or `b = -1` gives the two actual first-Cauchy sides. -/
theorem engineOrbit_image_fibres_le_one (source : Finset Q)
    (b : A.R) (hb : b ≠ 0) (rows : Finset A.R)
    (hrows : rows ⊆ source.image (fun q => q.out.val * b)) (q : Q) :
    (rows.filter (fun h => engineElementOrbit (Γ := Γ) h = q)).card ≤ 1 := by
  apply Finset.card_le_one_iff.mpr
  intro h h' hh hh'
  obtain ⟨hr, he⟩ := Finset.mem_filter.mp hh
  obtain ⟨hr', he'⟩ := Finset.mem_filter.mp hh'
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (hrows hr)
  obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp (hrows hr')
  exact congrArg (fun v : Q => v.out.val * b)
    (engineElementOrbit_out_mul_injective b hb (he.trans he'.symm))

theorem engineOrbit_image_multiplicity_le_one (source : Finset Q)
    (b : A.R) (hb : b ≠ 0) (rows : Finset A.R)
    (hrows : rows ⊆ source.image (fun q => q.out.val * b)) :
    engineOrbitMultiplicity (Γ := Γ) rows ≤ 1 :=
  engineOrbitMultiplicity_le rows 1 (engineOrbit_image_fibres_le_one source b hb rows hrows)

/-- A raw representative recipe gives the required injectivity on the
original rows, before the prime amplification is applied. -/
theorem engineOrbit_image_injOn (source : Finset Q)
    (b : A.R) (hb : b ≠ 0) (rows : Finset A.R)
    (hrows : rows ⊆ source.image (fun q => q.out.val * b)) :
    Set.InjOn (engineElementOrbit (Γ := Γ)) (rows : Set A.R) := by
  intro h hh h' hh' he
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (hrows hh)
  obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp (hrows hh')
  exact congrArg (fun v : Q => v.out.val * b)
    (engineElementOrbit_out_mul_injective b hb he)

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {htrace : A.ContainsTraceBadPlaces}

/-- For a fixed auxiliary prime, cancellation of the actual nonzero
sixth power is injective on the original orbit rows.  Distinct primes
in a fibre divide the same original output ideal. -/
theorem actualFrequencyAmplify_orbit_fibre_count
    (C : A.GeneralArithmeticContext σ η htrace)
    (rows : Finset A.R) (rowIdeal : A.R → A.Exterior)
    (hrows : ∀ h ∈ rows, A.Generates (rowIdeal h) h)
    (hinj : Set.InjOn (engineElementOrbit (Γ := Γ)) (rows : Set A.R))
    (pairs : Finset (A.R × ExteriorPrime A))
    (hpairs : ∀ x ∈ pairs, x.1 ∈ rows)
    (q : Q)
    (houtput : ∀ x ∈ pairs, engineElementOrbit (Γ := Γ) (actualFrequencyAmplify C x) = q)
    (Z ell B : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ x ∈ pairs, Z ^ ell ≤ (Ideal.absNorm x.2.val.asIdeal : ℝ))
    (hupper : (Ideal.absNorm (ProbeOrbitNormSum.principalExterior A q.out).val : ℝ) ≤ Z ^ B) :
    (pairs.card : ℝ) ≤ B / ell := by
  refine indexed_large_prime_ideal_count pairs (fun x => x.2.val.asIdeal) ?_
    (fun x _ => x.2.val.prime)
    (ProbeOrbitNormSum.principalExterior A q.out).val
    (ProbeOrbitNormSum.principalExterior A q.out).property.1 ?_
    Z ell B hZ hell hlower hupper
  · intro x hx x' hx' heq
    have hp : x.2 = x'.2 := Subtype.ext (HeightOneSpectrum.asIdeal_injective heq)
    have he : engineElementOrbit (Γ := Γ) (x.1 * generator C x.2 ^ 6) =
        engineElementOrbit (Γ := Γ) (x'.1 * generator C x.2 ^ 6) := by
      change engineElementOrbit (Γ := Γ) (actualFrequencyAmplify C x) = _
      rw [houtput x hx, hp]
      exact (houtput x' hx').symm
    have hfirst : x.1 = x'.1 := hinj (hpairs x hx) (hpairs x' hx')
      (engineElementOrbit_cancel_mul (hrows x.1 (hpairs x hx)).1
        (hrows x'.1 (hpairs x' hx')).1
        (pow_ne_zero 6 (generator_generates C x.2).1) he)
    exact Prod.ext hfirst hp
  · intro x hx
    have hg := amplifiedExterior_generates C (rowIdeal x.1) x.2 x.1
      (hrows x.1 (hpairs x hx))
    have he := engineElementOrbit_generatedIdeal (Γ := Γ)
      (amplifiedExterior (rowIdeal x.1) x.2) (actualFrequencyAmplify C x) hg
    rw [houtput x hx] at he
    rw [he, amplifiedExterior_val]
    exact (dvd_pow_self x.2.val.asIdeal (by decide : 6 ≠ 0)).trans (dvd_mul_right _ _)

/-- The actual enlarged element row set retains this finite orbital
multiplicity.  It is controlled by original row and prime norm windows,
with no factor equal to the size of the auxiliary prime pool. -/
theorem actualFrequencyAmplify_orbit_output_fibres
    (C : A.GeneralArithmeticContext σ η htrace)
    (rows : Finset A.R) (rowIdeal : A.R → A.Exterior)
    (hrows : ∀ h ∈ rows, A.Generates (rowIdeal h) h)
    (hinj : Set.InjOn (engineElementOrbit (Γ := Γ)) (rows : Set A.R))
    (pool : Finset (ExteriorPrime A)) (allow : A.R → ExteriorPrime A → Prop)
    (Z ell M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hpl : ∀ p ∈ pool, Z ^ ell ≤ (Ideal.absNorm p.val.asIdeal : ℝ))
    (hpu : ∀ p ∈ pool, (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ L)
    (hhu : ∀ h ∈ rows, (Ideal.absNorm (rowIdeal h).val : ℝ) ≤ Z ^ M)
    (q : Q) :
    ((((eligiblePairs rows pool allow).image (actualFrequencyAmplify C)).filter
      (fun h => engineElementOrbit (Γ := Γ) h = q)).card : ℝ) ≤ (M + 6 * L) / ell := by
  let pairs := (eligiblePairs rows pool allow).filter
    (fun x => engineElementOrbit (Γ := Γ) (actualFrequencyAmplify C x) = q)
  have hmem (x : A.R × ExteriorPrime A) (hx : x ∈ pairs) :
      x.1 ∈ rows ∧ x.2 ∈ pool :=
    Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have he : (((eligiblePairs rows pool allow).image (actualFrequencyAmplify C)).filter
      (fun h => engineElementOrbit (Γ := Γ) h = q)) =
      pairs.image (actualFrequencyAmplify C) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_image, pairs]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hq⟩
      exact ⟨x, ⟨hx, hq⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hq⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hq⟩
  rw [he]
  by_cases hp : pairs.Nonempty
  · obtain ⟨x, hx⟩ := hp
    have hbound : (pairs.card : ℝ) ≤ (M + 6 * L) / ell := by
      apply actualFrequencyAmplify_orbit_fibre_count C rows rowIdeal hrows hinj pairs
        (fun x hx => (hmem x hx).1) q (fun x hx => (Finset.mem_filter.mp hx).2)
        Z ell (M + 6 * L) hZ hell (fun x hx => hpl x.2 (hmem x hx).2)
      have hg := amplifiedExterior_generates C (rowIdeal x.1) x.2 x.1
        (hrows x.1 (hmem x hx).1)
      have hi := engineElementOrbit_generatedIdeal (Γ := Γ)
        (amplifiedExterior (rowIdeal x.1) x.2) (actualFrequencyAmplify C x) hg
      rw [(Finset.mem_filter.mp hx).2] at hi
      rw [hi]
      simpa only [idealAmplify, amplifiedExterior_val] using
        idealAmplify_norm ((rowIdeal x.1).val, x.2.val.asIdeal) Z M L
          (zero_lt_one.trans hZ) (hhu x.1 (hmem x hx).1) (hpu x.2 (hmem x hx).2)
    exact (Nat.cast_le.mpr Finset.card_image_le).trans hbound
  · rw [Finset.not_nonempty_iff_eq_empty.mp hp, Finset.image_empty,
      Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (add_nonneg hM (mul_nonneg (by norm_num) hL)) hell.le

namespace FirstGaussPoolData

variable {C : A.GeneralArithmeticContext σ η htrace}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

/-- The enlarged norm window follows from the original row window
and the actual single sixth-power prime insertion. -/
theorem main_originalFrequencyIdeal_norm_le (d : FirstGaussPoolData C P ι)
    (h : A.R) (hh : h ∈ d.mainRows) :
    A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ (d.rowExponent + 6 * ell) := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hh
  have hm : x.1 ∈ d.rows ∧ x.2 ∈ P.primes :=
    Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have hg := amplifiedExterior_generates C (d.rowIdeal x.1) x.2 x.1 (d.row_generates x.1 hm.1)
  have hi := generatedIdeal_unique
    (originalFrequencyIdeal_generates (actualFrequencyAmplify C x) hg.1) hg
  rw [hi]
  change (Ideal.absNorm (amplifiedExterior (d.rowIdeal x.1) x.2).val : ℝ) ≤ _
  simpa only [idealAmplify, amplifiedExterior_val] using
    idealAmplify_norm ((d.rowIdeal x.1).val, x.2.val.asIdeal) Z d.rowExponent ell
      (zero_lt_one.trans P.base_gt_one) (d.row_norm x.1 hm.1) (P.norm_upper x.2 hm.2)

theorem error_originalFrequencyIdeal_norm_le (d : FirstGaussPoolData C P ι)
    (p : ExteriorPrime A) (h : A.R) (hh : h ∈ d.errorRows p) :
    A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ d.rowExponent := by
  have hm : h ∈ d.rows := (Finset.mem_filter.mp hh).1
  have hi := generatedIdeal_unique
    (originalFrequencyIdeal_generates h (d.row_generates h hm).1) (d.row_generates h hm)
  rw [hi]
  exact d.row_norm h hm

/-- The pool keeps the exact orbital multiplicity of its actual main
row image. The earlier original representative recipe proves the input
injectivity; the enlarged rows need not be injective. -/
theorem main_orbit_fibres_le (d : FirstGaussPoolData C P ι)
    (source : Finset Q) (b : A.R) (hb : b ≠ 0)
    (horiginal : d.rows ⊆ source.image (fun q => q.out.val * b)) (q : Q) :
    ((d.mainRows.filter (fun h => engineElementOrbit (Γ := Γ) h = q)).card : ℝ) ≤
      d.multiplicity :=
  actualFrequencyAmplify_orbit_output_fibres C d.rows d.rowIdeal d.row_generates
    (engineOrbit_image_injOn source b hb d.rows horiginal)
    P.primes (fun h p => actualPrimeEligible d.frozen (d.rowIdeal h) p)
    Z (ell / 2) d.rowExponent ell P.base_gt_one
    (div_pos P.exponent_pos (by norm_num)) d.rowExponent_nonneg P.exponent_pos.le
    P.norm_lower P.norm_upper d.row_norm q

theorem main_orbit_multiplicity_le (d : FirstGaussPoolData C P ι)
    (source : Finset Q) (b : A.R) (hb : b ≠ 0)
    (horiginal : d.rows ⊆ source.image (fun q => q.out.val * b)) :
    engineOrbitMultiplicity (Γ := Γ) d.mainRows ≤ ⌈d.multiplicity⌉₊ := by
  apply engineOrbitMultiplicity_le
  intro q
  exact Nat.cast_le.mp ((d.main_orbit_fibres_le source b hb horiginal q).trans
    (Nat.le_ceil d.multiplicity))

/-- A fixed original exponent window chooses the integer fibre cap
before the scale, prime pool and moving source are used. -/
theorem main_orbit_multiplicity_le_uniform (M : ℝ)
    (d : FirstGaussPoolData C P ι) (hM : d.rowExponent ≤ M)
    (source : Finset Q) (b : A.R) (hb : b ≠ 0)
    (horiginal : d.rows ⊆ source.image (fun q => q.out.val * b)) :
    engineOrbitMultiplicity (Γ := Γ) d.mainRows ≤
      ⌈(M + 6 * ell) / (ell / 2)⌉₊ := by
  apply (d.main_orbit_multiplicity_le source b hb horiginal).trans
  apply Nat.ceil_le_ceil
  exact div_le_div_of_nonneg_right (add_le_add hM le_rfl)
    (div_nonneg P.exponent_pos.le (by norm_num))

/-- Valuation corrections use subsets of the same original signed
representative image, so they retain unit orbital fibres. -/
theorem error_orbit_multiplicity_le_one (d : FirstGaussPoolData C P ι)
    (source : Finset Q) (b : A.R) (hb : b ≠ 0)
    (horiginal : d.rows ⊆ source.image (fun q => q.out.val * b))
    (p : ExteriorPrime A) :
    engineOrbitMultiplicity (Γ := Γ) (d.errorRows p) ≤ 1 :=
  engineOrbit_image_multiplicity_le_one source b hb (d.errorRows p)
    ((Finset.filter_subset _ _).trans horiginal)

end FirstGaussPoolData

section CanonicalFirst

variable (C : A.GeneralArithmeticContext σ η htrace)
variable {ι κ : Type*} (left : Finset ι) (right : Finset κ)
variable (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
variable (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
variable (hDE : DE ∈ commonSupportPool left right
  (fun i => (fullI i).val) (fun j => (fullJ j).val))

theorem canonicalFirstLeftGaussData_orbit_multiplicity_le_one (rows : Finset Q) :
    engineOrbitMultiplicity (Γ := Γ)
      (canonicalFirstLeftGaussData C left right fullI fullJ DE hDE rows).rows ≤ 1 := by
  apply engineOrbit_image_multiplicity_le_one rows 1 one_ne_zero
  simpa only [mul_one] using (Finset.Subset.refl (rows.image (fun q : Q => q.out.val)))

theorem canonicalFirstRightGaussData_orbit_multiplicity_le_one (rows : Finset Q) :
    engineOrbitMultiplicity (Γ := Γ)
      (canonicalFirstRightGaussData C left right fullI fullJ DE hDE rows).rows ≤ 1 := by
  apply engineOrbit_image_multiplicity_le_one rows (-1) (neg_ne_zero.mpr one_ne_zero)
  simpa only [mul_neg_one] using
    (Finset.Subset.refl (rows.image (fun q : Q => -q.out.val)))

theorem canonicalFirstLeftGaussData_norm_le (rows : Finset Q)
    (R : ℝ) (hR : ∀ q ∈ rows,
      (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ q).val ≤ R)
    (h : A.R) (hh : h ∈
      (canonicalFirstLeftGaussData C left right fullI fullJ DE hDE rows).rows) :
    A.exteriorNorm (originalFrequencyIdeal h) ≤ R := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hh
  rw [originalFrequencyIdeal_out_norm]
  exact hR q hq

theorem canonicalFirstRightGaussData_norm_le (rows : Finset Q)
    (R : ℝ) (hR : ∀ q ∈ rows,
      (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ q).val ≤ R)
    (h : A.R) (hh : h ∈
      (canonicalFirstRightGaussData C left right fullI fullJ DE hDE rows).rows) :
    A.exteriorNorm (originalFrequencyIdeal h) ≤ R := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hh
  rw [originalFrequencyIdeal_neg_out_norm]
  exact hR q hq

end CanonicalFirst

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.engineOrbit_image_fibres_le_one
#print axioms HeckeSkeleton.Moments.EngineStep.actualFrequencyAmplify_orbit_fibre_count
#print axioms HeckeSkeleton.Moments.EngineStep.actualFrequencyAmplify_orbit_output_fibres
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.main_orbit_multiplicity_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.main_orbit_multiplicity_le_uniform
#print axioms HeckeSkeleton.Moments.EngineStep.canonicalFirstRightGaussData_orbit_multiplicity_le_one
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.main_originalFrequencyIdeal_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.canonicalFirstRightGaussData_norm_le
