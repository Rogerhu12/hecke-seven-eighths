import GeneratorMaskWitness
import ActualRowBallDualChartIntegrand
import ActualGramJointKernelIdentification
import HeckeGeneral.Analysis.SUnitPartitionCovariance

/-!
UNCOMPILED / native 0. For the SAME adjusted-generator witness, membership
in its finite-S sextic complement identifies exactly the original
sixth-power-unit orbit of the generator of the actual contracted ideal.
No orbit-selection, principalization or local-global detection premise
is supplied. An actual two-column unit-partition insertion is also proved
for the row-ball dual pair integrand, with c identically one.

The finite-local mask below contains NO archimedean coordinate. Its local
constancy, a usable fixed-depth congruence period on the actual valuation
box, and preservation of the exterior complete mean are not asserted here.
In particular, this is not permission to apply the unmasked whole-column
cancellation bound to a chosen-generator subset.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualGeneratorChoiceDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.AllowedGeneratorConstruction
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open ActualProbeGaussFourierDraft ActualProbePairOrbitalDraft
open ActualRowBallDualChartDraft ActualGramJointKernelDraft
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)

local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer S K
local notation "NZ" => NonzeroRingElements OS
local notation "E" => ExteriorIdeal K S
local notation "Γ" => sixthPowerUnits K S
local notation "OQ" => SIntegerOrbits K S Γ

/-- The ordinary exterior ideal of the ACTUAL nonzero S-integer. -/
def choiceColumnIdeal (m : NZ) : E :=
  ⟨⟨sIntegerModulusContraction K S m.val,
    mem_nonZeroDivisors_of_ne_zero (sIntegerModulusContraction_ne_bot K S m.val m.property)⟩,
    by
      intro p hp hpS
      have hcop := sIntegerModulusContraction_coprime K S m.val m.property p hpS
      have hle := Ideal.dvd_iff_le.mp hp
      exact p.isPrime.ne_top ((sup_of_le_right hle).symm.trans hcop)⟩

theorem choiceColumnIdeal_generator_span (m : NZ) :
    Ideal.span ({w.D.generator (choiceColumnIdeal K w m)} : Set OS) =
      Ideal.span ({m.val} : Set OS) := by
  rw [w.D.generator_span]
  exact map_sIntegerModulusContraction K S m.val

/-- Literal sextic power-class quotient on the finite S-local unit product.
There is no real/complex place or infinity condition in this definition. -/
def choiceFiniteClassHom : SFiniteLocalGroup K S →*
    sameSLocalPowerQuotients K w.S 6 where
  toFun x v := QuotientGroup.mk' _ (x v)
  map_one' := by ext v; simp
  map_mul' x y := by ext v; simp

@[simp] theorem choiceFiniteClassHom_diagonal (m : NZ) :
    choiceFiniteClassHom K w (sLocalNonzeroIntegerDiagonal K S m).2 =
      fieldLocalPowerClassHom K w.S 6 (nonzeroSIntegerFieldUnit K S m) := rfl

/-- The actual generator-choice mask on finite local coordinates only. -/
def choiceFiniteMask (x : SFiniteLocalGroup K S) : ℂ :=
  if choiceFiniteClassHom K w x ∈ w.C6 then 1 else 0

/-- A genuine coordinatewise sixth power is killed by the actual quotient. -/
theorem choiceFiniteClassHom_pow_six (x : SFiniteLocalGroup K S) :
    choiceFiniteClassHom K w (x ^ 6) = 1 := by
  rw [map_pow]
  exact sameSLocalPowerQuotients_pow_eq_one K w.S 6 _

/-- Multiplicative sixth-power invariance is algebraic; it does not assert
an additive congruence period or local constancy at zero. -/
theorem choiceFiniteMask_mul_sixth (x y : SFiniteLocalGroup K S) :
    choiceFiniteMask K w (y ^ 6 * x) = choiceFiniteMask K w x := by
  unfold choiceFiniteMask
  rw [map_mul, choiceFiniteClassHom_pow_six, sameSLocalPowerQuotients_one_mul]

theorem choiceFiniteClassHom_gamma (u : Γ) :
    choiceFiniteClassHom K w (sLocalDiagonal K S u.val).2 = 1 := by
  have hq : QuotientGroup.mk'
      (powMonoidHom 6 : (S).unit K →* (S).unit K).range u.val = 1 :=
    (QuotientGroup.eq_one_iff u.val).mpr u.property
  change sUnitPowerLocalization K w.S 6 (QuotientGroup.mk' _ u.val) = 1
  rw [hq, map_one]

/-- The SAME original Gamma action preserves the finite choice mask. -/
theorem choiceFiniteMask_gamma_mul (u : Γ) (x : SFiniteLocalGroup K S) :
    choiceFiniteMask K w ((sLocalDiagonal K S u.val).2 * x) =
      choiceFiniteMask K w x := by
  unfold choiceFiniteMask
  rw [map_mul, choiceFiniteClassHom_gamma, sameSLocalPowerQuotients_one_mul]

/-- Complement disjointness and actual injectivity force a true global
sixth power; the unit relating the two generators is not assumed to lie
in Gamma and is not replaced by a scalar phase. -/
theorem class_mem_iff_generator_orbit_of_span
    (I : E) (m : NZ)
    (hspan : Ideal.span ({w.D.generator I} : Set OS) = Ideal.span ({m.val} : Set OS)) :
    fieldLocalPowerClassHom K w.S 6 (nonzeroSIntegerFieldUnit K S m) ∈ w.C6 ↔
      (Quotient.mk _ m : OQ) = Quotient.mk _ (probeGenerator K S w.D I) := by
  constructor
  · intro hm
    obtain ⟨u, hu⟩ := exists_sUnit_ratio_of_span_eq K w.S _ _ hspan
    have hfield : nonzeroSIntegerFieldUnit K S m = (u : Kˣ) *
        generatorFieldUnit K w.S w.D I := by
      apply Units.ext
      exact congrArg (fun a : OS => (a : K)) hu
    have hp := congrArg (fieldLocalPowerClassHom K w.S 6) hfield
    rw [map_mul] at hp
    change fieldLocalPowerClassHom K w.S 6 (nonzeroSIntegerFieldUnit K S m) =
      fieldLocalPowerClassHom K w.S 6 (u : Kˣ) * generatorSameSClass K w.S w.D I at hp
    have huC : fieldLocalPowerClassHom K w.S 6 (u : Kˣ) ∈ w.C6 := by
      have heq : fieldLocalPowerClassHom K w.S 6 (u : Kˣ) =
          fieldLocalPowerClassHom K w.S 6 (nonzeroSIntegerFieldUnit K S m) /
            generatorSameSClass K w.S w.D I := by
        exact sameSLocalPowerQuotients_eq_div_of_mul_eq K w.S 6 hp.symm
      rw [heq]
      exact w.C6.div_mem hm (w.generator_class_mem I)
    have huE : fieldLocalPowerClassHom K w.S 6 (u : Kˣ) ∈
        (sUnitPowerLocalization K w.S 6).range :=
      ⟨QuotientGroup.mk' _ u, sUnitPowerLocalization_mk K w.S 6 u⟩
    have huone : fieldLocalPowerClassHom K w.S 6 (u : Kˣ) = 1 :=
      (Subgroup.disjoint_def.mp w.disjoint6) huE huC
    have hq : QuotientGroup.mk'
        (powMonoidHom 6 : (S).unit K →* (S).unit K).range u = 1 := by
      apply w.localization_injective
      rw [sUnitPowerLocalization_mk, map_one]
      exact huone
    have huΓ : u ∈ Γ := (QuotientGroup.eq_one_iff u).mp hq
    apply Quotient.sound
    apply (sIntegerOrbitRelation_iff K S Γ m (probeGenerator K S w.D I)).mpr
    refine ⟨⟨u, huΓ⟩, ?_⟩
    exact (congrArg (fun a : OS => (a : K)) hu).symm
  · intro hm
    obtain ⟨u, hu⟩ := (sIntegerOrbitRelation_iff K S Γ m
      (probeGenerator K S w.D I)).mp (Quotient.exact hm)
    have hq : QuotientGroup.mk'
        (powMonoidHom 6 : (S).unit K →* (S).unit K).range u.val = 1 :=
      (QuotientGroup.eq_one_iff u.val).mpr u.property
    have huone := congrArg (sUnitPowerLocalization K w.S 6) hq
    rw [sUnitPowerLocalization_mk, map_one] at huone
    have hfield : nonzeroSIntegerFieldUnit K S m = (u.val : Kˣ) *
        generatorFieldUnit K w.S w.D I := by
      apply Units.ext
      exact hu.symm
    have hp := congrArg (fieldLocalPowerClassHom K w.S 6) hfield
    rw [map_mul, huone] at hp
    replace hp := hp.trans (sameSLocalPowerQuotients_one_mul K w.S 6 _)
    change fieldLocalPowerClassHom K w.S 6 (nonzeroSIntegerFieldUnit K S m) =
      generatorSameSClass K w.S w.D I at hp
    rw [hp]
    exact w.generator_class_mem I

/-- No principal-span premise remains: the ideal is the real contraction. -/
theorem choiceFiniteMask_diagonal (m : NZ) :
    choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m).2 =
      if (Quotient.mk _ m : OQ) =
        Quotient.mk _ (probeGenerator K S w.D (choiceColumnIdeal K w m)) then 1 else 0 := by
  unfold choiceFiniteMask
  rw [choiceFiniteClassHom_diagonal,
    class_mem_iff_generator_orbit_of_span K w (choiceColumnIdeal K w m) m
      (choiceColumnIdeal_generator_span K w m)]
  congr

@[simp] theorem choiceFiniteMask_generator (I : E) :
    choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S
      (probeGenerator K S w.D I)).2 = 1 := by
  unfold choiceFiniteMask
  rw [choiceFiniteClassHom_diagonal]
  change (if generatorSameSClass K w.S w.D I ∈ w.C6 then (1 : ℂ) else 0) = 1
  exact if_pos (w.generator_class_mem I)

@[simp] theorem choiceFiniteMask_generator_translate (I : E) (u : Γ) :
    choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S
      (sIntegerOrbitTranslate K S Γ u (probeGenerator K S w.D I))).2 = 1 := by
  rw [sLocalNonzeroIntegerDiagonal_translate]
  change choiceFiniteMask K w ((sLocalDiagonal K S u.val).2 *
    (sLocalNonzeroIntegerDiagonal K S (probeGenerator K S w.D I)).2) = 1
  rw [choiceFiniteMask_gamma_mul, choiceFiniteMask_generator]

/-- The literal mask selects precisely the union of the original Gamma
orbits of the SAME chosen generators; no unit sector is silently dropped. -/
theorem choiceFiniteMask_eq_one_iff_generator_translate (m : NZ) :
    choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m).2 = 1 ↔
      ∃ I : E, ∃ u : Γ, m =
        sIntegerOrbitTranslate K S Γ u (probeGenerator K S w.D I) := by
  constructor
  · intro hm
    rw [choiceFiniteMask_diagonal] at hm
    have heq : (Quotient.mk _ m : OQ) =
        Quotient.mk _ (probeGenerator K S w.D (choiceColumnIdeal K w m)) := by
      by_contra hn
      simp only [if_neg hn] at hm
      exact zero_ne_one hm
    obtain ⟨u, hu⟩ := (sIntegerOrbitRelation_iff K S Γ m
      (probeGenerator K S w.D (choiceColumnIdeal K w m))).mp (Quotient.exact heq)
    refine ⟨choiceColumnIdeal K w m, u, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hu.symm
  · rintro ⟨I, u, rfl⟩
    exact choiceFiniteMask_generator_translate K w I u

end HeckeGeneral.ThetaSkeleton.Physical.ActualGeneratorChoiceDraft

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualGeneratorChoiceDraft

open NumberField IsDedekindDomain MeasureTheory HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open ActualGramJointKernelDraft ActualRowBallDualChartDraft ActualProbePairOrbitalDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "SF" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Γ" => sixthPowerUnits K SF
local notation "E" => ExteriorIdeal K SF
local notation "OQ" => SIntegerOrbits K SF Γ

local instance choice_sixthUnits_finiteIndex : Subgroup.FiniteIndex Γ :=
  sUnit_power_range_finiteIndex K SF 6 (by decide)

/-- A genuine partition on translates of the SAME normalized generator
column, retaining its moving finite coordinate. -/
def generatorColumnPartition (D : ThetaArithmeticData K SF) (I : E)
    (Y : ℝ) (hY : 0 < Y) (u : Γ) : ℝ :=
  sUnitNormalizedPartitionArchPullback K SF Γ
    ((sLocalDiagonal K SF u.val).2 * additiveGramColumnFinite K S D I Y hY)
    (sUnitPartitionArchTranslate K SF Γ u (additiveGramColumnArch K S D I Y hY)).val

theorem tsum_generatorColumnPartition (D : ThetaArithmeticData K SF) (I : E)
    (Y : ℝ) (hY : 0 < Y) :
    (∑' u : Γ, generatorColumnPartition K S D I Y hY u) = 1 :=
  sUnitNormalizedPartitionArchPullback_partition K SF Γ
    (additiveGramColumnFinite K S D I Y hY) (additiveGramColumnArch K S D I Y hY)

/-- The annular factors on the two actual columns are reconstructed with
independent original-Gamma sums, not one simultaneous unit translate. -/
theorem generatorColumns_annular_partition (D : ThetaArithmeticData K SF)
    (I J : E) (Y : ℝ) (hY : 0 < Y) (a : ℝ → ℝ) :
    (∑' u : Γ, ∑' v : Γ,
      sUnitAnnularPartitionCutoff K SF Γ a
        ((sLocalDiagonal K SF u.val).2 * additiveGramColumnFinite K S D I Y hY)
        (sUnitPartitionArchTranslate K SF Γ u (additiveGramColumnArch K S D I Y hY)).val *
      sUnitAnnularPartitionCutoff K SF Γ a
        ((sLocalDiagonal K SF v.val).2 * additiveGramColumnFinite K S D J Y hY)
        (sUnitPartitionArchTranslate K SF Γ v (additiveGramColumnArch K S D J Y hY)).val) =
      a (exteriorNorm K SF I / Y) * a (exteriorNorm K SF J / Y) := by
  rw [sUnitAnnularPartitionCutoff_two_column,
    additiveGramColumn_totalNorm, additiveGramColumn_totalNorm]

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- Actual c=1 row-ball pair integrand, with its genuine Fourier profile,
reconstructed by two unit partitions. The arithmetic coefficient is still
the original ideal-pair value; no invariance of an artificial extension or
identification with an unmasked whole-column sum is asserted. -/
theorem rowBallDual_pair_partition (P : ProbeData K SF) (W : SmoothAnnularTest)
    (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}) (q : OQ) (I J : E) :
    (∑' u : Γ, ∑' v : Γ,
      (generatorColumnPartition K S P.arithmetic I Y hY u : ℂ) *
      (generatorColumnPartition K S P.arithmetic J Y hY v : ℂ) *
      (rowBallDualSpectralCoefficient K S μv P W Y η r q I J *
        probeOriginalCorrelationOrbitWeight K S P I J q)) =
      rowBallDualSpectralCoefficient K S μv P W Y η r q I J *
        probeOriginalCorrelationOrbitWeight K S P I J q := by
  simp only [← mul_assoc, tsum_mul_right, tsum_mul_left,
    ← Complex.ofReal_tsum, tsum_generatorColumnPartition, Complex.ofReal_one, one_mul]

end HeckeGeneral.ThetaSkeleton.Physical.ActualGeneratorChoiceDraft
