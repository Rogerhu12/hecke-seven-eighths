import HeckeGeneral.Analysis.MomentInputs
import HeckeGeneral.Analysis.SixthPowerFreeFactorization
import ArithmeticFrequencyRowCharacterFibers
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

/-!
# Numerical regions and eventual eligibility of the actual frequency rows

The numerical region requires nonnegative lengths.  Paired-row eligibility
also requires the actual allowed-row predicate, the norm upper bound, and
a lower cutoff on the sixth-power-free base.  The cutoff is uniform over
a fixed finite character family and is constructed from the genuine finite
character fibers; it does not require that those characters are unramified
outside the original set of places.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators

/-- The revised paired region retains the full interval up to one and the
unrestricted zero-slot alternative. -/
def FullPRegion (a : RealParameters) : Prop :=
  3 / 4 ≤ a.κ ∧ a.κ ≤ 1 ∧
    (a.z = 0 ∨ (0 < a.z ∧ a.n₁ + a.n₂ + 6 * a.κ * a.z ≤ a.m + a.q))

/-- A positive loss supplies both strict inverse margins. -/
theorem inverse_region_of_capacity
    (r z lam κ : ℝ) (hr : 0 ≤ r) (hz : 0 ≤ z) (hlam : 0 < lam)
    (hfirst : r + 2 * z ≤ 1 - 2 * lam)
    (hsecond : 2 * r + 8 * z ≤ 3 - 2 * lam) :
    MIRegion ⟨1, r, z, 0, 0, 0, κ⟩ := by
  refine ⟨zero_le_one, hr, hz, ?_, ?_⟩ <;> dsimp <;> linarith

/-- The full paired capacity includes the endpoint κ = 1. -/
theorem paired_region_of_capacity
    (B n z : ℝ) (hB : 7 / 8 ≤ B) (hB' : B ≤ 1) (hz : 0 ≤ z)
    (hcapacity : 2 * n + 6 * (2 * B - 1) * z ≤ 1) :
    FullPRegion ⟨1, 0, z, 0, n, n, 2 * B - 1⟩ := by
  refine ⟨by dsimp; linarith, by dsimp; linarith, ?_⟩
  by_cases hzero : z = 0
  · exact Or.inl hzero
  · right
    constructor
    · dsimp
      exact lt_of_le_of_ne hz (Ne.symm hzero)
    · dsimp
      linarith

/-- At zero slots the plain lengths have no capacity restriction. -/
theorem paired_region_zero_slot
    (B m r q n₁ n₂ : ℝ) (hB : 7 / 8 ≤ B) (hB' : B ≤ 1) :
    FullPRegion ⟨m, r, 0, q, n₁, n₂, 2 * B - 1⟩ := by
  refine ⟨by dsimp; linarith, by dsimp; linarith, Or.inl rfl⟩

/-- A genuine high-bin witness supplies the nonnegative lengths used by
both region tests.  The caller retains its exact inverse and paired
capacity inequalities, including the full endpoint `B = 1`. -/
theorem blockSource_moment_regions
    {Row : Type} {g : PrimeWindowGeometry} {b : ModerateBlock Row g.slots}
    {B lam k Z : ℝ} (hb : BlockSource g b B lam k Z)
    (hB : 7 / 8 ≤ B) (hB' : B ≤ 1) (hlam : 0 < lam)
    (hbin : 51 / 100 < b.bin) (ℓ : b.Label) (t : ℝ)
    (ht : 1 ≤ t) (ht' : t ≤ 3 / 2)
    (j : Fin ((b.amplitudeSet ℓ).subdivisionCount t))
    (I : Finset (Fin g.slots)) :
    let r := ((b.amplitudeSet ℓ).subdivision t j).inverseLength
    let n := ((b.amplitudeSet ℓ).subdivision t j).plainLength
    let z := ∑ _j ∈ I, HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots b.shell
    (r + 2 * z ≤ 1 - 2 * lam ∧ 2 * r + 8 * z ≤ 3 - 2 * lam →
      MIRegion ⟨1, r, z, 0, 0, 0, 2 * B - 1⟩) ∧
    (2 * n + 6 * (2 * B - 1) * z ≤ 1 →
      FullPRegion ⟨1, 0, z, 0, n, n, 2 * B - 1⟩) := by
  dsimp only
  have hr := (blockSource_witness_lengths hb hbin ℓ t ht ht' j).1
  have hz := blockSource_selected_length_nonneg hb I
  constructor
  · rintro ⟨hfirst, hsecond⟩
    exact inverse_region_of_capacity _ _ _ _ hr hz hlam hfirst hsecond
  · intro hcapacity
    exact paired_region_of_capacity _ _ _ hB hB' hz hcapacity

variable {K : Type} [Field K] [NumberField K]
variable {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]

/-- The original ideal and original sector recover the complete physical row. -/
theorem frequencyRow_ideal_sector_injective :
    Function.Injective (fun u : FrequencyRow K S => (u.ideal.val, u.sector)) := by
  intro u v h
  have hideal : u.ideal = v.ideal := Subtype.ext (congrArg Prod.fst h)
  have hsector : u.sector = v.sector := congrArg Prod.snd h
  cases u
  cases v
  cases hideal
  cases hsector
  rfl

/-- The arithmetic base already carries the true sixth-power-free predicate. -/
theorem frequencyRow_sixthPowerFree (u : FrequencyRow K S) :
    SixthPowerFreeIdeal u.ideal.val :=
  (sixthPowerFreeIdeal_iff_primeExponents_lt u.ideal.val).mpr u.sixthPowerFree

/-- The physical row envelope has exactly its stated upper norm scale. -/
theorem frequencyRows_idealNorm_le
    (U : ℝ) (hU : 0 ≤ U) (u : FrequencyRow K S)
    (hu : u ∈ frequencyRows K S U) : idealNorm K u.ideal.val ≤ U := by
  unfold frequencyRows at hu
  obtain ⟨⟨I, s⟩, _, rfl⟩ := Finset.mem_image.mp hu
  have hI := (Finset.mem_filter.mp I.property).1
  have hnorm := (mem_dyadicIdealSupport_iff K
    (div_nonneg hU (by norm_num : (0 : ℝ) ≤ 2)) I.val).mp hI
  change idealNorm K I.val ≤ U
  linarith

variable (K S)

/-- A single positive cutoff excludes every member of a fixed finite family.
It is imposed on the sixth-free base norm, before inserting any amplifier. -/
theorem finite_character_family_cutoff
    (P : ProbeData K S) (Θ : Finset (HeckeCharacter K)) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : FrequencyRow K S,
      C < frequencyRowNorm K S u → arithmeticRowCharacter K S P u ∉ Θ := by
  let E := {u : FrequencyRow K S // arithmeticRowCharacter K S P u ∈ Θ}
  letI : Finite E := arithmeticRowCharacter_finiteFamily_finite K S P Θ
  letI : Fintype E := Fintype.ofFinite E
  let C : ℝ := (∑ v : E, |frequencyRowNorm K S v.val|) + 1
  have hsum : 0 ≤ ∑ v : E, |frequencyRowNorm K S v.val| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro u hlarge hmem
  let v : E := ⟨u, hmem⟩
  have hterm : |frequencyRowNorm K S u| ≤
      ∑ w : E, |frequencyRowNorm K S w.val| :=
    Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
  have hu := le_abs_self (frequencyRowNorm K S u)
  dsimp [C] at hlarge
  linarith

variable {K S}
variable {ω ψ : HeckeCharacter K}

/-- Choosing the slot coefficients in the original finite theta family
supplies finite order at every slot. -/
theorem slot_coefficients_finite_of_mem_theta
    (d : MomentData K ω ψ)
    (hslots : ∀ j, d.slotCoefficient j ∈ d.theta) :
    ∀ j, FiniteOrder (d.slotCoefficient j) :=
  fun j => d.theta_finite _ (hslots j)

/-- The three permitted plain backgrounds form one fixed exceptional
family, even when the target character has infinite order. -/
theorem plain_background_inverse_mem (d : MomentData K ω ψ) :
    d.plainBackground⁻¹ ∈ ({1, ψ, ψ⁻¹} : Finset (HeckeCharacter K)) := by
  rcases d.plain_background_spec with h | h | h <;> simp [h]

/-- The row enumeration is exhaustive for the actual arithmetic predicate
and its stated norm upper bound. -/
theorem inverse_row_mem_of_allowed_norm
    (d : MomentData K ω ψ) (u : FrequencyRow K S) (U : ℝ)
    (hallowed : d.allowedRow u.ideal.val)
    (hnorm : idealNorm K u.ideal.val ≤ U) :
    u.ideal.val ∈ d.rows U :=
  (d.rows_spec U u.ideal.val).mpr ⟨hallowed, hnorm⟩

/-- Unmarked row membership retains the complete sixth-free filter. -/
theorem unmarked_row_mem_of_allowed_norm
    (d : MomentData K ω ψ) (u : FrequencyRow K S) (U : ℝ)
    (hallowed : d.allowedRow u.ideal.val)
    (hnorm : idealNorm K u.ideal.val ≤ 2 * U) :
    u.ideal.val ∈ (d.rows (2 * U)).filter SixthPowerFreeIdeal := by
  exact Finset.mem_filter.mpr
    ⟨inverse_row_mem_of_allowed_norm d u (2 * U) hallowed hnorm,
      frequencyRow_sixthPowerFree u⟩

/-- One fixed exceptional family handles both true branches of `pairedRows`:
finite theta exclusion for positive slots and the actual principal character
exclusion at zero slots. -/
theorem paired_row_mem_of_character_exclusion
    (P : ProbeData K S) (Θ : Finset (HeckeCharacter K))
    (d : MomentData K ω ψ) (a : RealParameters) (Z : ℝ)
    (u : FrequencyRow K S)
    (hcharacter : d.rowCharacter u.ideal.val = arithmeticRowCharacter K S P u)
    (htheta : d.theta ⊆ Θ) (hbackground : d.plainBackground⁻¹ ∈ Θ)
    (hexcluded : arithmeticRowCharacter K S P u ∉ Θ)
    (hallowed : d.allowedRow u.ideal.val)
    (hnorm : idealNorm K u.ideal.val ≤ Z ^ (a.m + a.q)) :
    u.ideal.val ∈ pairedRows d a Z := by
  apply Finset.mem_filter.mpr
  refine ⟨inverse_row_mem_of_allowed_norm d u _ hallowed hnorm, ?_⟩
  split_ifs with hzero
  · intro hprincipal
    have heq : d.rowCharacter u.ideal.val = d.plainBackground⁻¹ :=
      eq_inv_of_mul_eq_one_right hprincipal
    apply hexcluded
    rw [← hcharacter, heq]
    exact hbackground
  · intro hmem
    exact hexcluded (hcharacter ▸ htheta hmem)

variable (K S)

/-- The cutoff is chosen before the scale, the model, or the slot branch.
Only the true local calibration and arithmetic membership data remain as
premises when it is applied to an actual model family. -/
theorem paired_rows_eventual_eligibility
    (P : ProbeData K S) (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ω : HeckeCharacter K) (d : MomentData K ω ψ)
        (a : RealParameters) (Z : ℝ) (u : FrequencyRow K S),
        d.rowCharacter u.ideal.val = arithmeticRowCharacter K S P u →
        d.theta ⊆ Θ →
        C < frequencyRowNorm K S u → d.allowedRow u.ideal.val →
        idealNorm K u.ideal.val ≤ Z ^ (a.m + a.q) →
        u.ideal.val ∈ pairedRows d a Z := by
  let E := Θ ∪ ({1, ψ, ψ⁻¹} : Finset (HeckeCharacter K))
  obtain ⟨C, hC, hcutoff⟩ := finite_character_family_cutoff K S P E
  refine ⟨C, hC, ?_⟩
  intro ω d a Z u hcharacter htheta hlarge hallowed hnorm
  have htheta' : d.theta ⊆ E := by
    intro χ hχ
    exact Finset.mem_union.mpr (Or.inl (htheta hχ))
  have hbackground : d.plainBackground⁻¹ ∈ E :=
    Finset.mem_union.mpr (Or.inr (plain_background_inverse_mem d))
  exact paired_row_mem_of_character_exclusion P E d a Z u hcharacter
    htheta' hbackground (hcutoff u hlarge) hallowed hnorm

end HeckeSkeleton.Moments.UniformAmplify
