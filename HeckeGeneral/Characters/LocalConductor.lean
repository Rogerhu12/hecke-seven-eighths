import HeckeGeneral.Characters.FiniteRamification
import HeckeGeneral.Characters.LocalUniformizer
import HeckeGeneral.Characters.PrincipalUnitFiltration
import HeckeGeneral.Arithmetic.IdealFactorization
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite local conductor depth

A continuous circle-valued character of a nonarchimedean local field is
trivial on a sufficiently small principal-unit neighborhood. We prove this
from continuity and the explicit circle arc lemma, then use the actual
residue cardinality to define the least conductor exponent. Depth zero
means triviality on all integral units. Positive depth n means triviality
on the principal units with norm of u - 1 at most q^(-n).
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain Filter Topology
open scoped Classical nonZeroDivisors

private theorem norm_pow_sub_one_le {F : Type*} [NormedField F] [IsUltrametricDist F]
    (x : F) (hx : ‖x - 1‖ ≤ 1) (n : ℕ) : ‖x ^ n - 1‖ ≤ ‖x - 1‖ := by
  have hnorm : ‖x‖ ≤ 1 := by
    calc
      ‖x‖ = ‖(x - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ max ‖x - 1‖ ‖(1 : F)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le hx (by simp)
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : x ^ (n + 1) - 1 = (x ^ n - 1) * x + (x - 1) := by ring
    rw [heq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)).trans (by simpa using ih)

/-- Continuity forces a genuine open neighborhood of local units into the kernel. -/
theorem exists_radius_trivial {F : Type*} [NormedField F] [IsUltrametricDist F]
    (χ : Fˣ →ₜ* Circle) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : Fˣ, ‖u.val - 1‖ < ε → χ u = 1 := by
  have hn : χ ⁻¹' circleSmallArc ∈ 𝓝 (1 : Fˣ) :=
    χ.continuous.continuousAt.preimage_mem_nhds
      (isOpen_circleSmallArc.mem_nhds (by simpa using one_mem_circleSmallArc))
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap] at hn
  obtain ⟨V, hV, hsub⟩ := Filter.mem_comap.mp hn
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨min δ 1, lt_min hδ zero_lt_one, fun u hu => ?_⟩
  apply circle_eq_one_of_powers_re
  intro n
  have hp : ‖(u ^ n).val - 1‖ < δ :=
    (norm_pow_sub_one_le u.val (le_trans hu.le (min_le_right _ _)) n).trans_lt
      (lt_of_lt_of_le hu (min_le_left _ _))
  have hv : (u ^ n).val ∈ V := hball (by simpa [Metric.mem_ball, dist_eq_norm] using hp)
  have hs := hsub hv
  change (1 / 2 : ℝ) < (χ (u ^ n) : ℂ).re at hs
  rw [map_pow] at hs
  exact hs.le

variable (K : Type*) [Field K] [NumberField K]

/-- The usual unit filtration, written using the normalized local norm. -/
def TrivialAtDepth (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) : ℕ → Prop
  | 0 => UnramifiedAt K χ v
  | n + 1 => ∀ u : (v.adicCompletion K)ˣ,
      ‖u.val - 1‖ ≤ (residueCard K v : ℝ)⁻¹ ^ (n + 1) → localComponent K v χ u = 1

theorem trivialAtDepth_mul_normTwist_iff (χ : HeckeCharacter K) (t : ℝ)
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    TrivialAtDepth K (χ * heckeNormTwist K t) v n ↔ TrivialAtDepth K χ v n := by
  cases n with
  | zero => exact unramifiedAt_mul_normTwist_iff K χ t v
  | succ n =>
    have he (u : (v.adicCompletion K)ˣ)
        (hu : ‖u.val - 1‖ ≤ (residueCard K v : ℝ)⁻¹ ^ (n + 1)) :
        localComponent K v (χ * heckeNormTwist K t) u = localComponent K v χ u := by
      change localComponent K v χ u * localComponent K v (heckeNormTwist K t) u = _
      rw [unramifiedAt_normTwist K t v u
        (principalUnit_norm_one K v u (n + 1) (Nat.succ_pos n) hu), mul_one]
    constructor
    · intro h u hu
      rw [← he u hu]
      exact h u hu
    · intro h u hu
      rw [he u hu]
      exact h u hu

theorem exists_trivialAtDepth (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℕ, TrivialAtDepth K χ v n := by
  obtain ⟨ε, hε, hχ⟩ := exists_radius_trivial (localComponent K v χ)
  have hq : (1 : ℝ) < residueCard K v := by exact_mod_cast one_lt_residueCard K v
  have hinv : (residueCard K v : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hinv
  refine ⟨n + 1, fun u hu => hχ u (hu.trans_lt ?_)⟩
  have hpow : (residueCard K v : ℝ)⁻¹ ^ (n + 1) ≤ (residueCard K v : ℝ)⁻¹ ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (by positivity) hinv.le
  exact hpow.trans_lt hn

/-- The least depth at which the actual local character is trivial. -/
def localConductorExponent (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Nat.find (exists_trivialAtDepth K χ v)

theorem trivialAtDepth_localConductorExponent (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) : TrivialAtDepth K χ v (localConductorExponent K χ v) :=
  Nat.find_spec (exists_trivialAtDepth K χ v)

theorem localConductorExponent_le (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : TrivialAtDepth K χ v n) :
    localConductorExponent K χ v ≤ n := Nat.find_min' (exists_trivialAtDepth K χ v) hn

theorem localConductorExponent_eq_zero_iff (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) :
    localConductorExponent K χ v = 0 ↔ UnramifiedAt K χ v := by
  exact Nat.find_eq_zero (exists_trivialAtDepth K χ v)

theorem localConductorExponent_mul_normTwist (χ : HeckeCharacter K) (t : ℝ)
    (v : HeightOneSpectrum (𝓞 K)) :
    localConductorExponent K (χ * heckeNormTwist K t) v = localConductorExponent K χ v := by
  apply le_antisymm
  · exact localConductorExponent_le K _ v
      ((trivialAtDepth_mul_normTwist_iff K χ t v _).mpr
        (trivialAtDepth_localConductorExponent K χ v))
  · exact localConductorExponent_le K χ v
      ((trivialAtDepth_mul_normTwist_iff K χ t v _).mp
        (trivialAtDepth_localConductorExponent K _ v))

theorem finite_localConductor_support (χ : HeckeCharacter K) :
    {v : HeightOneSpectrum (𝓞 K) | localConductorExponent K χ v ≠ 0}.Finite := by
  simpa only [ne_eq, localConductorExponent_eq_zero_iff] using finite_ramifiedPlaces K χ

/-- The finite exponent vector of the actual local conductor depths. -/
def conductorExponents (χ : HeckeCharacter K) : HeightOneSpectrum (𝓞 K) →₀ ℕ :=
  Finsupp.ofSupportFinite (localConductorExponent K χ) (finite_localConductor_support K χ)

@[simp] theorem conductorExponents_apply (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) :
    conductorExponents K χ v = localConductorExponent K χ v := rfl

/-- The nonzero integral conductor ideal from the proved finite local depths. -/
def finiteConductor (χ : HeckeCharacter K) : (Ideal (𝓞 K))⁰ :=
  Arithmetic.idealOfPrimeExponents (conductorExponents K χ)

@[simp] theorem primeExponents_finiteConductor (χ : HeckeCharacter K) :
    Arithmetic.primeExponents (finiteConductor K χ) = conductorExponents K χ :=
  Arithmetic.primeExponents_idealOfPrimeExponents _

theorem finiteConductor_mul_normTwist (χ : HeckeCharacter K) (t : ℝ) :
    finiteConductor K (χ * heckeNormTwist K t) = finiteConductor K χ := by
  have he : conductorExponents K (χ * heckeNormTwist K t) = conductorExponents K χ := by
    ext v
    exact localConductorExponent_mul_normTwist K χ t v
  simp only [finiteConductor, he]

@[simp] theorem localConductorExponent_normTwist (t : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    localConductorExponent K (heckeNormTwist K t) v = 0 :=
  (localConductorExponent_eq_zero_iff K _ v).mpr (unramifiedAt_normTwist K t v)

@[simp] theorem finiteConductor_normTwist (t : ℝ) :
    finiteConductor K (heckeNormTwist K t) = 1 := by
  have he : conductorExponents K (heckeNormTwist K t) = 0 := by ext v; simp
  simp [finiteConductor, he]

end HeckeGeneral.Characters
