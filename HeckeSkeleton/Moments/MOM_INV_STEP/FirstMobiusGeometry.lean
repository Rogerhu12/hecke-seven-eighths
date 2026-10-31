import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCompletePools
import HeckeSkeleton.Moments.MOM_INV_STEP.FullMobius

/-!
# Actual overlap divisors of the first positive source

Every divisor in the full Möbius pool is a nonzero squarefree exterior
ideal. Its support and norm bounds are derived from an actual member of
the original independent residual domain, not supplied separately.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstMobiusGeometry

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOMInvStep.FullMobius
open FirstSourceReindexing FirstNormPoolEnergy FirstCompletePools CanonicalNormPools IdealMobiusMask
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

def overlapPool (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext) (side : Bool) :=
  divisorPool (sideDomain K S (dyadicPool K Sset X.val) r₁ r₂ b₁ b₂ side)
    (fun U => primeProduct U)

theorem overlap_exists_source (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext) (side : Bool)
    (e : Ideal (𝓞 K)) (he : e ∈ overlapPool K S X r₁ r₂ b₁ b₂ side) :
    ∃ U ∈ sideDomain K S (dyadicPool K Sset X.val) r₁ r₂ b₁ b₂ side,
      e ∣ primeProduct U := by
  obtain ⟨U,hU,he⟩ := Finset.mem_biUnion.mp he
  exact ⟨U,hU,(mem_idealDivisors (primeProduct_ne_bot U)).mp he⟩

theorem overlap_nonzero (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext) (side : Bool)
    (e : Ideal (𝓞 K)) (he : e ∈ overlapPool K S X r₁ r₂ b₁ b₂ side) : e ≠ 0 := by
  obtain ⟨U,hU,heU⟩ := overlap_exists_source K S X r₁ r₂ b₁ b₂ side e he
  exact ne_zero_of_dvd_ne_zero (primeProduct_ne_bot U) heU

theorem overlap_squarefree (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext) (side : Bool)
    (e : Ideal (𝓞 K)) (he : e ∈ overlapPool K S X r₁ r₂ b₁ b₂ side) : Squarefree e := by
  obtain ⟨U,hU,heU⟩ := overlap_exists_source K S X r₁ r₂ b₁ b₂ side e he
  exact (squarefree_primeProduct U).of_dvd heU

include D in
theorem overlap_outside (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext) (side : Bool)
    (e : Ideal (𝓞 K)) (he : e ∈ overlapPool K S X r₁ r₂ b₁ b₂ side) :
    ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ e → p ∉ Sset := by
  obtain ⟨U,hU,heU⟩ := overlap_exists_source K S X r₁ r₂ b₁ b₂ side e he
  intro p hp
  exact sideDomain_exterior K S D X r₁ r₂ b₁ b₂ side U hU p (hp.trans heU)

def overlapIdeal (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext) (side : Bool)
    (e : overlapPool K S X r₁ r₂ b₁ b₂ side) : Ext :=
  ⟨⟨e.val, mem_nonZeroDivisors_of_ne_zero
      (overlap_nonzero K S X r₁ r₂ b₁ b₂ side e.val e.property)⟩,
    overlap_outside K S D X r₁ r₂ b₁ b₂ side e.val e.property⟩

@[simp] theorem overlapIdeal_val (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext) (side : Bool)
    (e : overlapPool K S X r₁ r₂ b₁ b₂ side) :
    (overlapIdeal K S D X r₁ r₂ b₁ b₂ side e).val.val = e.val := rfl

include D in
theorem overlap_norm_le (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext) (side : Bool)
    (e : Ideal (𝓞 K)) (he : e ∈ overlapPool K S X r₁ r₂ b₁ b₂ side) :
    (e.absNorm : ℝ) ≤ 2 * (residualScale K S X r₁ r₂ b₁ b₂ side).val := by
  obtain ⟨U,hU,heU⟩ := overlap_exists_source K S X r₁ r₂ b₁ b₂ side e he
  have hn : e.absNorm ≤ (primeProduct U).absNorm :=
    Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors (nonzeroProduct U))
      (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp heU))
  exact (by exact_mod_cast hn).trans
    (domain_height_window K S D X r₁ r₂ b₁ b₂ side U hU).2

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstMobiusGeometry

end

