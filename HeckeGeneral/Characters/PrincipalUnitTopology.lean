import HeckeGeneral.Characters.LocalResidueTower
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.LocallyConstant.Basic

/-! Openness of actual principal units and continuous characters of finite residue depth. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain Filter Topology
open scoped Classical

theorem monoidHom_locallyConstant_of_open_kernel {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [IsTopologicalGroup G] (f : G →* H)
    (hf : IsOpen (f.ker : Set G)) : IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have he : (fun y : G => y * x⁻¹) ⁻¹' (f.ker : Set G) ∈ 𝓝 x :=
    (continuous_id.mul_const x⁻¹).continuousAt.preimage_mem_nhds
      (hf.mem_nhds (by simp))
  filter_upwards [he] with y hy
  change f (y * x⁻¹) = 1 at hy
  rwa [map_mul, map_inv, mul_inv_eq_one] at hy

variable (K : Type*) [Field K] [NumberField K]

theorem principalUnits_isOpen (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    IsOpen (principalUnits K v n : Set (LocalIntegerRing K v)ˣ) := by
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  let f : (LocalIntegerRing K v)ˣ → ℝ := fun u => ‖(u.val : v.adicCompletion K) - 1‖
  have hf : Continuous f :=
    ((continuous_subtype_val.comp Units.continuous_val).sub continuous_const).norm
  have hpos : 0 < (residueCard K v : ℝ)⁻¹ ^ n :=
    pow_pos (inv_pos.mpr (by exact_mod_cast (Nat.zero_lt_one.trans (one_lt_residueCard K v)))) n
  have hneigh : {u | f u < (residueCard K v : ℝ)⁻¹ ^ n} ∈ 𝓝 1 :=
    (isOpen_lt hf continuous_const).mem_nhds (by simpa [f] using hpos)
  exact Filter.mem_of_superset hneigh fun u hu =>
    (mem_principalUnits_iff_norm K v n u).mpr hu.le

instance principalUnitsQuotient_discreteTopology (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    DiscreteTopology ((LocalIntegerRing K v)ˣ ⧸ principalUnits K v n) :=
  QuotientGroup.discreteTopology (principalUnits_isOpen K v n)

theorem localUnitReduction_isLocallyConstant (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    IsLocallyConstant (localUnitReduction K v n) :=
  monoidHom_locallyConstant_of_open_kernel _ (principalUnits_isOpen K v n)

/-- Every character of the finite residue unit group pulls back continuously. -/
def localResidueCharacterLift (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (ψ : (LocalResidueRing K v n)ˣ →* Circle) : UnitaryCharacter (LocalIntegerRing K v)ˣ where
  toMonoidHom := ψ.comp (localUnitReduction K v n)
  continuous_toFun := ((localUnitReduction_isLocallyConstant K v n).comp ψ).continuous

@[simp] theorem localResidueCharacterLift_apply (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (ψ : (LocalResidueRing K v n)ˣ →* Circle) (u : (LocalIntegerRing K v)ˣ) :
    localResidueCharacterLift K v n ψ u = ψ (localUnitReduction K v n u) := rfl

theorem localResidueCharacterLift_kernel (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (ψ : (LocalResidueRing K v n)ˣ →* Circle) :
    principalUnits K v n ≤ (localResidueCharacterLift K v n ψ).toMonoidHom.ker := by
  intro u hu
  change ψ (localUnitReduction K v n u) = 1
  rw [show localUnitReduction K v n u = 1 from hu, map_one]

theorem localResidueCharacterLift_injective (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Function.Injective (localResidueCharacterLift K v n) := by
  intro ψ θ h
  apply MonoidHom.ext
  intro y
  obtain ⟨u, rfl⟩ := localUnitReduction_surjective K v n y
  exact congrArg (fun f : UnitaryCharacter (LocalIntegerRing K v)ˣ => f u) h

def localUnitDepthCharacter (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :=
  {χ : UnitaryCharacter (LocalIntegerRing K v)ˣ // principalUnits K v n ≤ χ.toMonoidHom.ker}

/-- Continuous local unit characters of bounded depth are exactly finite residue characters. -/
def localUnitDepthCharacterEquiv (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    ((LocalResidueRing K v n)ˣ →* Circle) ≃ localUnitDepthCharacter K v n where
  toFun ψ := ⟨localResidueCharacterLift K v n ψ, localResidueCharacterLift_kernel K v n ψ⟩
  invFun χ := (localUnitReduction K v n).liftOfSurjective (localUnitReduction_surjective K v n)
    ⟨χ.val.toMonoidHom, χ.property⟩
  left_inv ψ := by
    apply MonoidHom.ext
    intro y
    obtain ⟨u, rfl⟩ := localUnitReduction_surjective K v n y
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  right_inv χ := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro u
    change ((localUnitReduction K v n).liftOfSurjective (localUnitReduction_surjective K v n)
      ⟨χ.val.toMonoidHom, χ.property⟩) (localUnitReduction K v n u) = χ.val u
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem localResidueCharacterLift_actual (v : HeightOneSpectrum (𝓞 K)) (χ : HeckeCharacter K)
    (n : ℕ) (hn : localConductorExponent K χ v ≤ n) :
    localResidueCharacterLift K v n (localResidueCharacter K v χ n hn) =
      localIntegralComponent K v χ := by
  apply ContinuousMonoidHom.ext
  exact localResidueCharacter_reduction K v χ n hn

theorem localIntegralComponent_isLocallyConstant (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) : IsLocallyConstant (localIntegralComponent K v χ) := by
  rw [← localResidueCharacterLift_actual K v χ _ le_rfl]
  exact (localUnitReduction_isLocallyConstant K v _).comp
    (localResidueCharacter K v χ _ le_rfl)

theorem localIntegralComponent_kernel_isOpen (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) : IsOpen ((localIntegralComponent K v χ).toMonoidHom.ker :
      Set (LocalIntegerRing K v)ˣ) :=
  Subgroup.isOpen_mono (conductor_principalUnits_le_ker K v χ)
    (principalUnits_isOpen K v _)

end HeckeGeneral.Characters
