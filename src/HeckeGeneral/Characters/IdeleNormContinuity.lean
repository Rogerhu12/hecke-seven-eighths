import HeckeGeneral.Characters.IdeleNorm
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# The continuous logarithmic norm on the actual idèle class group

The finite norm is constant equal to one on the open neighborhood where both an
idèle and its inverse are integral everywhere.  Its multiplicativity then gives
global continuity.  This argument uses the units topology, not a fictitious
normed-ring structure on the finite adèle ring.

The logarithmic norm is the negative logarithm of the conventional idelic modulus.
The prime-uniformizer formula and the analytic L-function shift identity remain
separate obligations.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Filter Topology

variable (K : Type*) [Field K] [NumberField K]

private abbrev FiniteAdelesForNorm := IsDedekindDomain.FiniteAdeleRing (𝓞 K) K

/-- The everywhere integral finite adèles form an open subset of the restricted product. -/
def integralFiniteAdeles : Set (FiniteAdelesForNorm K) :=
  {a | ∀ v : HeightOneSpectrum (𝓞 K), a v ∈ v.adicCompletionIntegers K}

theorem isOpen_integralFiniteAdeles : IsOpen (integralFiniteAdeles K) := by
  exact RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion K))

/-- Finite idèles whose value and inverse are both integral everywhere. -/
def integralFiniteIdeles : Set (FiniteAdelesForNorm K)ˣ :=
  Units.val ⁻¹' integralFiniteAdeles K ∩
    (fun u : (FiniteAdelesForNorm K)ˣ => (↑u⁻¹ : FiniteAdelesForNorm K)) ⁻¹'
      integralFiniteAdeles K

theorem isOpen_integralFiniteIdeles : IsOpen (integralFiniteIdeles K) :=
  ((isOpen_integralFiniteAdeles K).preimage Units.continuous_val).inter
    ((isOpen_integralFiniteAdeles K).preimage Units.continuous_coe_inv)

theorem one_mem_integralFiniteIdeles : (1 : (FiniteAdelesForNorm K)ˣ) ∈ integralFiniteIdeles K := by
  constructor <;> intro v <;> exact (v.adicCompletionIntegers K).one_mem

theorem finiteIdeleNorm_eq_one_of_integral (x : (FiniteAdelesForNorm K)ˣ)
    (hx : x ∈ integralFiniteIdeles K) : ‖x.val‖ = 1 := by
  change (∀ v, x.val v ∈ v.adicCompletionIntegers K) ∧
    (∀ v, (↑x⁻¹ : FiniteAdelesForNorm K) v ∈ v.adicCompletionIntegers K) at hx
  have hnorm (v : HeightOneSpectrum (𝓞 K)) : ‖x.val v‖ = 1 := by
    let xv : (v.adicCompletion K)ˣ :=
      RestrictedProduct.unitsEquiv (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) x v
    have hu : xv ∈ (v.adicCompletionIntegers K).units := ⟨hx.1 v, hx.2 v⟩
    have hv : (Valued.v (x.val v) : WithZero (Multiplicative ℤ)) = 1 :=
      (adicCompletionIntegers.mem_units_iff_valued_eq_one (K := K) (v := v) (a := xv)).mp hu
    exact (Valued.toNormedField.norm_eq_one_iff (L := v.adicCompletion K)
      (Γ₀ := WithZero (Multiplicative ℤ)) (x := x.val v)).mpr hv
  rw [NumberField.FiniteAdeleRing.norm_eq_finprod_of_unit]
  simp only [hnorm, finprod_one]

private def finiteIdeleNormHom : (FiniteAdelesForNorm K)ˣ →* ℝ where
  toFun x := ‖x.val‖
  map_one' := finiteIdeleNorm_eq_one_of_integral K 1 (one_mem_integralFiniteIdeles K)
  map_mul' := finiteIdeleNorm_mul K

theorem continuous_finiteIdeleNorm : Continuous (fun x : (FiniteAdelesForNorm K)ˣ => ‖x.val‖) := by
  apply continuous_of_continuousAt_one (finiteIdeleNormHom K)
  have heq : (fun _ : (FiniteAdelesForNorm K)ˣ => (1 : ℝ)) =ᶠ[𝓝 1]
      (fun x => ‖x.val‖) := by
    filter_upwards [(isOpen_integralFiniteIdeles K).mem_nhds (one_mem_integralFiniteIdeles K)]
      with x hx
    exact (finiteIdeleNorm_eq_one_of_integral K x hx).symm
  exact continuousAt_const.congr heq

theorem continuous_infiniteAdeleNorm : Continuous (fun x : InfiniteAdeleRing K => ‖x‖) := by
  change Continuous (fun x : InfiniteAdeleRing K => ∏ v, ‖x v‖ ^ v.mult)
  simpa using continuous_finsetProd Finset.univ
    (fun v _ => (continuous_norm.comp
      (show Continuous (fun x : InfiniteAdeleRing K => x v) from continuous_apply v)).pow v.mult)

theorem continuous_finiteIdelePart : Continuous (finiteIdelePart K) :=
  Units.continuous_map (show Continuous
    (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdelesForNorm K)) from continuous_snd)

theorem continuous_idelicNorm : Continuous (idelicNorm K) := by
  have hval : Continuous (fun x : IdeleGroup (𝓞 K) K => x.val) := Units.continuous_val
  have hinf : Continuous (fun x : IdeleGroup (𝓞 K) K => ‖x.val.1‖) :=
    (continuous_infiniteAdeleNorm K).comp hval.fst
  have hfin : Continuous (fun x : IdeleGroup (𝓞 K) K => ‖(finiteIdelePart K x).val‖) :=
    (continuous_finiteIdeleNorm K).comp (continuous_finiteIdelePart K)
  have hfin' : Continuous (fun x : IdeleGroup (𝓞 K) K => ‖x.val.2‖) := by
    simpa only [finiteIdelePart_val] using hfin
  exact hinf.mul hfin'

theorem continuous_ideleLogNormHom : Continuous (ideleLogNormHom K) := by
  exact ((continuous_idelicNorm K).log (fun x => (idelicNorm_pos K x).ne')).neg

theorem continuous_ideleClassLogNormHom : Continuous (ideleClassLogNormHom K) := by
  apply (QuotientGroup.isQuotientMap_mk
    (IdeleGroup.principalSubgroup (𝓞 K) K)).continuous_iff.mpr
  exact continuous_ideleLogNormHom K

/-- The actual continuous logarithmic norm on idèles. -/
def ideleLogNorm : LogNorm (IdeleGroup (𝓞 K) K) where
  toMonoidHom := ideleLogNormHom K
  continuous_toFun := continuous_ideleLogNormHom K

/-- The actual continuous logarithmic norm on the idèle class group. -/
def heckeLogNorm : LogNorm (IdeleClassGroup (𝓞 K) K) where
  toMonoidHom := ideleClassLogNormHom K
  continuous_toFun := continuous_ideleClassLogNormHom K

theorem heckeLogNorm_comp_ideleClassMap : (heckeLogNorm K).comp (ideleClassMap K) = ideleLogNorm K := by
  apply ContinuousMonoidHom.ext
  intro x
  rfl

/-- The continuous unitary norm character on the actual idèle class group. -/
def heckeNormTwist (t : ℝ) : HeckeCharacter K := normTwist (heckeLogNorm K) t

@[simp] theorem heckeNormTwist_apply (t : ℝ) (x : IdeleGroup (𝓞 K) K) :
    heckeNormTwist K t (ideleClassMap K x) = Circle.exp (t * (-Real.log (idelicNorm K x))) := rfl

/-- The packet is now instantiated using the actual continuous number-field norm. -/
def HeckePacket (ω : HeckeCharacter K) : Set (HeckeCharacter K) := Packet (heckeLogNorm K) ω

theorem base_mem_heckePacket (ω : HeckeCharacter K) : ω ∈ HeckePacket K ω :=
  base_mem_packet (heckeLogNorm K) ω

theorem finiteOrder_mem_heckePacket (ω θ : HeckeCharacter K) (hθ : FiniteOrder θ) :
    θ ∈ HeckePacket K ω := finiteOrder_mem_packet (heckeLogNorm K) ω θ hθ

theorem heckePacket_mul_normTwist (ω : HeckeCharacter K) {χ : HeckeCharacter K}
    (hχ : χ ∈ HeckePacket K ω) (t : ℝ) : χ * heckeNormTwist K t ∈ HeckePacket K ω :=
  packet_mul_normTwist (heckeLogNorm K) ω hχ t

theorem heckePacket_inv (ω : HeckeCharacter K) {χ : HeckeCharacter K}
    (hχ : χ ∈ HeckePacket K ω) : χ⁻¹ ∈ HeckePacket K ω :=
  packet_inv (heckeLogNorm K) ω hχ

end HeckeGeneral.Characters
