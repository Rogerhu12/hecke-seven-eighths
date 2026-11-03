import HeckeGeneral.Analysis.GlobalThetaData
import DedekindZetaZeroFree.Arithmetic.LocalFields.SexticHilbertPairing

/-!
# The S-local sixth-power class group is finite (TH-SIXTH-LOCAL-FINITE)

For a totally complex `K`, every unit of the mixed space is a sixth power, and at each
finite place the sixth-power class group of the completion is finite
(`ClassFieldTheory.powerClassGroup_finite`, as in Axiom's `V_finite`). So the
sixth powers have finite index in `sLocalMultiplicativeGroup K S`.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.SixthLocalFinite

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem six_ne_zero_completion (v : HeightOneSpectrum (𝓞 K)) :
    ((6 : ℕ) : v.adicCompletion K) ≠ 0 := by
  intro h
  have h' : ((6 : ℕ) : K) = 0 :=
    RingHom.injective (algebraMap K (v.adicCompletion K)) (by rw [map_natCast, h, map_zero])
  norm_num at h'

/-- Sixth powers have finite index at each finite place. -/
theorem finiteIndex_local (v : HeightOneSpectrum (𝓞 K)) :
    ((powMonoidHom 6 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range).FiniteIndex := by
  letI : ValuativeRel (v.adicCompletion K) :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel K v
  letI : IsNonarchimedeanLocalField (v.adicCompletion K) :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField K v
  have hfin : Finite (ClassFieldTheory.PowerClassGroup (v.adicCompletion K) 6) :=
    ClassFieldTheory.powerClassGroup_finite _ 6 (six_ne_zero_completion K v)
  have : Finite ((v.adicCompletion K)ˣ ⧸
      (powMonoidHom 6 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) := hfin
  exact Subgroup.finiteIndex_of_finite_quotient

omit [NumberField K] in
/-- Every unit of the mixed space of a totally complex field is a sixth power. -/
theorem mixed_unit_sixth_power [IsTotallyComplex K]
    (u : (mixedEmbedding.mixedSpace K)ˣ) : ∃ x, x ^ 6 = u := by
  classical
  have : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex w.val)) w.property⟩
  have hu2 : ∀ w, u.val.2 w ≠ 0 := by
    intro w h
    have h2 : (u.val * u.inv).2 w = 1 := by rw [u.val_inv]; rfl
    rw [Prod.snd_mul, Pi.mul_apply, h, zero_mul] at h2
    exact zero_ne_one h2
  let r : {w : InfinitePlace K // w.IsComplex} → ℂ := fun w =>
    Classical.choose (IsAlgClosed.exists_pow_nat_eq (u.val.2 w) (by norm_num : 0 < 6))
  have hr : ∀ w, r w ^ 6 = u.val.2 w := fun w =>
    Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (u.val.2 w) (by norm_num : 0 < 6))
  have hr0 : ∀ w, r w ≠ 0 := fun w h => hu2 w (by rw [← hr w, h]; norm_num)
  let y : mixedEmbedding.mixedSpace K := (u.val.1, r)
  let yi : mixedEmbedding.mixedSpace K := (u.inv.1, fun w => (r w)⁻¹)
  have h1 : y * yi = 1 := by
    refine Prod.ext (funext fun w => isEmptyElim w) (funext fun w => ?_)
    simp [y, yi, hr0 w]
  have h2 : yi * y = 1 := by
    refine Prod.ext (funext fun w => isEmptyElim w) (funext fun w => ?_)
    simp [y, yi, hr0 w]
  refine ⟨⟨y, yi, h1, h2⟩, Units.ext ?_⟩
  refine Prod.ext (funext fun w => isEmptyElim w) (funext fun w => ?_)
  simp only [Units.val_pow_eq_pow_val, Prod.pow_snd, Pi.pow_apply]
  exact hr w

/-- The sixth-power class group of the completion at `v`. -/
abbrev localQ (v : S) : Type :=
  (v.val.adicCompletion K)ˣ ⧸
    (powMonoidHom 6 : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range

instance localQ_finite (v : S) : Finite (localQ K S v) := by
  have := finiteIndex_local K v.val
  exact Subgroup.finite_quotient_of_finiteIndex

theorem sixthLocalClasses_finite [IsTotallyComplex K] : Finite (SixthLocalClasses K S) := by
  let H := (powMonoidHom 6 : sLocalMultiplicativeGroup K S →*
    sLocalMultiplicativeGroup K S).range
  let f : SixthLocalClasses K S → ((v : S) → localQ K S v) := fun c =>
    Quotient.liftOn' c (fun x v => (QuotientGroup.mk (x.2 v) : localQ K S v)) (by
      intro a b hab
      obtain ⟨y, hy⟩ := (QuotientGroup.leftRel_apply.mp hab : a⁻¹ * b ∈ H)
      funext v
      apply QuotientGroup.eq.mpr
      refine ⟨y.2 v, ?_⟩
      have := congrArg (fun z : sLocalMultiplicativeGroup K S => z.2 v) hy
      simpa using this)
  have hinj : Function.Injective f := by
    intro c d hcd
    induction c using QuotientGroup.induction_on with | H a => ?_
    induction d using QuotientGroup.induction_on with | H b => ?_
    apply QuotientGroup.eq.mpr
    have hv : ∀ v : S, ∃ q, q ^ 6 = (a.2 v)⁻¹ * b.2 v := by
      intro v
      have h1 := congrFun hcd v
      obtain ⟨q, hq⟩ := QuotientGroup.eq.mp h1
      exact ⟨q, hq⟩
    choose q hq using hv
    obtain ⟨x, hx⟩ := mixed_unit_sixth_power K (a.1⁻¹ * b.1)
    exact ⟨(x, q), Prod.ext hx (funext hq)⟩
  exact Finite.of_injective f hinj

end HeckeSkeleton.SixthLocalFinite
