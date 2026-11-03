import FiniteSUnitPowerDetectors
import HeckeGeneral.Arithmetic.SIntegerExteriorValuationRealization
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
UNCOMPILED independent allowed-generator construction candidate, 2026-10-11.
No Lean, Lake, compiler, or existing native queue was run or changed.

The sole arithmetic inputs are the actual finite Kummer detectors and the
project's proved principalization/exterior-valuation realization theorems.
All valuation realization uses the INITIAL principal support S0. Two detector
pairs are chosen independently from S0. A final principalization may enlarge
their union again: cancellation works for EVERY finite larger U, so there is
no assumed preservation-of-PID or preservation-of-injectivity theorem.

The last theorem constructs an actual injective homomorphism from S-units
modulo sixth powers to the PRODUCT of the actual same-S completion quotients.
No Hilbert pairing, isotropic complement, or allowed-generator section is
claimed here. Put this independent directory on the module search path when
the parent elects to compile it; it is not part of the frozen theta plan.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Arithmetic.AllowedGeneratorConstruction

open NumberField IsDedekindDomain KummerTheory
open IsDedekindDomain.HeightOneSpectrum
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

/-- The actual field-unit localization map. -/
def finiteUnitLocalization (q : HeightOneSpectrum (𝓞 K)) :
    Kˣ →* (q.adicCompletion K)ˣ :=
  Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom

/-- A detector for S-units yields detection on every finite U containing
both S and its detector T, using only the INITIAL principal support S0. -/
theorem sUnit_power_detected_on_enlargement
    (S0 S T U : Finset (HeightOneSpectrum (𝓞 K)))
    [IsPrincipalIdealRing ((S0 : Set (HeightOneSpectrum (𝓞 K))).integer K)]
    (hS0S : S0 ⊆ S) (hSU : S ⊆ U) (hTU : T ⊆ U) (n : ℕ+)
    (hdet : ∀ a : (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
      (∀ q ∈ T, ∃ z : (q.adicCompletion K)ˣ,
        z ^ (n : ℕ) = finiteUnitLocalization K q (a : Kˣ)) ↔
      ∃ b : (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
        b ^ (n : ℕ) = a)
    (x : (U : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (hx : ∀ q ∈ U, ∃ z : (q.adicCompletion K)ˣ,
      z ^ (n : ℕ) = finiteUnitLocalization K q (x : Kˣ)) :
    ∃ y : (U : Set (HeightOneSpectrum (𝓞 K))).unit K,
      y ^ (n : ℕ) = x := by
  classical
  -- Only finitely many new valuation coordinates need cancellation.
  choose z hz using fun q : {q : HeightOneSpectrum (𝓞 K) // q ∈ U \ S} =>
    hx q.val (Finset.mem_sdiff.mp q.property).1
  let e : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
    Finsupp.onFinset (U \ S)
      (fun q => if hq : q ∈ U \ S then
        -WithZero.log
          (Valued.v ((z ⟨q, hq⟩) : q.adicCompletion K) :
            WithZero (Multiplicative ℤ)) else 0)
      (by
        intro q hq
        by_contra hnot
        exact hq (dif_neg hnot))
  obtain ⟨y0, hy0⟩ := exists_exterior_valuation_realization K
    (S0 : Set (HeightOneSpectrum (𝓞 K))) e
  have hyU : y0 ∈ (U : Set (HeightOneSpectrum (𝓞 K))).unit K := by
    intro q hqU
    have hq0 : q ∉ (S0 : Set (HeightOneSpectrum (𝓞 K))) :=
      fun hq => hqU (hSU (hS0S hq))
    have hqnew : q ∉ U \ S :=
      fun hq => hqU (Finset.mem_sdiff.mp hq).1
    rw [hy0 q hq0]
    simp only [e, Finsupp.onFinset_apply, dif_neg hqnew, neg_zero,
      WithZero.exp_zero]
  -- At a new prime, y0 has exactly the valuation of the chosen local root.
  have hynew (q : HeightOneSpectrum (𝓞 K)) (hq : q ∈ U \ S) :
      q.valuation K (y0 : K) =
        (Valued.v ((z ⟨q, hq⟩) : q.adicCompletion K) :
          WithZero (Multiplicative ℤ)) := by
    have hq0 : q ∉ (S0 : Set (HeightOneSpectrum (𝓞 K))) :=
      fun h => (Finset.mem_sdiff.mp hq).2 (hS0S h)
    rw [hy0 q hq0]
    simp only [e, Finsupp.onFinset_apply, dif_pos hq, neg_neg]
    exact WithZero.exp_log
      ((Valued.v : Valuation (q.adicCompletion K)
        (WithZero (Multiplicative ℤ))).map_eq_zero_iff.ne.mpr
          (Units.ne_zero (z ⟨q, hq⟩)))
  have hxnew (q : HeightOneSpectrum (𝓞 K)) (hq : q ∈ U \ S) :
      q.valuation K ((x : Kˣ) : K) =
        (Valued.v ((z ⟨q, hq⟩) : q.adicCompletion K) :
          WithZero (Multiplicative ℤ)) ^ (n : ℕ) := by
    have hval := congrArg
      (fun u : (q.adicCompletion K)ˣ =>
        (Valued.v (u : q.adicCompletion K) : WithZero (Multiplicative ℤ)))
      (hz ⟨q, hq⟩)
    change Valued.v (((z ⟨q, hq⟩) : q.adicCompletion K) ^ (n : ℕ)) =
      Valued.v (((x : Kˣ) : K) : q.adicCompletion K) at hval
    rw [map_pow, adicCompletion.valued_coe] at hval
    exact hval.symm
  have hx0S : (x : Kˣ) / y0 ^ (n : ℕ) ∈
      (S : Set (HeightOneSpectrum (𝓞 K))).unit K := by
    intro q hqS
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    rw [map_div₀, map_pow]
    by_cases hqU : q ∈ U
    · have hq : q ∈ U \ S := Finset.mem_sdiff.mpr ⟨hqU, hqS⟩
      rw [hxnew q hq, hynew q hq]
      exact div_self (pow_ne_zero _
        ((Valued.v : Valuation (q.adicCompletion K)
          (WithZero (Multiplicative ℤ))).map_eq_zero_iff.ne.mpr
            (Units.ne_zero (z ⟨q, hq⟩))))
    · rw [x.property q hqU, hyU q hqU, one_pow, one_div, inv_one]
  let x0 : (S : Set (HeightOneSpectrum (𝓞 K))).unit K :=
    ⟨(x : Kˣ) / y0 ^ (n : ℕ), hx0S⟩
  have hx0local : ∀ q ∈ T, ∃ w : (q.adicCompletion K)ˣ,
      w ^ (n : ℕ) = finiteUnitLocalization K q (x0 : Kˣ) := by
    intro q hq
    obtain ⟨w, hw⟩ := hx q (hTU hq)
    refine ⟨w / finiteUnitLocalization K q y0, ?_⟩
    calc
      (w / finiteUnitLocalization K q y0) ^ (n : ℕ) =
          w ^ (n : ℕ) / (finiteUnitLocalization K q y0) ^ (n : ℕ) :=
        div_pow _ _ _
      _ = finiteUnitLocalization K q (x : Kˣ) /
          finiteUnitLocalization K q (y0 ^ (n : ℕ)) := by rw [hw, map_pow]
      _ = finiteUnitLocalization K q ((x : Kˣ) / y0 ^ (n : ℕ)) :=
        (map_div (finiteUnitLocalization K q) _ _).symm
      _ = finiteUnitLocalization K q (x0 : Kˣ) := rfl
  obtain ⟨b, hb⟩ := (hdet x0).mp hx0local
  have hbU : (b : Kˣ) ∈ (U : Set (HeightOneSpectrum (𝓞 K))).unit K := by
    intro q hqU
    exact b.property q (fun hqS => hqU (hSU hqS))
  refine ⟨⟨y0 * (b : Kˣ), Subgroup.mul_mem _ hyU hbU⟩, ?_⟩
  apply Subtype.ext
  have hbval : (b : Kˣ) ^ (n : ℕ) = (x : Kˣ) / y0 ^ (n : ℕ) :=
    congrArg (fun a : (S : Set (HeightOneSpectrum (𝓞 K))).unit K => (a : Kˣ)) hb
  change (y0 * (b : Kˣ)) ^ (n : ℕ) = (x : Kˣ)
  rw [mul_pow, hbval]
  exact mul_div_cancel _ _

/-- Two actual detectors, chosen independently over one initial PID support,
give square AND cube detection at the SAME final finite PID support. -/
theorem exists_finite_square_cube_sUnit_detection
    (Sinitial : Finset (HeightOneSpectrum (𝓞 K)))
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 6) :
    ∃ U : Finset (HeightOneSpectrum (𝓞 K)),
      Sinitial ⊆ U ∧
      IsPrincipalIdealRing ((U : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
      (∀ x : (U : Set (HeightOneSpectrum (𝓞 K))).unit K,
        (∀ q ∈ U, ∃ z : (q.adicCompletion K)ˣ,
          z ^ 2 = finiteUnitLocalization K q (x : Kˣ)) →
        ∃ y : (U : Set (HeightOneSpectrum (𝓞 K))).unit K, y ^ 2 = x) ∧
      (∀ x : (U : Set (HeightOneSpectrum (𝓞 K))).unit K,
        (∀ q ∈ U, ∃ z : (q.adicCompletion K)ˣ,
          z ^ 3 = finiteUnitLocalization K q (x : Kˣ)) →
        ∃ y : (U : Set (HeightOneSpectrum (𝓞 K))).unit K, y ^ 3 = x) := by
  classical
  obtain ⟨S0set, hS0finite, hinitial, hS0pid⟩ :=
    exists_finite_sInteger_isPrincipalIdealRing K
      (Sinitial : Set (HeightOneSpectrum (𝓞 K))) Sinitial.finite_toSet
  let S0 : Finset (HeightOneSpectrum (𝓞 K)) := hS0finite.toFinset
  have hS0coe : (S0 : Set (HeightOneSpectrum (𝓞 K))) = S0set :=
    hS0finite.coe_toFinset
  letI : IsPrincipalIdealRing
      ((S0 : Set (HeightOneSpectrum (𝓞 K))).integer K) := by
    rw [hS0coe]
    exact hS0pid
  obtain ⟨S2, T2, h02, _hdisj2, hdet2⟩ :=
    exists_finite_quadratic_sUnit_detector K S0 zeta hzeta
  obtain ⟨S3, T3, h03, _hdisj3, hdet3⟩ :=
    exists_finite_cubic_sUnit_detector K S0 zeta hzeta
  let B := (S2 ∪ T2) ∪ (S3 ∪ T3)
  -- This second principalization is actual existence, not a PID-preservation
  -- assumption. Cancellation below still uses the FIRST PID instance only.
  obtain ⟨Uset, hUfinite, hBUset, hUpid⟩ :=
    exists_finite_sInteger_isPrincipalIdealRing K
      (B : Set (HeightOneSpectrum (𝓞 K))) B.finite_toSet
  let U : Finset (HeightOneSpectrum (𝓞 K)) := hUfinite.toFinset
  have hUcoe : (U : Set (HeightOneSpectrum (𝓞 K))) = Uset :=
    hUfinite.coe_toFinset
  have hBU : B ⊆ U := by
    intro q hq
    change q ∈ (U : Set (HeightOneSpectrum (𝓞 K)))
    rw [hUcoe]
    exact hBUset hq
  have h2U : S2 ⊆ U := by
    intro q hq
    apply hBU
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hq)))
  have hT2U : T2 ⊆ U := by
    intro q hq
    apply hBU
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hq)))
  have h3U : S3 ⊆ U := by
    intro q hq
    apply hBU
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl hq)))
  have hT3U : T3 ⊆ U := by
    intro q hq
    apply hBU
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr hq)))
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro q hq
    apply h2U
    apply h02
    change q ∈ (S0 : Set (HeightOneSpectrum (𝓞 K)))
    rw [hS0coe]
    exact hinitial hq
  · rw [hUcoe]
    exact hUpid
  · intro x hx
    exact sUnit_power_detected_on_enlargement K S0 S2 T2 U
      h02 h2U hT2U (2 : ℕ+) hdet2 x hx
  · intro x hx
    exact sUnit_power_detected_on_enlargement K S0 S3 T3 U
      h03 h3U hT3U (3 : ℕ+) hdet3 x hx

/-- An actual finite enlargement with SAME-S local sixth-power detection. -/
theorem exists_finite_sextic_sUnit_detection
    (Sinitial : Finset (HeightOneSpectrum (𝓞 K)))
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 6) :
    ∃ U : Finset (HeightOneSpectrum (𝓞 K)),
      Sinitial ⊆ U ∧
      IsPrincipalIdealRing ((U : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
      ∀ x : (U : Set (HeightOneSpectrum (𝓞 K))).unit K,
        (∀ q ∈ U, ∃ z : (q.adicCompletion K)ˣ,
          z ^ 6 = finiteUnitLocalization K q (x : Kˣ)) ↔
        ∃ y : (U : Set (HeightOneSpectrum (𝓞 K))).unit K, y ^ 6 = x := by
  obtain ⟨U, hiU, hpid, htwo, hthree⟩ :=
    exists_finite_square_cube_sUnit_detection K Sinitial zeta hzeta
  refine ⟨U, hiU, hpid, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    obtain ⟨a, ha⟩ := htwo x (by
      intro q hq
      obtain ⟨z, hz⟩ := hx q hq
      exact ⟨z ^ 3, by simpa only [← pow_mul] using hz⟩)
    obtain ⟨b, hb⟩ := hthree x (by
      intro q hq
      obtain ⟨z, hz⟩ := hx q hq
      exact ⟨z ^ 2, by simpa only [← pow_mul] using hz⟩)
    refine ⟨a / b, ?_⟩
    calc
      (a / b) ^ 6 = (a ^ 2) ^ 3 / (b ^ 3) ^ 2 := by
        rw [div_pow, ← pow_mul, ← pow_mul]
      _ = x ^ 3 / x ^ 2 := by rw [ha, hb]
      _ = x ^ 2 * x / x ^ 2 := by rw [pow_succ x 2]
      _ = x := mul_div_cancel_left _ _
  · rintro ⟨y, hy⟩ q hq
    refine ⟨finiteUnitLocalization K q (y : Kˣ), ?_⟩
    rw [← map_pow]
    exact congrArg (finiteUnitLocalization K q)
      (congrArg (fun a : (U : Set (HeightOneSpectrum (𝓞 K))).unit K => (a : Kˣ)) hy)

/-- The target is the product of the genuine local field-unit power quotients. -/
abbrev sameSLocalPowerQuotients
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :=
  (q : S) → (q.val.adicCompletion K)ˣ ⧸
    (powMonoidHom n : (q.val.adicCompletion K)ˣ →*
      (q.val.adicCompletion K)ˣ).range

def sUnitLocalPowerClassHom
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    (S : Set (HeightOneSpectrum (𝓞 K))).unit K →*
      sameSLocalPowerQuotients K S n where
  toFun x q := QuotientGroup.mk' _ (finiteUnitLocalization K q.val (x : Kˣ))
  map_one' := by ext q; simp
  map_mul' x y := by ext q; simp

private theorem sUnitPowers_le_localPowerClassHom_ker
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    (powMonoidHom n : (S : Set (HeightOneSpectrum (𝓞 K))).unit K →*
      (S : Set (HeightOneSpectrum (𝓞 K))).unit K).range ≤
        (sUnitLocalPowerClassHom K S n).ker := by
  rintro x ⟨y, rfl⟩
  change sUnitLocalPowerClassHom K S n (y ^ n) = 1
  funext q
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨finiteUnitLocalization K q.val (y : Kˣ), ?_⟩
  exact (map_pow (finiteUnitLocalization K q.val) (y : Kˣ) n).symm

/-- Canonical localization homomorphism on actual S-unit power classes. -/
def sUnitPowerLocalization
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⧸
      (powMonoidHom n : (S : Set (HeightOneSpectrum (𝓞 K))).unit K →*
        (S : Set (HeightOneSpectrum (𝓞 K))).unit K).range) →*
      sameSLocalPowerQuotients K S n :=
  QuotientGroup.lift
    (G := (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (M := sameSLocalPowerQuotients K S n)
    (powMonoidHom n : (S : Set (HeightOneSpectrum (𝓞 K))).unit K →*
      (S : Set (HeightOneSpectrum (𝓞 K))).unit K).range
    (sUnitLocalPowerClassHom K S n)
    (sUnitPowers_le_localPowerClassHom_ker K S n)

/-- A concrete consumer converting the proved detection implication to
injectivity. Its hypothesis is discharged existentially below. -/
theorem sUnitPowerLocalization_injective_of_detection
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (hdet : ∀ x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
      (∀ q ∈ S, ∃ z : (q.adicCompletion K)ˣ,
        z ^ n = finiteUnitLocalization K q (x : Kˣ)) →
      ∃ y : (S : Set (HeightOneSpectrum (𝓞 K))).unit K, y ^ n = x) :
    Function.Injective (sUnitPowerLocalization K S n) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  apply le_antisymm (sUnitPowers_le_localPowerClassHom_ker K S n)
  intro x hx
  change sUnitLocalPowerClassHom K S n x = 1 at hx
  obtain ⟨y, hy⟩ := hdet x (by
    intro q hq
    have hqclass := congrFun hx (⟨q, hq⟩ : S)
    change (finiteUnitLocalization K q (x : Kˣ) :
      (q.adicCompletion K)ˣ ⧸ (powMonoidHom n :
        (q.adicCompletion K)ˣ →* (q.adicCompletion K)ˣ).range) = 1 at hqclass
    obtain ⟨z, hz⟩ := (QuotientGroup.eq_one_iff _).mp hqclass
    exact ⟨z, hz⟩)
  exact ⟨y, hy⟩

/-- The finite SAME-S sextic embedding, with an actual finite PID support,
is constructed from primitive roots and proved upstream arithmetic only. -/
theorem exists_finite_sextic_sUnitPowerLocalization_injective
    (Sinitial : Finset (HeightOneSpectrum (𝓞 K)))
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 6) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      Sinitial ⊆ S ∧
      IsPrincipalIdealRing ((S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
      Function.Injective (sUnitPowerLocalization K S 6) := by
  obtain ⟨S, hiS, hpid, hdet⟩ :=
    exists_finite_sextic_sUnit_detection K Sinitial zeta hzeta
  exact ⟨S, hiS, hpid, sUnitPowerLocalization_injective_of_detection K S 6
    (fun x hx => (hdet x).mp hx)⟩

end HeckeGeneral.Arithmetic.AllowedGeneratorConstruction
