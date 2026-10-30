import HeckeGeneral.Characters.LocalConductor

/-! Arithmetic of the actual local conductor exponents. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

theorem TrivialAtDepth.mono {χ : HeckeCharacter K} {v : HeightOneSpectrum (𝓞 K)}
    {n m : ℕ} (hχ : TrivialAtDepth K χ v n) (hnm : n ≤ m) : TrivialAtDepth K χ v m := by
  cases n with
  | zero =>
    cases m with
    | zero => exact hχ
    | succ m =>
      intro u hu
      exact hχ u (principalUnit_norm_one K v u (m + 1) (Nat.succ_pos m) hu)
  | succ n =>
    cases m with
    | zero => exact False.elim (Nat.not_succ_le_zero n hnm)
    | succ m =>
      intro u hu
      apply hχ u
      have hq : (1 : ℝ) < residueCard K v := by exact_mod_cast one_lt_residueCard K v
      exact hu.trans (pow_le_pow_of_le_one (inv_nonneg.mpr (le_trans zero_le_one hq.le))
        (inv_lt_one_of_one_lt₀ hq).le hnm)

theorem TrivialAtDepth.mul {χ ψ : HeckeCharacter K} {v : HeightOneSpectrum (𝓞 K)}
    {n : ℕ} (hχ : TrivialAtDepth K χ v n) (hψ : TrivialAtDepth K ψ v n) :
    TrivialAtDepth K (χ * ψ) v n := by
  cases n with
  | zero => exact UnramifiedAt.mul K hχ hψ
  | succ n =>
    intro u hu
    change localComponent K v χ u * localComponent K v ψ u = 1
    rw [hχ u hu, hψ u hu, one_mul]

theorem trivialAtDepth_one (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    TrivialAtDepth K (1 : HeckeCharacter K) v n := by
  cases n with
  | zero => exact unramifiedAt_one K v
  | succ n => intro u _; rfl

theorem TrivialAtDepth.inv {χ : HeckeCharacter K} {v : HeightOneSpectrum (𝓞 K)}
    {n : ℕ} (hχ : TrivialAtDepth K χ v n) : TrivialAtDepth K χ⁻¹ v n := by
  cases n with
  | zero => exact UnramifiedAt.inv K hχ
  | succ n =>
    intro u hu
    change (localComponent K v χ u)⁻¹ = 1
    rw [hχ u hu, inv_one]

theorem trivialAtDepth_inv_iff (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) : TrivialAtDepth K χ⁻¹ v n ↔ TrivialAtDepth K χ v n := by
  constructor
  · intro h
    simpa only [inv_inv] using h.inv
  · exact TrivialAtDepth.inv K

theorem TrivialAtDepth.pow {χ : HeckeCharacter K} {v : HeightOneSpectrum (𝓞 K)}
    {n : ℕ} (hχ : TrivialAtDepth K χ v n) (r : ℕ) : TrivialAtDepth K (χ ^ r) v n := by
  induction r with
  | zero => simpa using trivialAtDepth_one K v n
  | succ r hr => simpa only [pow_succ] using TrivialAtDepth.mul K hr hχ

theorem TrivialAtDepth.zpow {χ : HeckeCharacter K} {v : HeightOneSpectrum (𝓞 K)}
    {n : ℕ} (hχ : TrivialAtDepth K χ v n) (r : ℤ) : TrivialAtDepth K (χ ^ r) v n := by
  cases r with
  | ofNat r => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hχ.pow K r
  | negSucc r => simpa only [zpow_negSucc] using (hχ.pow K (r + 1)).inv

theorem localConductorExponent_le_iff (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    localConductorExponent K χ v ≤ n ↔ TrivialAtDepth K χ v n := by
  exact ⟨fun h => (trivialAtDepth_localConductorExponent K χ v).mono K h,
    localConductorExponent_le K χ v⟩

@[simp] theorem localConductorExponent_one (v : HeightOneSpectrum (𝓞 K)) :
    localConductorExponent K (1 : HeckeCharacter K) v = 0 :=
  (localConductorExponent_eq_zero_iff K _ v).mpr (unramifiedAt_one K v)

@[simp] theorem localConductorExponent_inv (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) :
    localConductorExponent K χ⁻¹ v = localConductorExponent K χ v := by
  apply le_antisymm
  · exact localConductorExponent_le K _ v (trivialAtDepth_localConductorExponent K χ v).inv
  · exact localConductorExponent_le K χ v
      ((trivialAtDepth_inv_iff K χ v _).mp (trivialAtDepth_localConductorExponent K χ⁻¹ v))

theorem localConductorExponent_mul_le_max (χ ψ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) :
    localConductorExponent K (χ * ψ) v ≤
      max (localConductorExponent K χ v) (localConductorExponent K ψ v) := by
  apply localConductorExponent_le
  exact ((trivialAtDepth_localConductorExponent K χ v).mono K (le_max_left _ _)).mul K
    ((trivialAtDepth_localConductorExponent K ψ v).mono K (le_max_right _ _))

theorem localConductorExponent_pow_le (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) (r : ℕ) :
    localConductorExponent K (χ ^ r) v ≤ localConductorExponent K χ v :=
  localConductorExponent_le K _ v ((trivialAtDepth_localConductorExponent K χ v).pow K r)

theorem localConductorExponent_zpow_le (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) (r : ℤ) :
    localConductorExponent K (χ ^ r) v ≤ localConductorExponent K χ v :=
  localConductorExponent_le K _ v ((trivialAtDepth_localConductorExponent K χ v).zpow K r)

theorem localConductorExponent_left_le (χ ψ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) :
    localConductorExponent K χ v ≤
      max (localConductorExponent K (χ * ψ) v) (localConductorExponent K ψ v) := by
  simpa only [mul_inv_cancel_right, localConductorExponent_inv] using
    localConductorExponent_mul_le_max K (χ * ψ) ψ⁻¹ v

theorem localConductorExponent_right_le (χ ψ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) :
    localConductorExponent K ψ v ≤
      max (localConductorExponent K (χ * ψ) v) (localConductorExponent K χ v) := by
  simpa only [mul_comm] using localConductorExponent_left_le K ψ χ v

/-- Conductors of unequal depth cannot cancel in a product. -/
theorem localConductorExponent_mul_eq_max_of_ne (χ ψ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K))
    (hne : localConductorExponent K χ v ≠ localConductorExponent K ψ v) :
    localConductorExponent K (χ * ψ) v =
      max (localConductorExponent K χ v) (localConductorExponent K ψ v) := by
  apply le_antisymm (localConductorExponent_mul_le_max K χ ψ v)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [max_eq_right hlt.le]
    have hb := localConductorExponent_right_le K χ ψ v
    by_contra h
    exact (not_le_of_gt (max_lt (lt_of_not_ge h) hlt)) hb
  · rw [max_eq_left hgt.le]
    have hb := localConductorExponent_left_le K χ ψ v
    by_contra h
    exact (not_le_of_gt (max_lt (lt_of_not_ge h) hgt)) hb

theorem conductorExponents_inv (χ : HeckeCharacter K) :
    conductorExponents K χ⁻¹ = conductorExponents K χ := by
  ext v
  exact localConductorExponent_inv K χ v

theorem finiteConductor_inv (χ : HeckeCharacter K) :
    finiteConductor K χ⁻¹ = finiteConductor K χ := by
  simp only [finiteConductor, conductorExponents_inv]

end HeckeGeneral.Characters
