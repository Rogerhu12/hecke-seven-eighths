import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalClippedProfileBounds

/-!
# Paying every original Mellin scale power before the moving parameters

The target seminorms, annulus, slot cap, direction bound and number of
Mellin factors are fixed first.  One positive tilt is then chosen from
the final profile-degree budget.  Its finitely many possible multiples
determine one finite sum of the already proved analytic constants.

The actual profile amplitudes are bounded from the original atom scales
and directions.  The powers of `Z` remain explicit.  Raising the common
amplitude to the full pre-removal degree pays precisely the chosen
`Z^ε` budget; no aggregate amplitude estimate is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

namespace CanonicalLogProfiles

/-- A fixed number of original Mellin factors permits only these real
powers.  The set is fixed before the scales or Fourier parameters. -/
def exponentPalette (δ : ℝ) (R : ℕ) : Finset ℝ :=
  (Finset.range (R + 1)).image (fun j : ℕ => (j : ℝ) * δ)

theorem exponentPalette_nonneg {δ e : ℝ} (hδ : 0 ≤ δ) {R : ℕ}
    (he : e ∈ exponentPalette δ R) : 0 ≤ e := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
  exact mul_nonneg (Nat.cast_nonneg _) hδ

theorem exponentPalette_le {δ e : ℝ} (hδ : 0 ≤ δ) {R : ℕ}
    (he : e ∈ exponentPalette δ R) : e ≤ (R : ℝ) * δ := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
  have hjR : j ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjR) hδ

def paletteShapeCoefficient (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (s : Finset (ℕ × ℕ)) (δ : ℝ) (R : ℕ) : ℝ :=
  ∑ e ∈ exponentPalette δ R, shapeCoefficient window hcompact hpositive e s

theorem paletteShapeCoefficient_nonneg (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (s : Finset (ℕ × ℕ)) (δ : ℝ) (R : ℕ) :
    0 ≤ paletteShapeCoefficient window hcompact hpositive s δ R :=
  Finset.sum_nonneg (fun e _ => shapeCoefficient_nonneg window hcompact hpositive e s)

theorem shapeCoefficient_le_palette (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (s : Finset (ℕ × ℕ)) (δ : ℝ) (R : ℕ)
    {e : ℝ} (he : e ∈ exponentPalette δ R) :
    shapeCoefficient window hcompact hpositive e s ≤
      paletteShapeCoefficient window hcompact hpositive s δ R :=
  Finset.single_le_sum (fun e _ => shapeCoefficient_nonneg window hcompact hpositive e s) he

/-- This coefficient contains no moving scale or original profile. -/
def profileAtomConstant (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (s : Finset (ℕ × ℕ)) (δ : ℝ) (R : ℕ) (D : ℝ) : ℝ :=
  paletteShapeCoefficient window hcompact hpositive s δ R *
    (1 + 2 * Real.pi * D) ^ (s.sup Prod.snd)

theorem profileAtomConstant_nonneg (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (s : Finset (ℕ × ℕ)) (δ : ℝ) (R : ℕ)
    (D : ℝ) (hD : 0 ≤ D) :
    0 ≤ profileAtomConstant window hcompact hpositive s δ R D :=
  mul_nonneg (paletteShapeCoefficient_nonneg window hcompact hpositive s δ R)
    (pow_nonneg (by positivity) _)

def commonAmplitudeConstant (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (s : Finset (ℕ × ℕ))
    (δ : ℝ) (R cap : ℕ) (D : ℝ) : ℝ :=
  1 + ((cap : ℝ) + 2) * profileAtomConstant window hcompact hpositive s δ R D

theorem commonAmplitudeConstant_one_le (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (s : Finset (ℕ × ℕ))
    (δ : ℝ) (R cap : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    1 ≤ commonAmplitudeConstant window hcompact hpositive s δ R cap D := by
  have hC := profileAtomConstant_nonneg window hcompact hpositive s δ R D hD
  unfold commonAmplitudeConstant
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) hC)

section Atoms

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem Atom.profileCoefficient_le_palette_scale (p : Atom V)
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (s : Finset (ℕ × ℕ)) (δ : ℝ) (hδ : 0 ≤ δ) (R : ℕ)
    (D L Z : ℝ) (hD : 0 ≤ D) (hL : 0 ≤ L) (hZ : 1 ≤ Z)
    (he : p.exponent ∈ exponentPalette δ R) (hd : ‖p.direction‖ ≤ D)
    (hscale : p.scale ≤ Z ^ L) :
    p.profileCoefficient window hcompact hpositive s ≤
      profileAtomConstant window hcompact hpositive s δ R D * Z ^ (L * R * δ) := by
  have he0 := exponentPalette_nonneg hδ he
  have hebound := exponentPalette_le hδ he
  have hbudget : L * p.exponent ≤ L * R * δ := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hebound hL
  have hraw := p.profileCoefficient_le_scaleBudget window hcompact hpositive s
    Z L (L * R * δ) hZ he0 hscale hbudget
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have hdirection : (1 + 2 * Real.pi * ‖p.direction‖) ^ (s.sup Prod.snd) ≤
      (1 + 2 * Real.pi * D) ^ (s.sup Prod.snd) := by
    have hbase : 1 + 2 * Real.pi * ‖p.direction‖ ≤ 1 + 2 * Real.pi * D := by
      linarith [mul_le_mul_of_nonneg_left hd hπ]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hcoefficient : shapeCoefficient window hcompact hpositive p.exponent s *
      (1 + 2 * Real.pi * ‖p.direction‖) ^ (s.sup Prod.snd) ≤
        profileAtomConstant window hcompact hpositive s δ R D :=
    mul_le_mul (shapeCoefficient_le_palette window hcompact hpositive s δ R he)
      hdirection (pow_nonneg (by positivity) _)
      (paletteShapeCoefficient_nonneg window hcompact hpositive s δ R)
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoefficient
    (Real.rpow_nonneg (zero_le_one.trans hZ) _))

/-- Whole conjugation reverses the location direction and its offset.
The actual profile coefficient is unchanged, including its real scale
power; no factor is dropped before the conjugation. -/
theorem Atom.profileCoefficient_neg_location (p : Atom V)
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (s : Finset (ℕ × ℕ)) :
    ({ p with offset := -p.offset, direction := -p.direction } : Atom V).profileCoefficient
        window hcompact hpositive s = p.profileCoefficient window hcompact hpositive s := by
  simp only [Atom.profileCoefficient, norm_neg]

end Atoms

section Amplitudes

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Every term of the actual common amplitude is bounded from its
original scale and direction.  The finite atom count remains explicit. -/
theorem profileAmplitude_le_original_scale
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (s : Finset (ℕ × ℕ)) (δ : ℝ) (hδ : 0 ≤ δ) (R cap : ℕ)
    (D L Z P : ℝ) (hD : 0 ≤ D) (hL : 0 ≤ L) (hZ : 1 ≤ Z) (hP : 0 ≤ P)
    (d : MomentData K ω ψ) (left right : Atom V)
    (slot : Fin d.geometry.slotCount → Atom V) (hcount : d.geometry.slotCount ≤ cap)
    (hleftExponent : left.exponent ∈ exponentPalette δ R)
    (hrightExponent : right.exponent ∈ exponentPalette δ R)
    (hslotExponent : ∀ i, (slot i).exponent ∈ exponentPalette δ R)
    (hleftDirection : ‖left.direction‖ ≤ D) (hrightDirection : ‖right.direction‖ ≤ D)
    (hslotDirection : ∀ i, ‖(slot i).direction‖ ≤ D)
    (hleftScale : left.scale ≤ Z ^ L) (hrightScale : right.scale ≤ Z ^ L)
    (hslotScale : ∀ i, (slot i).scale ≤ Z ^ L) :
    profileAmplitude d left right slot window hcompact hpositive s P ≤
      commonAmplitudeConstant window hcompact hpositive s δ R cap D * P * Z ^ (L * R * δ) := by
  let C := profileAtomConstant window hcompact hpositive s δ R D
  let T := Z ^ (L * R * δ)
  have hC : 0 ≤ C := profileAtomConstant_nonneg window hcompact hpositive s δ R D hD
  have hT : 1 ≤ T := Real.one_le_rpow hZ (mul_nonneg (mul_nonneg hL (Nat.cast_nonneg _)) hδ)
  have hleft : left.profileCoefficient window hcompact hpositive s ≤ C * T :=
    left.profileCoefficient_le_palette_scale window hcompact hpositive s δ hδ R
      D L Z hD hL hZ hleftExponent hleftDirection hleftScale
  have hright : right.profileCoefficient window hcompact hpositive s ≤ C * T :=
    right.profileCoefficient_le_palette_scale window hcompact hpositive s δ hδ R
      D L Z hD hL hZ hrightExponent hrightDirection hrightScale
  have hslot (i) : (slot i).profileCoefficient window hcompact hpositive s ≤ C * T :=
    (slot i).profileCoefficient_le_palette_scale window hcompact hpositive s δ hδ R
      D L Z hD hL hZ (hslotExponent i) (hslotDirection i) (hslotScale i)
  have hsum : (∑ i, (slot i).profileCoefficient window hcompact hpositive s) ≤
      (d.geometry.slotCount : ℝ) * (C * T) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hslot i)
  have hsumCap : (∑ i, (slot i).profileCoefficient window hcompact hpositive s) ≤
      (cap : ℝ) * (C * T) := hsum.trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount)
      (mul_nonneg hC (zero_le_one.trans hT)))
  have hwhole : 1 + left.profileCoefficient window hcompact hpositive s +
      right.profileCoefficient window hcompact hpositive s +
        ∑ i, (slot i).profileCoefficient window hcompact hpositive s ≤
      (1 + ((cap : ℝ) + 2) * C) * T := by nlinarith
  unfold profileAmplitude
  apply (mul_le_mul_of_nonneg_left hwhole hP).trans_eq
  change P * ((1 + ((cap : ℝ) + 2) * C) * T) =
    (1 + ((cap : ℝ) + 2) * C) * P * T
  ring

end Amplitudes

/-- The final degree is part of the tilt choice.  The denominator is
strictly positive even if the scale exponent or the degree is zero. -/
def budgetTilt (L : ℝ) (R degree : ℕ) (ε : ℝ) : ℝ :=
  min (1 / 2) (ε / ((L * R) * degree + 1))

theorem budgetTilt_pos (L : ℝ) (hL : 0 ≤ L) (R degree : ℕ)
    (ε : ℝ) (hε : 0 < ε) : 0 < budgetTilt L R degree ε := by
  have hden : 0 < (L * R) * degree + 1 := by positivity
  exact lt_min (by norm_num) (div_pos hε hden)

theorem budgetTilt_lt_one (L : ℝ) (R degree : ℕ) (ε : ℝ) :
    budgetTilt L R degree ε < 1 :=
  (min_le_left _ _).trans_lt (by norm_num)

theorem budgetTilt_le_half (L : ℝ) (R degree : ℕ) (ε : ℝ) :
    budgetTilt L R degree ε ≤ 1 / 2 := min_le_left _ _

theorem budgetTilt_total_scale_budget (L : ℝ) (hL : 0 ≤ L) (R degree : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    (L * R * budgetTilt L R degree ε) * degree ≤ ε := by
  have hden : 0 < (L * R) * degree + 1 := by positivity
  have hδ := (budgetTilt_pos L hL R degree ε hε).le
  have hdiv : budgetTilt L R degree ε ≤ ε / ((L * R) * degree + 1) := min_le_right _ _
  have hm := (le_div_iff₀ hden).mp hdiv
  calc
    _ = budgetTilt L R degree ε * ((L * R) * degree) := by ring
    _ ≤ budgetTilt L R degree ε * ((L * R) * degree + 1) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hδ
    _ ≤ ε := hm

theorem budgetTilt_scale_exponent_le (L : ℝ) (hL : 0 ≤ L) (R : ℕ)
    (τ : ℝ) (hτ : 0 < τ) : L * R * budgetTilt L R 1 τ ≤ τ := by
  simpa only [Nat.cast_one, mul_one] using budgetTilt_total_scale_budget L hL R 1 τ hτ

def clippedAmplitudeConstant (a B : ℝ) (ha : 0 < a) (s : Finset (ℕ × ℕ))
    (δ : ℝ) (R cap : ℕ) (D : ℝ) : ℝ :=
  clippingCoefficient B s * commonAmplitudeConstant (Set.Icc a B) isCompact_Icc
    (positiveAnnulus a B ha) s δ R cap D

theorem clippedAmplitudeConstant_one_le (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B)
    (s : Finset (ℕ × ℕ)) (δ : ℝ) (R cap : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    1 ≤ clippedAmplitudeConstant a B ha s δ R cap D := by
  have hc := clippingCoefficient_one_le B hB s
  have hA := commonAmplitudeConstant_one_le (Set.Icc a B) isCompact_Icc
    (positiveAnnulus a B ha) s δ R cap D hD
  simpa only [clippedAmplitudeConstant, one_mul] using
    mul_le_mul hc hA zero_le_one (zero_le_one.trans hc)

section ClippedAmplitudes

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem clippedProfileAmplitude_le_original_scale
    (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B) (s : Finset (ℕ × ℕ))
    (δ : ℝ) (hδ : 0 ≤ δ) (R cap : ℕ)
    (D L Z P : ℝ) (hD : 0 ≤ D) (hL : 0 ≤ L) (hZ : 1 ≤ Z) (hP : 0 ≤ P)
    (d : MomentData K ω ψ) (left right : Atom (WithLp 2 (U × E)))
    (slot : Fin d.geometry.slotCount → Atom (WithLp 2 (U × E)))
    (hcount : d.geometry.slotCount ≤ cap)
    (hleftExponent : left.exponent ∈ exponentPalette δ R)
    (hrightExponent : right.exponent ∈ exponentPalette δ R)
    (hslotExponent : ∀ i, (slot i).exponent ∈ exponentPalette δ R)
    (hleftDirection : ‖left.direction‖ ≤ D) (hrightDirection : ‖right.direction‖ ≤ D)
    (hslotDirection : ∀ i, ‖(slot i).direction‖ ≤ D)
    (hleftScale : left.scale ≤ Z ^ L) (hrightScale : right.scale ≤ Z ^ L)
    (hslotScale : ∀ i, (slot i).scale ≤ Z ^ L) :
    clippedProfileAmplitude d left right slot a B ha s P ≤
      clippedAmplitudeConstant a B ha s δ R cap D * P * Z ^ (L * R * δ) := by
  have hraw := profileAmplitude_le_original_scale (Set.Icc a B) isCompact_Icc
    (positiveAnnulus a B ha) s δ hδ R cap D L Z P hD hL hZ hP
    d left right slot hcount hleftExponent hrightExponent hslotExponent
    hleftDirection hrightDirection hslotDirection hleftScale hrightScale hslotScale
  have hC : 0 ≤ clippingCoefficient B s := zero_le_one.trans (clippingCoefficient_one_le B hB s)
  unfold clippedProfileAmplitude
  apply (mul_le_mul_of_nonneg_left hraw hC).trans_eq
  unfold clippedAmplitudeConstant
  ring

/-- The tilt and the common coefficient are chosen before `Z`, the
original profiles, the atoms, and their Fourier variables.  The
constant satisfies the `1 ≤ Cprofile` convention of mass absorption. -/
theorem exists_clipped_amplitude_scale_budget
    (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B) (s : Finset (ℕ × ℕ))
    (R cap : ℕ) (D L τ : ℝ) (hD : 0 ≤ D) (hL : 0 ≤ L) (hτ : 0 < τ) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ δ < 1 ∧ 1 ≤ C ∧ L * R * δ ≤ τ ∧
      ∀ (Z P : ℝ), 1 ≤ Z → 0 ≤ P →
      ∀ (d : MomentData K ω ψ) (left right : Atom (WithLp 2 (U × E)))
        (slot : Fin d.geometry.slotCount → Atom (WithLp 2 (U × E))),
      d.geometry.slotCount ≤ cap →
      left.exponent ∈ exponentPalette δ R → right.exponent ∈ exponentPalette δ R →
      (∀ i, (slot i).exponent ∈ exponentPalette δ R) →
      ‖left.direction‖ ≤ D → ‖right.direction‖ ≤ D →
      (∀ i, ‖(slot i).direction‖ ≤ D) →
      left.scale ≤ Z ^ L → right.scale ≤ Z ^ L → (∀ i, (slot i).scale ≤ Z ^ L) →
        clippedProfileAmplitude d left right slot a B ha s P ≤ C * P * Z ^ τ := by
  let δ := budgetTilt L R 1 τ
  let C := clippedAmplitudeConstant a B ha s δ R cap D
  have hδ : 0 < δ := budgetTilt_pos L hL R 1 τ hτ
  have hC : 1 ≤ C := clippedAmplitudeConstant_one_le a B ha hB s δ R cap D hD
  have hbudget : L * R * δ ≤ τ := budgetTilt_scale_exponent_le L hL R τ hτ
  refine ⟨δ, C, hδ, budgetTilt_le_half L R 1 τ, budgetTilt_lt_one L R 1 τ, hC, hbudget, ?_⟩
  intro Z P hZ hP d left right slot hcount hlE hrE hsE hlD hrD hsD hlS hrS hsS
  have hraw := clippedProfileAmplitude_le_original_scale a B ha hB s δ hδ.le R cap
    D L Z P hD hL hZ hP d left right slot hcount hlE hrE hsE hlD hrD hsD hlS hrS hsS
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ hbudget) (mul_nonneg (zero_le_one.trans hC) hP))

end ClippedAmplitudes

private theorem one_add_amplitude_power_le
    (amplitude C P Z η ε : ℝ) (degree : ℕ)
    (hamp0 : 0 ≤ amplitude) (hC : 0 ≤ C) (hP : 1 ≤ P) (hZ : 1 ≤ Z) (hη : 0 ≤ η)
    (hamp : amplitude ≤ C * P * Z ^ η) (hbudget : η * degree ≤ ε) :
    (1 + amplitude) ^ degree ≤ (1 + C) ^ degree * P ^ degree * Z ^ ε := by
  have hT : 1 ≤ Z ^ η := Real.one_le_rpow hZ hη
  have hPT : 1 ≤ P * Z ^ η := by
    simpa only [one_mul] using mul_le_mul hP hT zero_le_one (zero_le_one.trans hP)
  have hone : 1 + amplitude ≤ (1 + C) * P * Z ^ η := by
    calc
      _ ≤ P * Z ^ η + C * P * Z ^ η := add_le_add hPT hamp
      _ = _ := by ring
  have hpow := pow_le_pow_left₀ (by positivity) hone degree
  have hZpower : (Z ^ η) ^ degree = Z ^ (η * (degree : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hZ)]
  calc
    _ ≤ ((1 + C) * P * Z ^ η) ^ degree := hpow
    _ = (1 + C) ^ degree * P ^ degree * Z ^ (η * degree) := by
      rw [mul_pow, mul_pow, hZpower]
    _ ≤ (1 + C) ^ degree * P ^ degree * Z ^ ε :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hbudget)
        (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (zero_le_one.trans hP) _))

section FullDegree

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The complete pre-removal degree is paid after selecting the tilt.
This is a statement about the actual computed clipped amplitude, with
only original atom count, direction, exponent and scale hypotheses. -/
theorem exists_clipped_amplitude_degree_budget
    (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B) (s : Finset (ℕ × ℕ))
    (R cap degree : ℕ) (D L ε : ℝ) (hD : 0 ≤ D) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ δ < 1 ∧ 1 ≤ C ∧
      ∀ (Z P : ℝ), 1 ≤ Z → 1 ≤ P →
      ∀ (d : MomentData K ω ψ) (left right : Atom (WithLp 2 (U × E)))
        (slot : Fin d.geometry.slotCount → Atom (WithLp 2 (U × E))),
      d.geometry.slotCount ≤ cap →
      left.exponent ∈ exponentPalette δ R → right.exponent ∈ exponentPalette δ R →
      (∀ i, (slot i).exponent ∈ exponentPalette δ R) →
      ‖left.direction‖ ≤ D → ‖right.direction‖ ≤ D →
      (∀ i, ‖(slot i).direction‖ ≤ D) →
      left.scale ≤ Z ^ L → right.scale ≤ Z ^ L → (∀ i, (slot i).scale ≤ Z ^ L) →
        (1 + clippedProfileAmplitude d left right slot a B ha s P) ^ degree ≤
          C * P ^ degree * Z ^ ε := by
  let δ := budgetTilt L R degree ε
  let Cprofile := clippedAmplitudeConstant a B ha s δ R cap D
  let C := (1 + Cprofile) ^ degree
  have hδ : 0 < δ := budgetTilt_pos L hL R degree ε hε
  have hCprofile : 1 ≤ Cprofile := clippedAmplitudeConstant_one_le a B ha hB s δ R cap D hD
  have hbase : 1 ≤ 1 + Cprofile := by linarith
  have hC : 1 ≤ C := one_le_pow₀ hbase
  refine ⟨δ, C, hδ, budgetTilt_le_half L R degree ε,
    budgetTilt_lt_one L R degree ε, hC, ?_⟩
  intro Z P hZ hP d left right slot hcount hlE hrE hsE hlD hrD hsD hlS hrS hsS
  have hraw := clippedProfileAmplitude_le_original_scale a B ha hB s δ hδ.le R cap
    D L Z P hD hL hZ (zero_le_one.trans hP) d left right slot
    hcount hlE hrE hsE hlD hrD hsD hlS hrS hsS
  exact one_add_amplitude_power_le
    (clippedProfileAmplitude d left right slot a B ha s P) Cprofile P Z (L * R * δ) ε degree
    (clippedProfileAmplitude_nonneg d left right slot a B ha hB s (zero_le_one.trans hP))
    (zero_le_one.trans hCprofile) hP hZ
    (mul_nonneg (mul_nonneg hL (Nat.cast_nonneg _)) hδ.le) hraw
    (budgetTilt_total_scale_budget L hL R degree ε hε)

end FullDegree
end CanonicalLogProfiles
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.profileAmplitude_le_original_scale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.exists_clipped_amplitude_scale_budget
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.exists_clipped_amplitude_degree_budget
