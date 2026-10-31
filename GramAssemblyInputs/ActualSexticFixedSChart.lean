import SIntegerSexticFixedFrequencyPeriod

/-! UNCOMPILED / native 0. Literal raw sextic times actual ALL-S RCorrection
on a fixed S chart. Chart membership is an actual ordinary-ideal congruence,
not a supplied coefficient-factorization assertion. All common-prime zeros
are retained by the zero-extended reciprocity theorem. -/

noncomputable section
namespace HeckeGeneral.Characters.ActualGramJointChartDraft
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "N" => NonzeroRingElements (S.integer K)
local notation "χ" => sIntegerSexticSymbol K S ζ hζ σ hS6
local notation "R" => sIntegerSexticRCorrection K S ζ hζ σ
local notation "MS" => sIntegerSexticSPlaceModulus K S ζ hζ
local notation "active" => fun n : N => Prod.snd (sLocalNonzeroIntegerDiagonal K S n)

/-- A genuine translate of the ordinary S-place modulus inside O_S.
The base point may have S-denominators. -/
def fixedSChart (base : N) : Set N :=
  {n | ∃ t : 𝓞 K, t ∈ MS ∧
    n.val - base.val = algebraMap (𝓞 K) (S.integer K) t}

@[simp] theorem mem_fixedSChart_self (base : N) :
    base ∈ fixedSChart K S ζ hζ base := by
  exact ⟨0, Ideal.zero_mem _, by simp⟩

/-- One common denominator converts an actual integral residue congruence
modulo (δ)MS into the ordinary increment required by the S-correction
period. No inverse of δ or unproved localization identification is used. -/
theorem mem_fixedSChart_of_cleared_congruence
    (δ z z₀ : 𝓞 K) (hδ : δ ≠ 0) (n base : N)
    (hn : algebraMap (𝓞 K) (S.integer K) δ * n.val =
      algebraMap (𝓞 K) (S.integer K) z)
    (hb : algebraMap (𝓞 K) (S.integer K) δ * base.val =
      algebraMap (𝓞 K) (S.integer K) z₀)
    (hz : z - z₀ ∈ Ideal.span ({δ} : Set (𝓞 K)) * MS) :
    n ∈ fixedSChart K S ζ hζ base := by
  obtain ⟨t, ht, he⟩ := Ideal.mem_span_singleton_mul.mp hz
  refine ⟨t, ht, ?_⟩
  have hδ' : algebraMap (𝓞 K) (S.integer K) δ ≠ 0 := by
    intro h
    apply hδ
    apply IsFractionRing.injective (𝓞 K) K
    simpa using congrArg (fun x : S.integer K => (x : K)) h
  apply mul_left_cancel₀ hδ'
  calc
    _ = algebraMap (𝓞 K) (S.integer K) (z - z₀) := by
      rw [mul_sub, hn, hb, map_sub]
    _ = algebraMap (𝓞 K) (S.integer K) (δ * t) := congrArg _ he.symm
    _ = _ := map_mul _ _ _

theorem RCorrection_fixed_first_on_chart
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (k n base : N) (hn : n ∈ fixedSChart K S ζ hζ base)
    (hb : active base ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    R k n = R k base := by
  obtain ⟨t, ht, he⟩ := hn
  have h := (sIntegerSexticSPlaceCorrection_fixed_first_periodic
    K S ζ hζ Γ (nonzeroSIntegerFieldUnit K S k) n base t ht he hb).2
  exact congrArg (fun x => σ (x.val : K)) h

theorem RCorrection_on_charts
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (n₁ b₁ n₂ b₂ : N)
    (h₁ : n₁ ∈ fixedSChart K S ζ hζ b₁)
    (h₂ : n₂ ∈ fixedSChart K S ζ hζ b₂)
    (hb₁ : active b₁ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
    (hb₂ : active b₂ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    R n₁ n₂ = R b₁ b₂ := by
  obtain ⟨t₁, ht₁, he₁⟩ := h₁
  obtain ⟨t₂, ht₂, he₂⟩ := h₂
  exact sIntegerSexticRCorrection_periodic K S ζ hζ σ Γ
    n₁ b₁ n₂ b₂ t₁ t₂ ht₁ ht₂ he₁ he₂ hb₁ hb₂

/-- The negative frequency keeps its actual S-local correction. Only the
fixed denominator symbol is identified, via equality of the actual ideals. -/
theorem symbol_negative_denominator (a : S.integer K) (k : N) :
    χ a (sIntegerSexticNegativeFrequency K S k) = χ a k := by
  unfold sIntegerSexticSymbol
  simp only [sIntegerModulusContraction_negative_frequency] <;> rfl

/-- The precise fixed-chart phase, with the original negative frequency.
It is constructed from actual RCorrection, never a replacement definition
of RCorrection. -/
def actualChartPhase (k b₁ b₂ : N) : ℂ :=
  R k b₁ * conj (R (sIntegerSexticNegativeFrequency K S k) b₂) * R b₁ b₂

/-- Actual raw times R on every pair in the two fixed S charts. The
columns may share arbitrary exterior primes; their zero values remain in
the identity, so this theorem also applies after the full Mobius expansion. -/
theorem raw_mul_RCorrection_eq_chartPhase_mul_fixed_symbols
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (k n₁ b₁ n₂ b₂ : N)
    (h₁ : n₁ ∈ fixedSChart K S ζ hζ b₁)
    (h₂ : n₂ ∈ fixedSChart K S ζ hζ b₂)
    (hb₁ : active b₁ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
    (hb₂ : active b₂ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    sIntegerSexticRawCoefficient K S ζ hζ σ hS6 n₁ n₂ k * R n₁ n₂ =
      actualChartPhase K S ζ hζ σ k b₁ b₂ * (χ n₁.val k * conj (χ n₂.val k)) := by
  have hrec₁ : χ k.val n₁ = R k n₁ * χ n₁.val k :=
    sIntegerSexticSymbol_reciprocity K S ζ hζ σ hS6 k n₁
  have hrec₂ : χ (-k.val) n₂ =
      R (sIntegerSexticNegativeFrequency K S k) n₂ * χ n₂.val k := by
    have h := sIntegerSexticSymbol_reciprocity K S ζ hζ σ hS6
      (sIntegerSexticNegativeFrequency K S k) n₂
    rw [symbol_negative_denominator K S ζ hζ σ hS6] at h
    exact h
  change (χ k.val n₁ * conj (χ (-k.val) n₂)) * R n₁ n₂ = _
  rewrite [hrec₁, hrec₂,
    RCorrection_fixed_first_on_chart K S ζ hζ σ Γ k n₁ b₁ h₁ hb₁,
    RCorrection_fixed_first_on_chart K S ζ hζ σ Γ
      (sIntegerSexticNegativeFrequency K S k) n₂ b₂ h₂ hb₂,
    RCorrection_on_charts K S ζ hζ σ Γ n₁ b₁ n₂ b₂ h₁ h₂ hb₁ hb₂,
    map_mul]
  unfold actualChartPhase
  ring

end HeckeGeneral.Characters.ActualGramJointChartDraft
