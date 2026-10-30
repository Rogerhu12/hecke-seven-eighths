import HeckeGeneral.Characters.LocalComponent

/-!
# Local uniformizers and the sign of the norm character

The local normalized valuation is surjective onto the multiplicative integers
with zero.  We choose a preimage of `exp (-1)`, prove that this is a uniformizer,
and compute its norm as the inverse of the actual residue-field cardinality.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical NNReal

variable (K : Type*) [Field K] [NumberField K]

/-- The actual residue-field cardinality, expressed as the absolute ideal norm. -/
abbrev residueCard (v : HeightOneSpectrum (𝓞 K)) : ℕ := Ideal.absNorm v.asIdeal

theorem residueCard_eq_natCard (v : HeightOneSpectrum (𝓞 K)) :
    residueCard K v = Nat.card ((𝓞 K) ⧸ v.asIdeal) := rfl

theorem one_lt_residueCard (v : HeightOneSpectrum (𝓞 K)) : 1 < residueCard K v :=
  NumberField.HeightOneSpectrum.one_lt_absNorm v

/-- A concrete choice of a local element with normalized valuation `exp (-1)`. -/
def localUniformizer (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K :=
  Classical.choose (valuedAdicCompletion_surjective K v (WithZero.exp (-1 : ℤ)))

@[simp] theorem localUniformizer_valuation (v : HeightOneSpectrum (𝓞 K)) :
    (Valued.v (localUniformizer K v) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1 : ℤ) :=
  Classical.choose_spec (valuedAdicCompletion_surjective K v (WithZero.exp (-1 : ℤ)))

theorem localUniformizer_ne_zero (v : HeightOneSpectrum (𝓞 K)) : localUniformizer K v ≠ 0 := by
  intro hz
  have hv := localUniformizer_valuation K v
  rw [hz, map_zero] at hv
  exact WithZero.exp_ne_zero hv.symm

theorem valuation_eq_exp_neg_one_of_isUniformizer (v : HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletion K)
    (hπ : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).IsUniformizer π) :
    (Valued.v π : WithZero (Multiplicative ℤ)) = WithZero.exp (-1 : ℤ) := by
  have hgen := Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
    (v := (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))))
    (valuedAdicCompletion_surjective K v)
  exact hπ.val.trans (congrArg Units.val hgen)

theorem localUniformizer_isUniformizer (v : HeightOneSpectrum (𝓞 K)) :
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).IsUniformizer
      (localUniformizer K v) := by
  change (Valued.v (localUniformizer K v) : WithZero (Multiplicative ℤ)) = _
  rw [localUniformizer_valuation,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (valuedAdicCompletion_surjective K v)]
  rfl

theorem localNorm_eq_inv_residueCard_of_valuation (v : HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletion K)
    (hπ : (Valued.v π : WithZero (Multiplicative ℤ)) = WithZero.exp (-1 : ℤ)) :
    ‖π‖ = (residueCard K v : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, hπ]
  rw [WithZeroMulInt.toNNReal_neg_apply (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
    (WithZero.exp_ne_zero (a := (-1 : ℤ)))]
  change (↑((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-1 : ℤ)) : ℝ) = _
  simp [residueCard]

theorem localUniformizer_norm (v : HeightOneSpectrum (𝓞 K)) :
    ‖localUniformizer K v‖ = (residueCard K v : ℝ)⁻¹ :=
  localNorm_eq_inv_residueCard_of_valuation K v _ (localUniformizer_valuation K v)

theorem localNorm_eq_inv_residueCard_of_isUniformizer (v : HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletion K)
    (hπ : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).IsUniformizer π) :
    ‖π‖ = (residueCard K v : ℝ)⁻¹ :=
  localNorm_eq_inv_residueCard_of_valuation K v π
    (valuation_eq_exp_neg_one_of_isUniformizer K v π hπ)

/-- The chosen uniformizer as an element of the local multiplicative group. -/
def localUniformizerUnit (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ :=
  Units.mk0 (localUniformizer K v) (localUniformizer_ne_zero K v)

@[simp] theorem localUniformizerUnit_val (v : HeightOneSpectrum (𝓞 K)) :
    (localUniformizerUnit K v).val = localUniformizer K v := rfl

@[simp] theorem localUniformizerUnit_norm (v : HeightOneSpectrum (𝓞 K)) :
    ‖(localUniformizerUnit K v).val‖ = (residueCard K v : ℝ)⁻¹ := localUniformizer_norm K v

theorem idelicNorm_uniformizer (v : HeightOneSpectrum (𝓞 K)) :
    idelicNorm K (localIdeleEmbedding K v (localUniformizerUnit K v)) =
      (residueCard K v : ℝ)⁻¹ := by
  rw [idelicNorm_localIdeleEmbedding, localUniformizerUnit_norm]

/-- The negative-log convention yields the ideal-norm sign `exp (i * t * log q)`. -/
theorem heckeNormTwist_uniformizer (v : HeightOneSpectrum (𝓞 K)) (t : ℝ) :
    localComponent K v (heckeNormTwist K t) (localUniformizerUnit K v) =
      Circle.exp (t * Real.log (residueCard K v : ℝ)) := by
  rw [heckeNormTwist_local, localUniformizerUnit_norm, Real.log_inv, neg_neg]

end HeckeGeneral.Characters
