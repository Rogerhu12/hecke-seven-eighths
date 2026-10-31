import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SourceCartesianCover
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonTupleFibers

/-!
# Counting the original support keys and actual row classes

Each source key is the tuple of extracted ideals from the two original
plain occurrences and all original prime slots.  Its cardinality is
bounded by the divisor count of the actual extracted ideal.  The
uniform small-power constant below is obtained from the proved ideal
divisor bound before choosing the moving source or scale.

Row labels are counted only on the original finite row set.  A row
label may be padded with unused values, so its declared codomain size
is not charged.  A finite raw code controls that image through a
per-row identity, not through a supplied cardinality inequality.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

namespace OriginalFiniteFibre

/-- A raw row code consists of the selected original common-prime
subset, a fixed finite character class, and bounded dyadic coordinates.
Its meaning is supplied by the original per-row identities. -/
abbrev RowCode {P : Type*} (support : Finset P) (Θ : Type*)
    (dimension width : ℕ) :=
  support.powerset × Θ × (Fin dimension → Fin (width + 1))

theorem rowCode_card {P Θ : Type*} [Fintype Θ]
    (support : Finset P) (dimension width : ℕ) :
    Fintype.card (RowCode support Θ dimension width) =
      2 ^ support.card * Fintype.card Θ * (width + 1) ^ dimension := by
  simp only [RowCode, Fintype.card_prod, Fintype.card_coe, Finset.card_powerset,
    Fintype.card_pi_const, Fintype.card_fin]
  ac_rfl

/-- Factorization through an original finite code bounds precisely the
labels which occur.  The unused values of `label` are irrelevant. -/
theorem row_image_card_le {H L Code : Type*} [Fintype Code]
    (rows : Finset H) (label : H → L) (code : H → Code) (encode : Code → L)
    (hcode : ∀ h ∈ rows, label h = encode (code h)) :
    (rows.image label).card ≤ Fintype.card Code := by
  have hsub : rows.image label ⊆ (Finset.univ : Finset Code).image encode := by
    intro a ha
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨code h, Finset.mem_univ _, (hcode h hh).symm⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_image_le).trans_eq (Finset.card_univ))

theorem row_image_card_le_coordinates {H L P Θ : Type*} [Fintype Θ]
    (rows : Finset H) (label : H → L) (support : Finset P)
    (dimension width : ℕ) (code : H → RowCode support Θ dimension width)
    (encode : RowCode support Θ dimension width → L)
    (hcode : ∀ h ∈ rows, label h = encode (code h)) :
    (rows.image label).card ≤
      2 ^ support.card * Fintype.card Θ * (width + 1) ^ dimension := by
  simpa only [rowCode_card] using row_image_card_le rows label code encode hcode

end OriginalFiniteFibre

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}
variable {ι κ : Type*}

private theorem one_le_original_divisor_count (D : Ideal (𝓞 K)) (hD : D ≠ 0) :
    1 ≤ (idealDivisors D).card :=
  Nat.succ_le_of_lt (Finset.card_pos.mpr
    ⟨1, (mem_idealDivisors hD).mpr (one_dvd D)⟩)

namespace SourceCartesianAtlas

variable {columns : Finset ι} {ideal : ι → A.Exterior}
variable (T : SourceCartesianAtlas columns ideal)

/-- The original fixed slot cap also bounds every actual support key;
the two plain occurrences are retained explicitly. -/
theorem labels_card_le_cap (cap : ℕ) (hcap : T.slotCount ≤ cap)
    (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (hD : D ≠ 0) :
    (T.labels P D).card ≤ (idealDivisors D).card ^ (cap + 2) :=
  (T.labels_card_le P D hD).trans
    (pow_le_pow_right' (one_le_original_divisor_count D hD)
      (Nat.add_le_add_right hcap 2))

/-- Constants precede the scale and the entire original source atlas.
Only the original slot cap and the norm of the actual extracted ideal
are supplied; the label-cardinality conclusion is proved internally. -/
theorem labels_uniform_subpower (cap : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ (columns : Finset ι) (ideal : ι → A.Exterior)
        (T : SourceCartesianAtlas columns ideal), T.slotCount ≤ cap →
      ∀ (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)), D ≠ 0 →
        (Ideal.absNorm D : ℝ) ≤ Z ^ B → (T.labels P D).card ≤ C * Z ^ ε := by
  obtain ⟨C, hC, hcount⟩ :=
    support_tuple_multiplicity_subpower (K := K) (cap + 2) B ε hB hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ columns ideal T hcap P D hD hnorm
  have hk : ((T.labels P D).card : ℝ) ≤ (idealDivisorCount D : ℝ) ^ (cap + 2) := by
    exact_mod_cast T.labels_card_le_cap cap hcap P D hD
  exact hk.trans (hcount Z hZ D hnorm)

end SourceCartesianAtlas

namespace SourceCartesianCover

variable {columns : Finset ι} {ideal : ι → A.Exterior}
variable {otherColumns : Finset κ} {otherIdeal : κ → A.Exterior}
variable (LC : SourceCartesianCover columns ideal)
variable (RC : SourceCartesianCover otherColumns otherIdeal)

/-- With both common ideals fixed, these are precisely the remaining
cover keys, actual row labels and second extraction keys. -/
abbrev SupportClassKey {L : Type*} (labels : Finset L)
    (P : Finset (Ideal (𝓞 K))) (D E : Ideal (𝓞 K)) :=
  Σ a : LC.labels, Σ b : RC.labels,
    labels × (LC.branch a).labels P D × (RC.branch b).labels P E

theorem supportClassKey_card_le {L : Type*} (labels : Finset L)
    (P : Finset (Ideal (𝓞 K))) (D E : Ideal (𝓞 K))
    (hD : D ≠ 0) (hE : E ≠ 0) (cap : ℕ)
    (hLC : ∀ a, (LC.branch a).slotCount ≤ cap)
    (hRC : ∀ b, (RC.branch b).slotCount ≤ cap) :
    Fintype.card (LC.SupportClassKey RC labels P D E) ≤
      LC.labels.card * RC.labels.card * labels.card *
        (idealDivisors D).card ^ (cap + 2) *
          (idealDivisors E).card ^ (cap + 2) := by
  simp only [SupportClassKey, Fintype.card_sigma, Fintype.card_prod, Fintype.card_coe]
  calc
    _ ≤ ∑ _a : LC.labels, ∑ _b : RC.labels,
        labels.card * ((idealDivisors D).card ^ (cap + 2) *
          (idealDivisors E).card ^ (cap + 2)) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact Nat.mul_le_mul_left labels.card
        (Nat.mul_le_mul ((LC.branch a).labels_card_le_cap cap (hLC a) P D hD)
          ((RC.branch b).labels_card_le_cap cap (hRC b) P E hE))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ac_rfl

end SourceCartesianCover

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces} {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {originalColumns : Finset ι} {originalIdeal : ι → A.Exterior}

namespace FirstGaussPoolData

variable (d : FirstGaussPoolData C P ι)
variable (T : SourceCartesianAtlas originalColumns originalIdeal)
variable (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
variable (hcolumns : d.columns =
  originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
variable (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val S)

theorem mainSourceCartesianCover_card_le (cap : ℕ) (hcap : T.slotCount ≤ cap)
    (hD : D ≠ 0) (c : ι → ℂ) :
    (d.mainSourceCartesianCover T S D hcolumns hideal c).labels.card ≤
      (idealDivisors D).card ^ (cap + 2) :=
  T.labels_card_le_cap cap hcap S D hD

/-- The actual valuation source retains its prime and valuation tag.
Only its combined extraction key is charged here; no pool-size factor
is introduced. -/
theorem residualSourceCartesianCover_card_le (cap : ℕ) (hcap : T.slotCount ≤ cap)
    (hD : D ≠ 0) (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ) :
    (d.residualSourceCartesianCover T S D hcolumns hideal p n c).labels.card ≤
      (idealDivisors (D * p.val.asIdeal ^ n)).card ^ (cap + 2) := by
  have hDp : D * p.val.asIdeal ^ n ≠ 0 :=
    mul_ne_zero hD (pow_ne_zero n p.val.ne_bot)
  exact (d.combinedLabels_card_le T S D hD hcolumns hideal p n).trans
    (pow_le_pow_right' (one_le_original_divisor_count _ hDp)
      (Nat.add_le_add_right hcap 2))

end FirstGaussPoolData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalFiniteFibre.row_image_card_le_coordinates
#print axioms HeckeSkeleton.Moments.EngineStep.SourceCartesianAtlas.labels_uniform_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.SourceCartesianCover.supportClassKey_card_le
