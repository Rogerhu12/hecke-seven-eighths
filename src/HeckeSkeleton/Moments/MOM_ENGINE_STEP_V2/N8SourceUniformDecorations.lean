import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceResidualWindows

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! Uniform subpower cost of the actual original second-class
decorations, with every norm window derived from the source trace. -/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  coveredClassKeyFintype

namespace N8Source

theorem original_class_decoration_subpower (c : TargetContext K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (call : Call c) (input : ProfileInput call),
      normThreshold c call.frame ≤ call.base →
      ∀ (p : SourceParameters c) (trace : SourceTrace call p), trace.Realizes →
      ∀ (i : Fin trace.expansion.count)
        (LC RC : OriginalCover (trace.second.source i).physical),
        LC.Realizes → RC.Realizes →
        ∀ DE : (trace.second.source i).CommonLabel,
          (Fintype.card ((trace.second.source i).CommonDecoration LC RC DE) : ℝ) ≤
            C * call.base ^ ε := by
  let δ : ℝ := ε / 5
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, hpow⟩ := support_tuple_multiplicity_subpower (K := K)
    (c.geometry.slots + 2) (columnExponent c) δ (columnExponent_pos c).le hδ
  obtain ⟨R, hR, hdiv⟩ := support_tuple_multiplicity_subpower (K := K)
    1 (columnExponent c) δ (columnExponent_pos c).le hδ
  let U : ℕ := Nat.card
    (SixthUnitClasses K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))))
  refine ⟨A ^ 4 * (R * (U : ℝ) + 1), by positivity, ?_⟩
  intro call input large p trace htrace i LC RC hLC hRC DE
  have hbase_pos : 0 < call.base := call.base_pos
  have hnorm := trace.second.common_norm input large htrace.first htrace.cauchy
    htrace.expansion htrace.second i DE
  have hne : (trace.second.source i).physical.source.columns.Nonempty := by
    obtain ⟨ij, hij, _⟩ := Finset.mem_image.mp DE.property
    exact ⟨ij.1, (Finset.mem_product.mp hij).1⟩
  have hcombined := trace.second.combined_extraction_norm input large htrace.first
    htrace.cauchy htrace.expansion htrace.second i hne
  have hLC' : (LC.cover.labels.card : ℝ) ≤ A * call.base ^ δ := by
    have h := trace.second.original_cover_card_le htrace.first htrace.cauchy
      htrace.expansion htrace.second i LC hLC
    have h' : (LC.cover.labels.card : ℝ) ≤
        (idealDivisorCount ((trace.second.source i).physical.first.selected.val *
          (trace.second.source i).physical.first.poolPower.val) : ℝ) ^
            (c.geometry.slots + 2) := by exact_mod_cast h
    exact h'.trans (hpow call.base call.domain.scale.le _ hcombined)
  have hRC' : (RC.cover.labels.card : ℝ) ≤ A * call.base ^ δ := by
    have h := trace.second.original_cover_card_le htrace.first htrace.cauchy
      htrace.expansion htrace.second i RC hRC
    have h' : (RC.cover.labels.card : ℝ) ≤
        (idealDivisorCount ((trace.second.source i).physical.first.selected.val *
          (trace.second.source i).physical.first.poolPower.val) : ℝ) ^
            (c.geometry.slots + 2) := by exact_mod_cast h
    exact h'.trans (hpow call.base call.domain.scale.le _ hcombined)
  have hD : (idealDivisorCount DE.val.1 : ℝ) ^ (c.geometry.slots + 2) ≤
      A * call.base ^ δ := hpow call.base call.domain.scale.le _ hnorm.1
  have hE : (idealDivisorCount DE.val.2 : ℝ) ^ (c.geometry.slots + 2) ≤
      A * call.base ^ δ := hpow call.base call.domain.scale.le _ hnorm.2
  have hrowDiv : (idealDivisorCount DE.val.1 : ℝ) ≤ R * call.base ^ δ := by
    simpa only [pow_one] using hdiv call.base call.domain.scale.le _ hnorm.1
  have hrow : ((idealDivisorCount DE.val.1 * U + 1 : ℕ) : ℝ) ≤
      (R * (U : ℝ) + 1) * call.base ^ δ := by
    calc
      _ = (idealDivisorCount DE.val.1 : ℝ) * (U : ℝ) + 1 := by norm_cast
      _ ≤ (R * call.base ^ δ) * (U : ℝ) + call.base ^ δ :=
        add_le_add (mul_le_mul_of_nonneg_right hrowDiv (Nat.cast_nonneg _))
          (Real.one_le_rpow call.domain.scale.le hδ.le)
      _ = _ := by ring
  have hcard : (Fintype.card ((trace.second.source i).CommonDecoration LC RC DE) : ℝ) ≤
      (LC.cover.labels.card : ℝ) * (RC.cover.labels.card : ℝ) *
        ((idealDivisorCount DE.val.1 * U + 1 : ℕ) : ℝ) *
        (idealDivisorCount DE.val.1 : ℝ) ^ (c.geometry.slots + 2) *
        (idealDivisorCount DE.val.2 : ℝ) ^ (c.geometry.slots + 2) := by
    exact_mod_cast (trace.second.source i).commonDecoration_card_le LC RC
      (htrace.second.stage i) hLC hRC DE
  have hLR := mul_le_mul hLC' hRC' (Nat.cast_nonneg _)
    (mul_nonneg hA.le (Real.rpow_nonneg call.base_pos.le _))
  have hLRrow := mul_le_mul hLR hrow (Nat.cast_nonneg _)
    (by positivity : 0 ≤ (A * call.base ^ δ) * (A * call.base ^ δ))
  have hLRrowD := mul_le_mul hLRrow hD (pow_nonneg (Nat.cast_nonneg _) _)
    (by positivity : 0 ≤ (A * call.base ^ δ) * (A * call.base ^ δ) *
      ((R * (U : ℝ) + 1) * call.base ^ δ))
  have hfull := mul_le_mul hLRrowD hE (pow_nonneg (Nat.cast_nonneg _) _)
    (by positivity : 0 ≤ (A * call.base ^ δ) * (A * call.base ^ δ) *
      ((R * (U : ℝ) + 1) * call.base ^ δ) * (A * call.base ^ δ))
  apply (hcard.trans hfull).trans_eq
  have he : ε = δ + δ + δ + δ + δ := by dsimp [δ]; ring
  rw [he, Real.rpow_add call.base_pos, Real.rpow_add call.base_pos,
    Real.rpow_add call.base_pos, Real.rpow_add call.base_pos]
  ring

end N8Source
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.original_class_decoration_subpower
