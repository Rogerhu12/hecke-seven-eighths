import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LocalCRT
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ChildAssembly

/-!
# Actual complete correlations and their separated children

The common-support identity used for the divisor expansion is proved here
for the source's complete sextic characters.  The arithmetic input left to
MOM_BASE is precisely the finite character expansion of the three
reciprocity phases.  Neither a correlation factorization nor an estimate
on the parent energy is assumed.

The coefficients `c` and `d` are unchanged by this identity.  They may be
the full centered coefficients, including every frozen factor and mask.
The two column characters retain the actual frequencies `h` and `-h`.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open UniqueFactorizationMonoid

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}

/-- The complete reciprocal phase before its finite-character expansion. -/
def actualCommonPhase (ID IE IA IB : A.Exterior) (d e a b : A.R) : ℂ :=
  (σ (A.sexticResidue IE a) * star (σ (A.sexticResidue IA e))) *
    (σ (A.sexticResidue IB d) * star (σ (A.sexticResidue ID b))) *
    (σ (A.sexticResidue IB a) * star (σ (A.sexticResidue IA b)))

/-- The complete-correlation factorization with quotient finiteness
derived from the actual exterior ideals. -/
theorem generated_correlation_common_support
    (ID IE IA IB IDA IEB : A.Exterior)
    (hIDA : IDA.val = ID.val * IA.val) (hIEB : IEB.val = IE.val * IB.val)
    (d e a b : A.R)
    (hd : A.Generates ID d) (he : A.Generates IE e)
    (ha : A.Generates IA a) (hb : A.Generates IB b)
    (hda : A.Generates IDA (d * a)) (heb : A.Generates IEB (e * b))
    (hDa : IsCoprime ID.val IA.val) (hEa : IsCoprime IE.val IA.val)
    (hDb : IsCoprime ID.val IB.val) (hEb : IsCoprime IE.val IB.val)
    (hab : IsCoprime IA.val IB.val) (h : A.R) :
    generatedIdealCorrelation (σ := σ) IDA IEB (d * a) (e * b) hda heb h =
      generatedIdealCorrelation (σ := σ) ID IE d e hd he h *
        actualCommonPhase (σ := σ) ID IE IA IB d e a b *
          (σ (A.sexticResidue IA h) * star (σ (A.sexticResidue IB (-h)))) := by
  letI : Finite (A.R ⧸ Ideal.span {d}) := by rw [hd.2]; exact A.exteriorResidue_finite ID
  letI : Finite (A.R ⧸ Ideal.span {e}) := by rw [he.2]; exact A.exteriorResidue_finite IE
  letI : Finite (A.R ⧸ Ideal.span {a}) := by rw [ha.2]; exact A.exteriorResidue_finite IA
  letI : Finite (A.R ⧸ Ideal.span {b}) := by rw [hb.2]; exact A.exteriorResidue_finite IB
  letI : Finite (A.R ⧸ Ideal.span {d * a}) := by rw [hda.2]; exact A.exteriorResidue_finite IDA
  letI : Finite (A.R ⧸ Ideal.span {e * b}) := by rw [heb.2]; exact A.exteriorResidue_finite IEB
  letI : Fintype (A.R ⧸ Ideal.span {d}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {e}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {a}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {b}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {d * a}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {e * b}) := Fintype.ofFinite _
  have hca : IsCoprime (d * e) a :=
    (generated_elements_coprime ID IA d a hd ha hDa).mul_left
      (generated_elements_coprime IE IA e a he ha hEa)
  have hcb : IsCoprime (d * e) b :=
    (generated_elements_coprime ID IB d b hd hb hDb).mul_left
      (generated_elements_coprime IE IB e b he hb hEb)
  have hcab : IsCoprime a b := generated_elements_coprime IA IB a b ha hb hab
  have hc := actual_complete_common_support (σ := σ) ID IE IA IB IDA IEB hIDA hIEB
    d e a b hd he ha hb hda heb hca hcb hcab h
  change generatedIdealCorrelation (σ := σ) IDA IEB (d * a) (e * b) hda heb h = _ at hc
  rw [hc]
  simp only [generatedIdealCorrelation, actualCommonPhase]
  ring

/-- Exact divisor children of the actual full second correlation.
The pointwise phase expansion is the finite-reciprocity input of MOM_BASE;
the complete correlation and its coprimality expansion are proved here. -/
theorem actual_full_correlation_children {ι κ γ : Type*} [Fintype γ]
    (leftColumns : Finset ι) (rightColumns : Finset κ)
    (ID IE : A.Exterior) (IA : ι → A.Exterior) (IB : κ → A.Exterior)
    (IDA : ι → A.Exterior) (IEB : κ → A.Exterior)
    (hIDA : ∀ i, (IDA i).val = ID.val * (IA i).val)
    (hIEB : ∀ j, (IEB j).val = IE.val * (IB j).val)
    (d e : A.R) (a : ι → A.R) (b : κ → A.R)
    (hd : A.Generates ID d) (he : A.Generates IE e)
    (ha : ∀ i, A.Generates (IA i) (a i)) (hb : ∀ j, A.Generates (IB j) (b j))
    (hda : ∀ i, A.Generates (IDA i) (d * a i))
    (heb : ∀ j, A.Generates (IEB j) (e * b j))
    (hDa : ∀ i, IsCoprime ID.val (IA i).val)
    (hEa : ∀ i, IsCoprime IE.val (IA i).val)
    (hDb : ∀ j, IsCoprime ID.val (IB j).val)
    (hEb : ∀ j, IsCoprime IE.val (IB j).val)
    (phaseCoefficient : γ → ℂ) (leftPhase : γ → ι → ℂ) (rightPhase : γ → κ → ℂ)
    (hphase : ∀ i j, IsCoprime (IA i).val (IB j).val →
      actualCommonPhase (σ := σ) ID IE (IA i) (IB j) d e (a i) (b j) =
        ∑ χ : γ, phaseCoefficient χ * leftPhase χ i * star (rightPhase χ j))
    (c : ι → ℂ) (f : κ → ℂ) (h : A.R) :
    (∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
      (if IsCoprime (IA i).val (IB j).val then
        generatedIdealCorrelation (σ := σ) (IDA i) (IEB j)
          (d * a i) (e * b j) (hda i) (heb j) h else 0) * (c i * star (f j))) =
      ∑ L ∈ divisorPool rightColumns (fun j => (IB j).val),
        (moebius L : ℂ) * generatedIdealCorrelation (σ := σ) ID IE d e hd he h *
          ∑ χ : γ, phaseCoefficient χ *
            (divisorPolynomial leftColumns (fun i => (IA i).val) L c (leftPhase χ)
                (fun i z => σ (A.sexticResidue (IA i) z)) h *
              star (divisorPolynomial rightColumns (fun j => (IB j).val) L f (rightPhase χ)
                (fun j z => σ (A.sexticResidue (IB j) (-z))) h)) := by
  apply full_correlation_divisor_children leftColumns rightColumns
    (fun i => (IA i).val) (fun j => (IB j).val)
    (fun j _ => (IB j).property.1)
    (fun i j z => generatedIdealCorrelation (σ := σ) (IDA i) (IEB j)
      (d * a i) (e * b j) (hda i) (heb j) z)
    (generatedIdealCorrelation (σ := σ) ID IE d e hd he)
    phaseCoefficient leftPhase rightPhase
    (fun i z => σ (A.sexticResidue (IA i) z))
    (fun j z => σ (A.sexticResidue (IB j) (-z)))
  intro i j z hcop
  rw [generated_correlation_common_support ID IE (IA i) (IB j) (IDA i) (IEB j)
    (hIDA i) (hIEB j) d e (a i) (b j) hd he (ha i) (hb j) (hda i) (heb j)
    (hDa i) (hEa i) (hDb j) (hEb j) hcop z, hphase i j hcop]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_full_correlation_children
