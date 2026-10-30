import HeckePort.Moments.Descent.Grid
import HeckePort.Moments.Descent.DivisorExtraction
import HeckePort.Moments.Descent.Quotients

/-!
# Extracting a divisor from a hybrid grid

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/ExtractedGrid.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

The quadratic row `quadraticRow k (primaryGenerator J)` is the abstract `q k J` with
`QuadraticRowAxioms`, the cubic kernel is the abstract `κ` with `CubicKernelAxioms`
(predicate `Ext` = "the primary generator is nonzero"), and `CubicSieve.Admissible` is a
divisor-closed predicate `CubAdm` all of whose members satisfy `Ext` (cf. `Descent/OriginalBlock`).
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators

variable {K : Type} [Field K] [NumberField K]

abbrev Grid (K : Type) [Field K] [NumberField K] :=
  Finset ((Ideal (𝓞 K) × Ideal (𝓞 K)) × Ideal (𝓞 K))

def quotientGridSupport (r : Ideal (𝓞 K)) (T : Grid K) : Grid K :=
  (T.filter fun u => r ∣ u.2).image fun u => (u.1, idealQuotient r u.2)

@[simp] theorem mem_quotientGridSupport (r : Ideal (𝓞 K)) (hr : r ≠ ⊥)
    (T : Grid K) (p : Ideal (𝓞 K) × Ideal (𝓞 K)) (c : Ideal (𝓞 K)) :
    (p, c) ∈ quotientGridSupport r T ↔ (p, r * c) ∈ T := by
  constructor
  · intro hu
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hu
    obtain ⟨huT, hru⟩ := Finset.mem_filter.mp hu
    have hp : u.1 = p := congrArg Prod.fst he
    have hc : idealQuotient r u.2 = c := congrArg Prod.snd he
    have hec : r * c = u.2 := by rw [← hc, idealQuotient_mul hru]
    simpa only [← hp, hec, Prod.eta] using huT
  · intro hu
    refine Finset.mem_image.mpr ⟨(p, r * c), Finset.mem_filter.mpr ⟨hu, dvd_mul_right _ _⟩, ?_⟩
    refine Prod.ext (show p = p from rfl) ?_
    exact mul_left_cancel₀ hr (idealQuotient_mul (dvd_mul_right r c))

theorem sum_quotientGridSupport {A : Type*} [AddCommMonoid A]
    (r : Ideal (𝓞 K)) (T : Grid K)
    (f : (Ideal (𝓞 K) × Ideal (𝓞 K)) × Ideal (𝓞 K) → A) :
    (∑ u ∈ T, if r ∣ u.2 then f u else 0) =
      ∑ u ∈ quotientGridSupport r T, f (u.1, r * u.2) := by
  rw [← Finset.sum_filter, quotientGridSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [idealQuotient_mul (Finset.mem_filter.mp hu).2]
  · intro u hu v hv he
    apply Prod.ext
    · simpa only using congrArg Prod.fst he
    · exact idealQuotient_injective_on r (Finset.mem_filter.mp hu).2
        (Finset.mem_filter.mp hv).2 (congrArg Prod.snd he)

theorem quotientGridSupport_origin (r : Ideal (𝓞 K)) (hr : r ≠ ⊥)
    (D : Finset (HybridColumnData K)) (p : Ideal (𝓞 K) × Ideal (𝓞 K)) (c : Ideal (𝓞 K))
    (hu : (p, c) ∈ quotientGridSupport r (hybridGridSupport D)) :
    ∃ d ∈ D, (d.residualN, d.residualB) = p ∧ d.common = r * c := by
  have hm := (mem_quotientGridSupport r hr (hybridGridSupport D) p c).mp hu
  obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hm
  exact ⟨d, hd, congrArg Prod.fst he, congrArg Prod.snd he⟩

theorem quotientGridCommonSupport_origin (r : Ideal (𝓞 K)) (hr : r ≠ ⊥)
    (D : Finset (HybridColumnData K)) (m c : Ideal (𝓞 K))
    (hc : c ∈ gridCommonSupport (quotientGridSupport r (hybridGridSupport D)) m) :
    ∃ d ∈ D, d.residualN = m ∧ d.common = r * c := by
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hc
  obtain ⟨huQ, hum⟩ := Finset.mem_filter.mp hu
  obtain ⟨d, hd, hp, hdc⟩ := quotientGridSupport_origin r hr D u.1 u.2 huQ
  refine ⟨d, hd, (congrArg Prod.fst hp).trans hum, ?_⟩
  simpa only [he] using hdc

def extractedGridCoefficient (T : Grid K) (R t : Ideal (𝓞 K))
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (c m h : Ideal (𝓞 K)) : ℂ :=
  if ((m, h), c) ∈ T then beta c m h * (if IsCoprime R (h * t) then 1 else 0) else 0

theorem extractedGridCoefficient_norm_le_one (T : Grid K) (R t : Ideal (𝓞 K))
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hb : ∀ u ∈ T, ‖beta u.2 u.1.1 u.1.2‖ ≤ 1)
    (c m h : Ideal (𝓞 K)) : ‖extractedGridCoefficient T R t beta c m h‖ ≤ 1 := by
  unfold extractedGridCoefficient
  split_ifs with hu hcop
  · simpa using hb ((m, h), c) hu
  · simp
  · simp

def gridDivisorHybridBlock (q κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (T : Grid K)
    (Pset : Finset (Ideal (𝓞 K))) (a : Ideal (𝓞 K) → ℂ)
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (t k R r : Ideal (𝓞 K)) : ℂ :=
  ∑ u ∈ T, if r ∣ u.2 then ∑ P ∈ Pset, if R ∣ P then
    a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta u.2 u.1.1 u.1.2 *
      (q k (u.1.1 * u.1.2) * κ P (u.2 * u.1.1)) *
        (if IsCoprime P (u.1.2 * t) then 1 else 0)
    else 0 else 0

theorem gridDivisorHybridBlock_eq_zero_of_quotientGrid_empty
    (q κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (T : Grid K) (Pset : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (t k R r : Ideal (𝓞 K)) (hQ : quotientGridSupport r T = ∅) :
    gridDivisorHybridBlock q κ T Pset a beta t k R r = 0 := by
  unfold gridDivisorHybridBlock
  rw [sum_quotientGridSupport, hQ]
  exact Finset.sum_empty

theorem gridDivisorHybridBlock_extract {Ext : Ideal (𝓞 K) → Prop} {Adm : Ideal (𝓞 K) → Prop}
    {q κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} (hκ : CubicKernelAxioms Ext κ)
    (hq : QuadraticRowAxioms Adm q)
    (CubAdm : Ideal (𝓞 K) → Prop) (hCubDvd : ∀ I J : Ideal (𝓞 K), CubAdm I → J ∣ I → CubAdm J)
    (hCubExt : ∀ P, CubAdm P → Ext P)
    (T : Grid K) (Pset : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (t k R r : Ideal (𝓞 K)) (hR : R ≠ ⊥) (hr : r ≠ ⊥)
    (hk : Adm ((R * r) * k))
    (hP : ∀ P ∈ Pset, CubAdm P) :
    gridDivisorHybridBlock q κ T Pset a beta t ((R * r) * k) R r =
      (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
        ∑ p ∈ (quotientGridSupport r T).image Prod.fst,
          q k (p.1 * p.2) *
            ∑ c ∈ gridCommonSupport (quotientGridSupport r T) p.1,
              hybridColumnCoefficient κ q R r (extractedGridCoefficient T R t beta) c p.1 p.2 *
                ∑ P ∈ quotientSupport R Pset,
                  hybridCubicCoefficient κ Ext R r p.2 t a P * κ P (c * p.1) := by
  have hmask (P h : Ideal (𝓞 K)) :
      (if IsCoprime (R * P) (h * t) then (1 : ℂ) else 0) =
      (if IsCoprime R (h * t) then 1 else 0) *
        (if IsCoprime P (h * t) then 1 else 0) := by
    simp only [IsCoprime.mul_left_iff]
    split_ifs <;> simp_all
  unfold gridDivisorHybridBlock
  rw [sum_quotientGridSupport]
  have hinner (u : (Ideal (𝓞 K) × Ideal (𝓞 K)) × Ideal (𝓞 K)) :
      (∑ P ∈ Pset, if R ∣ P then
        a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta (r * u.2) u.1.1 u.1.2 *
          (q ((R * r) * k) (u.1.1 * u.1.2) *
            κ P ((r * u.2) * u.1.1)) *
              (if IsCoprime P (u.1.2 * t) then 1 else 0) else 0) =
      ∑ P ∈ quotientSupport R Pset,
        a (R * P) / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) * beta (r * u.2) u.1.1 u.1.2 *
          (q ((R * r) * k) (u.1.1 * u.1.2) *
            κ (R * P) ((r * u.2) * u.1.1)) *
              (if IsCoprime (R * P) (u.1.2 * t) then 1 else 0) := by
    rw [← Finset.sum_filter]
    exact sum_quotientSupport R Pset _
  simp_rw [hinner]
  rw [finite_triple_support_reindex]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hu : (p, c) ∈ quotientGridSupport r T
  · have huc := (mem_quotientGridSupport r hr T p c).mp hu
    simp only [hu, ite_true]
    apply Finset.sum_congr rfl
    intro P hPP
    have hpgen := hCubExt P
      (quotientSupport_admissible CubAdm hCubDvd R hR Pset hP P hPP)
    have hid := hybrid_extracted_block_identity hκ hq R r k P c p.1 p.2 t hk hpgen a
      (extractedGridCoefficient T R t beta)
    simp only [extractedGridCoefficient, huc, ite_true] at hid
    rw [hmask]
    calc
      _ = a (R * P) / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) *
          (beta (r * c) p.1 p.2 * (if IsCoprime R (p.2 * t) then 1 else 0)) *
          (q ((R * r) * k) (p.1 * p.2) *
            κ (R * P) ((r * c) * p.1)) *
          (if IsCoprime P (p.2 * t) then 1 else 0) := by ring
      _ = _ := by rw [hid]; ring
  · have huc : (p, r * c) ∉ T := (mem_quotientGridSupport r hr T p c).not.mp hu
    simp [hu, hybridColumnCoefficient, extractedGridCoefficient, huc]

end HeckePort.Moments

end
