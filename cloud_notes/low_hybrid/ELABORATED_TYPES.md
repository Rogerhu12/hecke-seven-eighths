# 全部定理的 Lean 展开类型与假设

从最终通过核验的 Lean 环境直接导出，共 955 个定理常量。
包含源码公开/私有定理，以及 Lean 自动生成的方程、结构投影等辅助定理。

每条类型包含继承的 section 变量、隐式参数、类型类与显式前提；保留定义名，不展开其定义体。
完整模块见 HeckeSkeleton/LowDeclarations.lean；原始输出与成功退出码见 build_logs/HeckeSkeleton.LowDeclarations.log。
便于阅读的源码签名和所属模块另见 THEOREM_INDEX.md。

## HeckeSkeleton.LowFrozenCube.awayPart_avoids

```lean
∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] (s : Finset.{u_1} ι) (v : ι → ℕ),
  HeckeSkeleton.LowFrozenCube.AvoidsSupport.{u_1} s (HeckeSkeleton.LowFrozenCube.awayPart.{u_1} s v)
```

## HeckeSkeleton.LowFrozenCube.canonicalPair_admissible

```lean
∀ {e m x : ℕ},
  HeckeSkeleton.LowFrozenCube.CanonicalFrozenPair m x →
    Eq.{1} e (HAdd.hAdd.{0, 0, 0} m (HMul.hMul.{0, 0, 0} 3 x)) → HeckeSkeleton.LowFrozenCube.AdmissibleExponent e
```

## HeckeSkeleton.LowFrozenCube.card_le_real_scale_of_linear_counting

```lean
∀ {I : Type u_1} (q : I → ℕ) (normI : I → ℝ),
  (∀ (i : I), Eq.{1} (normI i) ↑(q i)) →
    ∀ (C : ℝ),
      LE.le.{0} 0 C →
        HeckeSkeleton.LowHybrid.LinearNormCounting.{u_1} q C →
          ∀ (X : ℝ),
            LE.le.{0} 0 X →
              ∀ (s : Finset.{u_1} I),
                (∀ (i : I), Membership.mem.{u_1, u_1} s i → LE.le.{0} (normI i) X) →
                  LE.le.{0} (↑(Finset.card.{u_1} s)) (HMul.hMul.{0, 0, 0} C X)
```

## HeckeSkeleton.LowFrozenCube.coefficientScale_identity

```lean
∀ (Z v ell S B : ℝ),
  LT.lt.{0} 0 Z →
    Eq.{1}
      (HDiv.hDiv.{0, 0, 0}
        (HDiv.hDiv.{0, 0, 0} (Inv.inv.{0} (HPow.hPow.{0, 0, 0} Z (HAdd.hAdd.{0, 0, 0} S B)))
          (HPow.hPow.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z ell) 2))
        (HPow.hPow.{0, 0, 0} Z v))
      (HPow.hPow.{0, 0, 0} Z (HeckeSkeleton.LowFrozenCube.squaredCoefficientExponent v ell S B))
```

## HeckeSkeleton.LowFrozenCube.columnCoefficient_frozen

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A] (χ : A → MonoidHom.{u_2, 0} A ℂ) (Cop : A → A → Prop),
  (∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((χ a) b) 6) (ite.{1} (Cop a b) 1 0)) →
    ∀ (F : Finset.{u_1} ι) (ψ : ι → A → ℂ) (j v : ι → ℕ),
      (∀ (p : ι), HeckeSkeleton.LowFrozenCube.AdmissibleExponent (v p)) →
        ∀ (lam : A → ℂ) (amin x c : A),
          Cop c x →
            Eq.{1}
              (HeckeSkeleton.LowFrozenCube.columnCoefficient.{u_1, u_2} χ F ψ j v lam
                (HMul.hMul.{u_2, u_2, u_2} amin (HPow.hPow.{u_2, 0, u_2} x 3)) c)
              (HeckeSkeleton.LowFrozenCube.columnCoefficient.{u_1, u_2} χ F ψ j
                (HeckeSkeleton.LowFrozenCube.frozenBase.{u_1} v) lam amin c)
```

## HeckeSkeleton.LowFrozenCube.cubeProduct_injective_on

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (t : Finset.{u_1} (Prod.{u_1, u_1} A A))
  (split : A → Prod.{u_1, u_1} A A),
  (∀ (q : Prod.{u_1, u_1} A A),
      Membership.mem.{u_1, u_1} t q → Eq.{u_1 + 1} (split (HeckeSkeleton.LowFrozenCube.cubeProduct.{u_1} q)) q) →
    Set.InjOn.{u_1, u_1} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_1} ↑t
```

## HeckeSkeleton.LowFrozenCube.cubicSaving_dichotomy

```lean
∀ {v z : ℝ},
  LE.le.{0} 0 v →
    Eq.{1} (HeckeSkeleton.LowFrozenCube.cubicSaving v z) z ∨
      LE.le.{0} v (HMul.hMul.{0, 0, 0} 2 (HeckeSkeleton.LowFrozenCube.cubicSaving v z))
```

## HeckeSkeleton.LowFrozenCube.cubicSaving_le_left

```lean
∀ (v z : ℝ), LE.le.{0} (HeckeSkeleton.LowFrozenCube.cubicSaving v z) v
```

## HeckeSkeleton.LowFrozenCube.cubicSaving_le_right

```lean
∀ (v z : ℝ), LE.le.{0} (HeckeSkeleton.LowFrozenCube.cubicSaving v z) z
```

## HeckeSkeleton.LowFrozenCube.cubicSaving_nonneg

```lean
∀ {v z : ℝ}, LE.le.{0} 0 v → LE.le.{0} 0 z → LE.le.{0} 0 (HeckeSkeleton.LowFrozenCube.cubicSaving v z)
```

## HeckeSkeleton.LowFrozenCube.cubicScale_le

```lean
∀ (Z v z : ℝ),
  LE.le.{0} 1 Z →
    LE.le.{0} (HeckeSkeleton.LowFrozenCube.cubicScale Z v z)
      (HMul.hMul.{0, 0, 0} 3
        (HPow.hPow.{0, 0, 0} Z
          (Max.max.{0} v (Max.max.{0} z (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (HAdd.hAdd.{0, 0, 0} v z)) 3)))))
```

## HeckeSkeleton.LowFrozenCube.cubicScale_nonneg

```lean
∀ (Z v z : ℝ), LE.le.{0} 0 Z → LE.le.{0} 0 (HeckeSkeleton.LowFrozenCube.cubicScale Z v z)
```

## HeckeSkeleton.LowFrozenCube.cubic_growth_identity

```lean
∀ (v z : ℝ),
  Eq.{1} (Max.max.{0} v (Max.max.{0} z (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (HAdd.hAdd.{0, 0, 0} v z)) 3)))
    (HSub.hSub.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} v z) (HeckeSkeleton.LowFrozenCube.cubicSaving v z))
```

## HeckeSkeleton.LowFrozenCube.disjoint_add_right

```lean
∀ {ι : Type u_1} [DecidableEq.{u_1 + 1} ι] {P x n : ι → ℕ},
  (HeckeSkeleton.LowFrozenCube.DisjointValuations.{u_1} P fun p => HAdd.hAdd.{0, 0, 0} (x p) (n p)) ↔
    HeckeSkeleton.LowFrozenCube.DisjointValuations.{u_1} P x ∧ HeckeSkeleton.LowFrozenCube.DisjointValuations.{u_1} P n
```

## HeckeSkeleton.LowFrozenCube.disjoint_supported_of_avoids

```lean
∀ {ι : Type u_1} [DecidableEq.{u_1 + 1} ι] {s : Finset.{u_1} ι} {P x : ι → ℕ},
  HeckeSkeleton.LowFrozenCube.AvoidsSupport.{u_1} s P →
    HeckeSkeleton.LowFrozenCube.SupportedOn.{u_1} s x → HeckeSkeleton.LowFrozenCube.DisjointValuations.{u_1} P x
```

## HeckeSkeleton.LowFrozenCube.frozenBase_support_exact

```lean
∀ {ι : Type u_1} (v : ι → ℕ) (p : ι), Ne.{1} (HeckeSkeleton.LowFrozenCube.frozenBase.{u_1} v p) 0 ↔ Ne.{1} (v p) 0
```

## HeckeSkeleton.LowFrozenCube.frozenBase_supported

```lean
∀ {ι : Type u_1} {s : Finset.{u_1} ι} {v : ι → ℕ},
  HeckeSkeleton.LowFrozenCube.SupportedOn.{u_1} s v →
    HeckeSkeleton.LowFrozenCube.SupportedOn.{u_1} s (HeckeSkeleton.LowFrozenCube.frozenBase.{u_1} v)
```

## HeckeSkeleton.LowFrozenCube.frozenCubeExp_eq_zero_of_base_zero

```lean
∀ {e : ℕ},
  Eq.{1} (HeckeSkeleton.LowFrozenCube.frozenMin e) 0 → Eq.{1} (HeckeSkeleton.LowFrozenCube.frozenCubeExp e) 0
```

## HeckeSkeleton.LowFrozenCube.frozenCubeExp_zero

```lean
Eq.{1} (HeckeSkeleton.LowFrozenCube.frozenCubeExp 0) 0
```

## HeckeSkeleton.LowFrozenCube.frozenCubeInner_eq_fullCubeInner

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (χ : A → MonoidHom.{u_1, 0} A ℂ) (Cop : A → A → Prop),
  (∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((χ a) b) 6) (ite.{1} (Cop a b) 1 0)) →
    ∀ (t : Finset.{u_1} (Prod.{u_1, u_1} A A)) (split : A → Prod.{u_1, u_1} A A),
      (∀ (q : Prod.{u_1, u_1} A A),
          Membership.mem.{u_1, u_1} t q → Eq.{u_1 + 1} (split (HeckeSkeleton.LowFrozenCube.cubeProduct.{u_1} q)) q) →
        ∀ (B : A → A → A → ℂ) (d P c : A),
          (∀ (q : Prod.{u_1, u_1} A A), Membership.mem.{u_1, u_1} t q → Cop P q.1) →
            Eq.{1} (HeckeSkeleton.LowFrozenCube.frozenCubeInner.{u_1} χ Cop B t d P c)
              (HeckeSkeleton.LowFrozenCube.fullCubeInner.{u_1} χ Cop
                (HeckeSkeleton.LowFrozenCube.fullCubeCoefficient.{u_1} split B)
                (Finset.image.{u_1, u_1} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_1} t) d P c)
```

## HeckeSkeleton.LowFrozenCube.frozenCube_supported

```lean
∀ {ι : Type u_1} {s : Finset.{u_1} ι} {v : ι → ℕ},
  HeckeSkeleton.LowFrozenCube.SupportedOn.{u_1} s v →
    HeckeSkeleton.LowFrozenCube.SupportedOn.{u_1} s (HeckeSkeleton.LowFrozenCube.frozenCube.{u_1} v)
```

## HeckeSkeleton.LowFrozenCube.frozenExponent_decomposition

```lean
∀ (e : ℕ),
  HeckeSkeleton.LowFrozenCube.AdmissibleExponent e →
    Eq.{1} e
      (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowFrozenCube.frozenMin e)
        (HMul.hMul.{0, 0, 0} 3 (HeckeSkeleton.LowFrozenCube.frozenCubeExp e)))
```

## HeckeSkeleton.LowFrozenCube.frozenExponent_unique

```lean
∀ {e m x : ℕ},
  HeckeSkeleton.LowFrozenCube.CanonicalFrozenPair m x →
    Eq.{1} e (HAdd.hAdd.{0, 0, 0} m (HMul.hMul.{0, 0, 0} 3 x)) →
      Eq.{1} m (HeckeSkeleton.LowFrozenCube.frozenMin e) ∧ Eq.{1} x (HeckeSkeleton.LowFrozenCube.frozenCubeExp e)
```

## HeckeSkeleton.LowFrozenCube.frozenMin_cases

```lean
∀ (e : ℕ),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.frozenMin e) 0 ∨
    Eq.{1} (HeckeSkeleton.LowFrozenCube.frozenMin e) 1 ∨ Eq.{1} (HeckeSkeleton.LowFrozenCube.frozenMin e) 3
```

## HeckeSkeleton.LowFrozenCube.frozenMin_eq_zero_iff

```lean
∀ (e : ℕ), Eq.{1} (HeckeSkeleton.LowFrozenCube.frozenMin e) 0 ↔ Eq.{1} e 0
```

## HeckeSkeleton.LowFrozenCube.frozenMin_le

```lean
∀ (e : ℕ), HeckeSkeleton.LowFrozenCube.AdmissibleExponent e → LE.le.{0} (HeckeSkeleton.LowFrozenCube.frozenMin e) e
```

## HeckeSkeleton.LowFrozenCube.frozenMin_zero

```lean
Eq.{1} (HeckeSkeleton.LowFrozenCube.frozenMin 0) 0
```

## HeckeSkeleton.LowFrozenCube.frozenPair_canonical

```lean
∀ (e : ℕ),
  HeckeSkeleton.LowFrozenCube.CanonicalFrozenPair (HeckeSkeleton.LowFrozenCube.frozenMin e)
    (HeckeSkeleton.LowFrozenCube.frozenCubeExp e)
```

## HeckeSkeleton.LowFrozenCube.frozenSeparatedRow_energy_eq_hybrid

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (χ : A → MonoidHom.{u_1, 0} A ℂ) (Cop : A → A → Prop),
  (∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((χ a) b) 6) (ite.{1} (Cop a b) 1 0)) →
    ∀ (rows marks columns : Finset.{u_1} A) (t : Finset.{u_1} (Prod.{u_1, u_1} A A)) (split : A → Prod.{u_1, u_1} A A),
      (∀ (q : Prod.{u_1, u_1} A A),
          Membership.mem.{u_1, u_1} t q → Eq.{u_1 + 1} (split (HeckeSkeleton.LowFrozenCube.cubeProduct.{u_1} q)) q) →
        ∀ (a : A → ℂ) (B : A → A → A → ℂ),
          (∀ (P : A),
              Membership.mem.{u_1, u_1} marks P →
                ∀ (q : Prod.{u_1, u_1} A A), Membership.mem.{u_1, u_1} t q → Cop P q.1) →
            ∀ (ρ : A → ℂ),
              (∀ (d : A), Membership.mem.{u_1, u_1} rows d → Eq.{1} (Norm.norm.{0} (ρ d)) 1) →
                Eq.{1}
                  (∑ d ∈ rows,
                    HPow.hPow.{0, 0, 0}
                      (Norm.norm.{0}
                        (HMul.hMul.{0, 0, 0} (ρ d)
                          (HeckeSkeleton.LowFrozenCube.frozenSeparatedRow.{u_1} χ Cop a B marks columns t d)))
                      2)
                  (∑ d ∈ rows,
                    HPow.hPow.{0, 0, 0}
                      (Norm.norm.{0}
                        (HeckeSkeleton.LowFrozenCube.hybridSeparatedRow.{u_1} χ Cop a
                          (HeckeSkeleton.LowFrozenCube.fullCubeCoefficient.{u_1} split B) marks columns
                          (Finset.image.{u_1, u_1} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_1} t) d))
                      2)
```

## HeckeSkeleton.LowFrozenCube.frozenSeparatedRow_eq_hybrid

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (χ : A → MonoidHom.{u_1, 0} A ℂ) (Cop : A → A → Prop),
  (∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((χ a) b) 6) (ite.{1} (Cop a b) 1 0)) →
    ∀ (marks columns : Finset.{u_1} A) (t : Finset.{u_1} (Prod.{u_1, u_1} A A)) (split : A → Prod.{u_1, u_1} A A),
      (∀ (q : Prod.{u_1, u_1} A A),
          Membership.mem.{u_1, u_1} t q → Eq.{u_1 + 1} (split (HeckeSkeleton.LowFrozenCube.cubeProduct.{u_1} q)) q) →
        ∀ (a : A → ℂ) (B : A → A → A → ℂ),
          (∀ (P : A),
              Membership.mem.{u_1, u_1} marks P →
                ∀ (q : Prod.{u_1, u_1} A A), Membership.mem.{u_1, u_1} t q → Cop P q.1) →
            ∀ (d : A),
              Eq.{1} (HeckeSkeleton.LowFrozenCube.frozenSeparatedRow.{u_1} χ Cop a B marks columns t d)
                (HeckeSkeleton.LowFrozenCube.hybridSeparatedRow.{u_1} χ Cop a
                  (HeckeSkeleton.LowFrozenCube.fullCubeCoefficient.{u_1} split B) marks columns
                  (Finset.image.{u_1, u_1} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_1} t) d)
```

## HeckeSkeleton.LowFrozenCube.frozenValuation_decomposition

```lean
∀ {ι : Type u_1} (v : ι → ℕ),
  (∀ (p : ι), HeckeSkeleton.LowFrozenCube.AdmissibleExponent (v p)) →
    Eq.{u_1 + 1} v fun p =>
      HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowFrozenCube.frozenBase.{u_1} v p)
        (HMul.hMul.{0, 0, 0} 3 (HeckeSkeleton.LowFrozenCube.frozenCube.{u_1} v p))
```

## HeckeSkeleton.LowFrozenCube.frozenValuation_unique

```lean
∀ {ι : Type u_1} {v a x : ι → ℕ},
  (∀ (p : ι), HeckeSkeleton.LowFrozenCube.CanonicalFrozenPair (a p) (x p)) →
    (∀ (p : ι), Eq.{1} (v p) (HAdd.hAdd.{0, 0, 0} (a p) (HMul.hMul.{0, 0, 0} 3 (x p)))) →
      Eq.{u_1 + 1} a (HeckeSkeleton.LowFrozenCube.frozenBase.{u_1} v) ∧
        Eq.{u_1 + 1} x (HeckeSkeleton.LowFrozenCube.frozenCube.{u_1} v)
```

## HeckeSkeleton.LowFrozenCube.frozen_cube_hybrid_summand

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (χ : A → MonoidHom.{u_1, 0} A ℂ) (Cop : A → A → Prop),
  (∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((χ a) b) 6) (ite.{1} (Cop a b) 1 0)) →
    ∀ (d P c x n : A),
      Cop P x →
        Eq.{1}
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} ((χ d) x) 3)
                (HPow.hPow.{0, 0, 0} ((χ d) (HMul.hMul.{u_1, u_1, u_1} c n)) 3))
              (HPow.hPow.{0, 0, 0} ((χ P) c) 4))
            (ite.{1} (Cop P n) 1 0))
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0}
              (HPow.hPow.{0, 0, 0} ((χ d) (HMul.hMul.{u_1, u_1, u_1} c (HMul.hMul.{u_1, u_1, u_1} x n))) 3)
              (HPow.hPow.{0, 0, 0} ((χ P) c) 4))
            (ite.{1} (Cop P (HMul.hMul.{u_1, u_1, u_1} x n)) 1 0))
```

## HeckeSkeleton.LowFrozenCube.frozen_cube_row_phase

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (χ : A → MonoidHom.{u_1, 0} A ℂ) (d c x n : A),
  Eq.{1}
    (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} ((χ d) x) 3)
      (HPow.hPow.{0, 0, 0} ((χ d) (HMul.hMul.{u_1, u_1, u_1} c n)) 3))
    (HPow.hPow.{0, 0, 0} ((χ d) (HMul.hMul.{u_1, u_1, u_1} c (HMul.hMul.{u_1, u_1, u_1} x n))) 3)
```

## HeckeSkeleton.LowFrozenCube.frozen_cube_square_phase

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (χ : A → MonoidHom.{u_1, 0} A ℂ) (Cop : A → A → Prop),
  (∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((χ a) b) 6) (ite.{1} (Cop a b) 1 0)) →
    ∀ (P x : A), Cop P x → Eq.{1} (HPow.hPow.{0, 0, 0} ((χ P) (HPow.hPow.{u_1, 0, u_1} x 3)) 2) 1
```

## HeckeSkeleton.LowFrozenCube.frozen_energy_eq_hybridEnergy

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (chi : A → MonoidHom.{u_1, 0} A ℂ) (cop : A → A → Prop),
  (∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((chi a) b) 6) (ite.{1} (cop a b) 1 0)) →
    ∀ (normI : A → ℝ) (rows marks columns : Finset.{u_1} A) (t : Finset.{u_1} (Prod.{u_1, u_1} A A))
      (split : A → Prod.{u_1, u_1} A A),
      (∀ (q : Prod.{u_1, u_1} A A),
          Membership.mem.{u_1, u_1} t q → Eq.{u_1 + 1} (split (HeckeSkeleton.LowFrozenCube.cubeProduct.{u_1} q)) q) →
        ∀ (a : A → ℂ) (B : A → A → A → ℂ),
          (∀ (P : A),
              Membership.mem.{u_1, u_1} marks P →
                ∀ (q : Prod.{u_1, u_1} A A), Membership.mem.{u_1, u_1} t q → cop P q.1) →
            ∀ (rho : A → ℂ),
              (∀ (k : A), Membership.mem.{u_1, u_1} rows k → Eq.{1} (Norm.norm.{0} (rho k)) 1) →
                Eq.{1}
                  (∑ k ∈ rows,
                    HPow.hPow.{0, 0, 0}
                      (Norm.norm.{0}
                        (HMul.hMul.{0, 0, 0} (rho k)
                          (HeckeSkeleton.LowFrozenCube.frozenSeparatedRow.{u_1} chi cop
                            (fun P => HDiv.hDiv.{0, 0, 0} (a P) ↑√(normI P)) B marks columns t k)))
                      2)
                  (HeckeSkeleton.LowHybrid.hybridEnergy.{u_1} (fun i j => (chi i) j) cop normI a
                    (HeckeSkeleton.LowFrozenCube.fullCubeCoefficient.{u_1} split B) rows marks columns
                    (Finset.image.{u_1, u_1} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_1} t))
```

## HeckeSkeleton.LowFrozenCube.frozen_pair_count_small_power

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    ∀ (Ccount : ℝ),
      LT.lt.{0} 0 Ccount →
        (∀ (a : A), LE.le.{0} 1 (q a)) →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
            ∀ (eps : ℝ),
              LT.lt.{0} 0 eps →
                ∃ C,
                  LT.lt.{0} 0 C ∧
                    ∀ (K : ℝ),
                      LE.le.{0} 1 K →
                        ∀ (support : Finset.{u_1} ι) (pairs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
                          (∀ (u : Prod.{u_2, u_2} A A),
                              Membership.mem.{u_2, u_2} pairs u →
                                (∀ (p : ι),
                                    Eq.{1}
                                        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords u.1)
                                          p)
                                        0 ∨
                                      LE.le.{0} 2
                                        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords u.1)
                                          p)) ∧
                                  LE.le.{0} (normI u.1) K ∧
                                    HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords u.2 ∧
                                      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords support
                                        u.2) →
                            LE.le.{0} (↑(Finset.card.{u_2} pairs))
                              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C √K)
                                (HPow.hPow.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0} K
                                    (normI
                                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2} coords support)))
                                  eps))
```

## HeckeSkeleton.LowFrozenCube.frozen_product_decomposition

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A] (prime : ι → A) (s : Finset.{u_1} ι) (v : ι → ℕ),
  (∀ (p : ι), HeckeSkeleton.LowFrozenCube.AdmissibleExponent (v p)) →
    Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime s v)
      (HMul.hMul.{u_2, u_2, u_2}
        (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime s
          (HeckeSkeleton.LowFrozenCube.frozenBase.{u_1} v))
        (HPow.hPow.{u_2, 0, u_2}
          (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime s
            (HeckeSkeleton.LowFrozenCube.frozenCube.{u_1} v))
          3))
```

## HeckeSkeleton.LowFrozenCube.frozen_row_pair_count_small_power

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    ∀ (Ccount : ℝ),
      LT.lt.{0} 0 Ccount →
        (∀ (a : A), LE.le.{0} 1 (q a)) →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
            ∀ (eps : ℝ),
              LT.lt.{0} 0 eps →
                ∃ C,
                  LT.lt.{0} 0 C ∧
                    ∀ (K : ℝ),
                      LE.le.{0} 1 K →
                        ∀ (support : Finset.{u_1} ι) (rows : Finset.{u_2} A),
                          (∀ (k : A),
                              Membership.mem.{u_2, u_2} rows k →
                                LE.le.{0}
                                  (normI
                                    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords
                                      k))
                                  K) →
                            LE.le.{0}
                              (↑(Finset.card.{u_2}
                                  (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2} coords support rows)))
                              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C √K)
                                (HPow.hPow.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0} K
                                    (normI
                                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2} coords support)))
                                  eps))
```

## HeckeSkeleton.LowFrozenCube.frozen_scale_le

```lean
∀ (Z O H v ell S B z T : ℝ),
  LE.le.{0} 1 Z →
    LE.le.{0}
      (HMul.hMul.{0, 0, 0}
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z (HDiv.hDiv.{0, 0, 0} O 2))
            (HPow.hPow.{0, 0, 0} Z (HeckeSkeleton.LowFrozenCube.squaredCoefficientExponent v ell S B)))
          (HeckeSkeleton.LowFrozenCube.hybridScale Z H v ell z))
        (HPow.hPow.{0, 0, 0} Z (HeckeSkeleton.LowFrozenCube.squaredKernelExponent T v ell)))
      (HMul.hMul.{0, 0, 0} 6 (HPow.hPow.{0, 0, 0} Z (HeckeSkeleton.LowFrozenCube.reflectedExponent O H v ell S B z T)))
```

## HeckeSkeleton.LowFrozenCube.fullCubeCoefficient_energy

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (t : Finset.{u_1} (Prod.{u_1, u_1} A A))
  (split : A → Prod.{u_1, u_1} A A),
  (∀ (q : Prod.{u_1, u_1} A A),
      Membership.mem.{u_1, u_1} t q → Eq.{u_1 + 1} (split (HeckeSkeleton.LowFrozenCube.cubeProduct.{u_1} q)) q) →
    ∀ (B : A → A → A → ℂ) (c : A),
      Eq.{1}
        (∑ b ∈ Finset.image.{u_1, u_1} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_1} t,
          HPow.hPow.{0, 0, 0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.fullCubeCoefficient.{u_1} split B c b)) 2)
        (∑ q ∈ t, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (B c q.1 q.2)) 2)
```

## HeckeSkeleton.LowFrozenCube.fullCubeCoefficient_norm_le

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (t : Finset.{u_1} (Prod.{u_1, u_1} A A))
  (split : A → Prod.{u_1, u_1} A A),
  (∀ (q : Prod.{u_1, u_1} A A),
      Membership.mem.{u_1, u_1} t q → Eq.{u_1 + 1} (split (HeckeSkeleton.LowFrozenCube.cubeProduct.{u_1} q)) q) →
    ∀ (B : A → A → A → ℂ) (c : A) (R : ℝ),
      (∀ (q : Prod.{u_1, u_1} A A), Membership.mem.{u_1, u_1} t q → LE.le.{0} (Norm.norm.{0} (B c q.1 q.2)) R) →
        ∀ (b : A),
          Membership.mem.{u_1, u_1} (Finset.image.{u_1, u_1} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_1} t) b →
            LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.fullCubeCoefficient.{u_1} split B c b)) R
```

## HeckeSkeleton.LowFrozenCube.fullCube_collision_mask

```lean
∀ {ι : Type u_1} [DecidableEq.{u_1 + 1} ι] {s : Finset.{u_1} ι} {P x n : ι → ℕ},
  HeckeSkeleton.LowFrozenCube.AvoidsSupport.{u_1} s P →
    HeckeSkeleton.LowFrozenCube.SupportedOn.{u_1} s x →
      ((HeckeSkeleton.LowFrozenCube.DisjointValuations.{u_1} P fun p => HAdd.hAdd.{0, 0, 0} (x p) (n p)) ↔
        HeckeSkeleton.LowFrozenCube.DisjointValuations.{u_1} P n)
```

## HeckeSkeleton.LowFrozenCube.fullCube_decomposition

```lean
∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] (s : Finset.{u_1} ι) (v : ι → ℕ),
  Eq.{u_1 + 1} v fun p =>
    HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowFrozenCube.supportedPart.{u_1} s v p)
      (HeckeSkeleton.LowFrozenCube.awayPart.{u_1} s v p)
```

## HeckeSkeleton.LowFrozenCube.fullCube_product_decomposition

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A] [inst_1 : DecidableEq.{u_1 + 1} ι] (prime : ι → A)
  (primes frozen : Finset.{u_1} ι) (v : ι → ℕ),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime primes v)
    (HMul.hMul.{u_2, u_2, u_2}
      (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime primes
        (HeckeSkeleton.LowFrozenCube.supportedPart.{u_1} frozen v))
      (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime primes
        (HeckeSkeleton.LowFrozenCube.awayPart.{u_1} frozen v)))
```

## HeckeSkeleton.LowFrozenCube.fullCube_unique

```lean
∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] {s : Finset.{u_1} ι} {v x n : ι → ℕ},
  HeckeSkeleton.LowFrozenCube.SupportedOn.{u_1} s x →
    HeckeSkeleton.LowFrozenCube.AvoidsSupport.{u_1} s n →
      (∀ (p : ι), Eq.{1} (v p) (HAdd.hAdd.{0, 0, 0} (x p) (n p))) →
        Eq.{u_1 + 1} x (HeckeSkeleton.LowFrozenCube.supportedPart.{u_1} s v) ∧
          Eq.{u_1 + 1} n (HeckeSkeleton.LowFrozenCube.awayPart.{u_1} s v)
```

## HeckeSkeleton.LowFrozenCube.full_cube_symbol_mask

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (χ : A → MonoidHom.{u_1, 0} A ℂ) (Cop : A → A → Prop),
  (∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((χ a) b) 6) (ite.{1} (Cop a b) 1 0)) →
    ∀ (P x n : A), Cop P x → Eq.{1} (ite.{1} (Cop P (HMul.hMul.{u_1, u_1, u_1} x n)) 1 0) (ite.{1} (Cop P n) 1 0)
```

## HeckeSkeleton.LowFrozenCube.hybridScale_le

```lean
∀ (Z H v ell z : ℝ),
  LE.le.{0} 1 Z →
    LE.le.{0} (HeckeSkeleton.LowFrozenCube.hybridScale Z H v ell z)
      (HMul.hMul.{0, 0, 0} 6 (HPow.hPow.{0, 0, 0} Z (HeckeSkeleton.LowFrozenCube.hybridGrowthExponent H v ell z)))
```

## HeckeSkeleton.LowFrozenCube.hybridSeparatedRow_eq_normalizedRow

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (chi : A → MonoidHom.{u_1, 0} A ℂ) (cop : A → A → Prop),
  (∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((chi a) b) 6) (ite.{1} (cop a b) 1 0)) →
    ∀ (normI : A → ℝ) (a : A → ℂ) (beta : A → A → ℂ) (marks columns cubes : Finset.{u_1} A) (k : A),
      Eq.{1}
        (HeckeSkeleton.LowFrozenCube.hybridSeparatedRow.{u_1} chi cop (fun P => HDiv.hDiv.{0, 0, 0} (a P) ↑√(normI P))
          beta marks columns cubes k)
        (HeckeSkeleton.LowHybrid.hybridRow.{u_1} (fun i j => (chi i) j) cop normI a beta marks columns cubes k)
```

## HeckeSkeleton.LowFrozenCube.inverse_fourth_eq_square

```lean
∀ (z : ℂ),
  Eq.{1} z 0 ∨ Eq.{1} (HPow.hPow.{0, 0, 0} z 6) 1 →
    Eq.{1} (HPow.hPow.{0, 0, 0} (Inv.inv.{0} z) 4) (HPow.hPow.{0, 0, 0} z 2)
```

## HeckeSkeleton.LowFrozenCube.inverse_square_eq_fourth

```lean
∀ (z : ℂ),
  Eq.{1} z 0 ∨ Eq.{1} (HPow.hPow.{0, 0, 0} z 6) 1 →
    Eq.{1} (HPow.hPow.{0, 0, 0} (Inv.inv.{0} z) 2) (HPow.hPow.{0, 0, 0} z 4)
```

## HeckeSkeleton.LowFrozenCube.localPhaseDigit_add_cube

```lean
∀ (j e x : ℕ),
  LT.lt.{0} 0 e →
    Eq.{1} (HeckeSkeleton.LowFrozenCube.localPhaseDigit j (HAdd.hAdd.{0, 0, 0} e (HMul.hMul.{0, 0, 0} 3 x)))
      (HeckeSkeleton.LowFrozenCube.localPhaseDigit j e)
```

## HeckeSkeleton.LowFrozenCube.localPhaseDigit_frozen

```lean
∀ (j e : ℕ),
  HeckeSkeleton.LowFrozenCube.AdmissibleExponent e →
    Eq.{1} (HeckeSkeleton.LowFrozenCube.localPhaseDigit j e)
      (HeckeSkeleton.LowFrozenCube.localPhaseDigit j (HeckeSkeleton.LowFrozenCube.frozenMin e))
```

## HeckeSkeleton.LowFrozenCube.markCoefficient_frozen

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A] (χ : A → MonoidHom.{u_2, 0} A ℂ) (Cop : A → A → Prop),
  (∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((χ a) b) 6) (ite.{1} (Cop a b) 1 0)) →
    ∀ (F : Finset.{u_1} ι) (ψ : ι → A → ℂ) (j v : ι → ℕ),
      (∀ (p : ι), HeckeSkeleton.LowFrozenCube.AdmissibleExponent (v p)) →
        ∀ (a₀ : A → ℂ) (amin x P : A),
          Cop P x →
            Eq.{1}
              (HeckeSkeleton.LowFrozenCube.markCoefficient.{u_1, u_2} χ F ψ j v a₀
                (HMul.hMul.{u_2, u_2, u_2} amin (HPow.hPow.{u_2, 0, u_2} x 3)) P)
              (HeckeSkeleton.LowFrozenCube.markCoefficient.{u_1, u_2} χ F ψ j
                (HeckeSkeleton.LowFrozenCube.frozenBase.{u_1} v) a₀ amin P)
```

## HeckeSkeleton.LowFrozenCube.mark_column_phase

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (χ : A → MonoidHom.{u_1, 0} A ℂ),
  (∀ (a b : A), Eq.{1} ((χ a) b) ((χ b) a)) →
    ∀ (P c : A),
      Eq.{1} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} ((χ P) c) 2) (HPow.hPow.{0, 0, 0} ((χ c) P) 2))
        (HPow.hPow.{0, 0, 0} ((χ P) c) 4)
```

## HeckeSkeleton.LowFrozenCube.mergeCubePair_injective_on

```lean
∀ {ι : Type u_1} [DecidableEq.{u_1 + 1} ι] (s : Finset.{u_1} ι)
  (t : Finset.{u_1} (Prod.{u_1, u_1} (ι → ℕ) (ι → ℕ))),
  (∀ (q : Prod.{u_1, u_1} (ι → ℕ) (ι → ℕ)),
      Membership.mem.{u_1, u_1} t q →
        HeckeSkeleton.LowFrozenCube.SupportedOn.{u_1} s q.1 ∧ HeckeSkeleton.LowFrozenCube.AvoidsSupport.{u_1} s q.2) →
    Set.InjOn.{u_1, u_1} HeckeSkeleton.LowFrozenCube.mergeCubePair.{u_1} ↑t
```

## HeckeSkeleton.LowFrozenCube.negativeOrdinaryInteraction_frozen

```lean
∀ {ι : Type u_1} {A : Type u_2} [CommMonoid.{u_2} A] (F : Finset.{u_1} ι) (ψ : ι → A → ℂ) (j v : ι → ℕ),
  (∀ (p : ι), HeckeSkeleton.LowFrozenCube.AdmissibleExponent (v p)) →
    ∀ (a : A),
      Eq.{1} (HeckeSkeleton.LowFrozenCube.negativeOrdinaryInteraction.{u_1, u_2} F ψ j v a)
        (HeckeSkeleton.LowFrozenCube.negativeOrdinaryInteraction.{u_1, u_2} F ψ j
          (HeckeSkeleton.LowFrozenCube.frozenBase.{u_1} v) a)
```

## HeckeSkeleton.LowFrozenCube.normalizedCoefficient_le_ledger

```lean
∀ (C N cubeNorm chargeNorm Z v ell S B : ℝ),
  LT.lt.{0} 0 N →
    LT.lt.{0} 0 Z →
      LE.le.{0} (HPow.hPow.{0, 0, 0} C 2) (Inv.inv.{0} chargeNorm) →
        Eq.{1} N (HPow.hPow.{0, 0, 0} Z v) →
          Eq.{1} cubeNorm (HPow.hPow.{0, 0, 0} Z ell) →
            Eq.{1} chargeNorm (HPow.hPow.{0, 0, 0} Z (HAdd.hAdd.{0, 0, 0} S B)) →
              LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} C cubeNorm) 2) N)
                (HPow.hPow.{0, 0, 0} Z (HeckeSkeleton.LowFrozenCube.squaredCoefficientExponent v ell S B))
```

## HeckeSkeleton.LowFrozenCube.normalizedCubeCoefficient_norm_le

```lean
∀ (Qx C : ℝ) (Ω : ℂ),
  LT.lt.{0} 0 Qx →
    LE.le.{0} 0 C →
      LE.le.{0} (Norm.norm.{0} Ω) (HDiv.hDiv.{0, 0, 0} C Qx) →
        LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.normalizedCubeCoefficient Qx C Ω)) 1
```

## HeckeSkeleton.LowFrozenCube.normalizedCubeCoefficient_reassemble

```lean
∀ (Qx Qn C : ℝ) (Ω : ℂ),
  LT.lt.{0} 0 Qx →
    LT.lt.{0} 0 Qn →
      LE.le.{0} 0 C →
        LE.le.{0} (Norm.norm.{0} Ω) (HDiv.hDiv.{0, 0, 0} C Qx) →
          Eq.{1} (HDiv.hDiv.{0, 0, 0} Ω ↑Qn)
            (HDiv.hDiv.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (↑C) (HeckeSkeleton.LowFrozenCube.normalizedCubeCoefficient Qx C Ω))
              ↑(HMul.hMul.{0, 0, 0} Qx Qn))
```

## HeckeSkeleton.LowFrozenCube.overlap_mask_zero

```lean
∀ {ι : Type u_1} [DecidableEq.{u_1 + 1} ι] {u v : ι → ℕ} (z : ℂ),
  (∃ p, Ne.{1} (u p) 0 ∧ Ne.{1} (v p) 0) →
    Eq.{1} (ite.{1} (HeckeSkeleton.LowFrozenCube.DisjointValuations.{u_1} u v) z 0) 0
```

## HeckeSkeleton.LowFrozenCube.overlap_not_disjoint

```lean
∀ {ι : Type u_1} [DecidableEq.{u_1 + 1} ι] {u v : ι → ℕ},
  (∃ p, Ne.{1} (u p) 0 ∧ Ne.{1} (v p) 0) → ¬HeckeSkeleton.LowFrozenCube.DisjointValuations.{u_1} u v
```

## HeckeSkeleton.LowFrozenCube.positiveOrdinaryInteraction_frozen

```lean
∀ {ι : Type u_1} {A : Type u_2} [CommMonoid.{u_2} A] (F : Finset.{u_1} ι) (ψ : ι → A → ℂ) (j v : ι → ℕ),
  (∀ (p : ι), HeckeSkeleton.LowFrozenCube.AdmissibleExponent (v p)) →
    ∀ (a : A),
      Eq.{1} (HeckeSkeleton.LowFrozenCube.positiveOrdinaryInteraction.{u_1, u_2} F ψ j v a)
        (HeckeSkeleton.LowFrozenCube.positiveOrdinaryInteraction.{u_1, u_2} F ψ j
          (HeckeSkeleton.LowFrozenCube.frozenBase.{u_1} v) a)
```

## HeckeSkeleton.LowFrozenCube.powerfulCubeDigit_squarefree

```lean
∀ (e : ℕ), LE.le.{0} (HeckeSkeleton.LowFrozenCube.powerfulCubeDigit e) 1
```

## HeckeSkeleton.LowFrozenCube.powerfulExponent_decomposition

```lean
∀ (e : ℕ),
  Eq.{1} e 0 ∨ LE.le.{0} 2 e →
    Eq.{1} e
      (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (HeckeSkeleton.LowFrozenCube.powerfulSquareExp e))
        (HMul.hMul.{0, 0, 0} 3 (HeckeSkeleton.LowFrozenCube.powerfulCubeDigit e)))
```

## HeckeSkeleton.LowFrozenCube.powerfulExponent_unique

```lean
∀ {e a b : ℕ},
  LE.le.{0} b 1 →
    Eq.{1} e (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 a) (HMul.hMul.{0, 0, 0} 3 b)) →
      Eq.{1} a (HeckeSkeleton.LowFrozenCube.powerfulSquareExp e) ∧
        Eq.{1} b (HeckeSkeleton.LowFrozenCube.powerfulCubeDigit e)
```

## HeckeSkeleton.LowFrozenCube.powerful_count_le_sqrt_harmonic

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    ∀ (C : ℝ),
      LE.le.{0} 0 C →
        (∀ (a : A), LE.le.{0} 1 (q a)) →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q C →
            ∀ (K : ℝ),
              LE.le.{0} 1 K →
                ∀ (s : Finset.{u_2} A),
                  (∀ (a : A),
                      Membership.mem.{u_2, u_2} s a →
                        (∀ (p : ι),
                            Eq.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) 0 ∨
                              LE.le.{0} 2
                                ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p)) ∧
                          LE.le.{0} (normI a) K) →
                    LE.le.{0} (↑(Finset.card.{u_2} s))
                      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C √K) (HeckeSkeleton.LowHybrid.harmonicEnvelope C K))
```

## HeckeSkeleton.LowFrozenCube.powerful_count_small_power

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    ∀ (Ccount : ℝ),
      LT.lt.{0} 0 Ccount →
        (∀ (a : A), LE.le.{0} 1 (q a)) →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
            ∀ (eps : ℝ),
              LT.lt.{0} 0 eps →
                ∃ C,
                  LT.lt.{0} 0 C ∧
                    ∀ (K : ℝ),
                      LE.le.{0} 1 K →
                        ∀ (s : Finset.{u_2} A),
                          (∀ (a : A),
                              Membership.mem.{u_2, u_2} s a →
                                (∀ (p : ι),
                                    Eq.{1}
                                        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p)
                                        0 ∨
                                      LE.le.{0} 2
                                        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a)
                                          p)) ∧
                                  LE.le.{0} (normI a) K) →
                            LE.le.{0} (↑(Finset.card.{u_2} s))
                              (HMul.hMul.{0, 0, 0} C (HPow.hPow.{0, 0, 0} K (HAdd.hAdd.{0, 0, 0} (1 / 2) eps)))
```

## HeckeSkeleton.LowFrozenCube.powerful_pair_injOn

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_2} A),
  (∀ (a : A),
      Membership.mem.{u_2, u_2} s a →
        ∀ (p : ι),
          Eq.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) 0 ∨
            LE.le.{0} 2 ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p)) →
    Set.InjOn.{u_2, u_2}
      (fun a =>
        Prod.mk.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulSquareFactor.{u_1, u_2} coords a)
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulCubeFactor.{u_1, u_2} coords a))
      ↑s
```

## HeckeSkeleton.LowFrozenCube.powerful_pair_norm_le_sqrt

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LE.le.{0} 1 (normI a)) →
    ∀ (a : A) (K : ℝ),
      (∀ (p : ι),
          Eq.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) 0 ∨
            LE.le.{0} 2 ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p)) →
        LE.le.{0} (normI a) K →
          LE.le.{0}
            (HMul.hMul.{0, 0, 0}
              (normI (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulSquareFactor.{u_1, u_2} coords a))
              (normI (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulCubeFactor.{u_1, u_2} coords a)))
            √K
```

## HeckeSkeleton.LowFrozenCube.powerful_product_decomposition

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A] (prime : ι → A) (s : Finset.{u_1} ι) (v : ι → ℕ),
  (∀ (p : ι), Eq.{1} (v p) 0 ∨ LE.le.{0} 2 (v p)) →
    Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime s v)
      (HMul.hMul.{u_2, u_2, u_2}
        (HPow.hPow.{u_2, 0, u_2}
          (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime s fun p =>
            HeckeSkeleton.LowFrozenCube.powerfulSquareExp (v p))
          2)
        (HPow.hPow.{u_2, 0, u_2}
          (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime s fun p =>
            HeckeSkeleton.LowFrozenCube.powerfulCubeDigit (v p))
          3))
```

## HeckeSkeleton.LowFrozenCube.product_pair_count_le_harmonic

```lean
∀ {I : Type u_1} (q : I → ℕ) (normI : I → ℝ),
  (∀ (i : I), Eq.{1} (normI i) ↑(q i)) →
    ∀ (C : ℝ),
      LE.le.{0} 0 C →
        (∀ (i : I), LE.le.{0} 1 (q i)) →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_1} q C →
            ∀ (R : ℝ),
              LE.le.{0} 1 R →
                ∀ (pairs : Finset.{u_1} (Prod.{u_1, u_1} I I)),
                  (∀ (u : Prod.{u_1, u_1} I I),
                      Membership.mem.{u_1, u_1} pairs u → LE.le.{0} (HMul.hMul.{0, 0, 0} (normI u.1) (normI u.2)) R) →
                    LE.le.{0} (↑(Finset.card.{u_1} pairs))
                      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C R) (HeckeSkeleton.LowHybrid.harmonicEnvelope C R))
```

## HeckeSkeleton.LowFrozenCube.quadraticScale_le

```lean
∀ (Z H v ell : ℝ),
  LE.le.{0} 1 Z →
    LE.le.{0} (HeckeSkeleton.LowFrozenCube.quadraticScale Z H v ell)
      (HMul.hMul.{0, 0, 0} 2 (HPow.hPow.{0, 0, 0} Z (Max.max.{0} H (HAdd.hAdd.{0, 0, 0} v ell))))
```

## HeckeSkeleton.LowFrozenCube.reflected_exponent_identity

```lean
∀ (O H v ell S B z T : ℝ),
  Eq.{1}
    (HAdd.hAdd.{0, 0, 0}
      (HAdd.hAdd.{0, 0, 0}
        (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} O 2)
          (HeckeSkeleton.LowFrozenCube.squaredCoefficientExponent v ell S B))
        (HeckeSkeleton.LowFrozenCube.hybridGrowthExponent H v ell z))
      (HeckeSkeleton.LowFrozenCube.squaredKernelExponent T v ell))
    (HeckeSkeleton.LowFrozenCube.reflectedExponent O H v ell S B z T)
```

## HeckeSkeleton.LowFrozenCube.residualRowPart_avoids

```lean
∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] (s : Finset.{u_1} ι) (v : ι → ℕ),
  HeckeSkeleton.LowFrozenCube.AvoidsSupport.{u_1} s (HeckeSkeleton.LowFrozenCube.residualRowPart.{u_1} s v)
```

## HeckeSkeleton.LowFrozenCube.residualRowPart_squarefree

```lean
∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] (s : Finset.{u_1} ι) (v : ι → ℕ) (p : ι),
  LE.le.{0} (HeckeSkeleton.LowFrozenCube.residualRowPart.{u_1} s v p) 1
```

## HeckeSkeleton.LowFrozenCube.rowCoefficient_frozen

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A] (χ : A → MonoidHom.{u_2, 0} A ℂ) (F : Finset.{u_1} ι)
  (ψ : ι → A → ℂ) (j v : ι → ℕ),
  (∀ (p : ι), HeckeSkeleton.LowFrozenCube.AdmissibleExponent (v p)) →
    ∀ (ρ₀ : A → ℂ) (amin x d : A),
      Eq.{1}
        (HeckeSkeleton.LowFrozenCube.rowCoefficient.{u_1, u_2} χ F ψ j v ρ₀
          (HMul.hMul.{u_2, u_2, u_2} amin (HPow.hPow.{u_2, 0, u_2} x 3)) d)
        (HMul.hMul.{0, 0, 0}
          (HeckeSkeleton.LowFrozenCube.rowCoefficient.{u_1, u_2} χ F ψ j
            (HeckeSkeleton.LowFrozenCube.frozenBase.{u_1} v) ρ₀ amin d)
          (HPow.hPow.{0, 0, 0} ((χ d) x) 3))
```

## HeckeSkeleton.LowFrozenCube.row_column_phase

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (χ : A → MonoidHom.{u_1, 0} A ℂ),
  (∀ (a b : A), Eq.{1} ((χ a) b) ((χ b) a)) →
    ∀ (d c : A),
      Eq.{1} (HMul.hMul.{0, 0, 0} ((χ d) c) (HPow.hPow.{0, 0, 0} ((χ c) d) 2)) (HPow.hPow.{0, 0, 0} ((χ d) c) 3)
```

## HeckeSkeleton.LowFrozenCube.row_decomposition

```lean
∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] (s : Finset.{u_1} ι) (v : ι → ℕ),
  Eq.{u_1 + 1} v fun p =>
    HAdd.hAdd.{0, 0, 0}
      (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowFrozenCube.powerfulRowPart.{u_1} v p)
        (HeckeSkeleton.LowFrozenCube.supportedRowPart.{u_1} s v p))
      (HeckeSkeleton.LowFrozenCube.residualRowPart.{u_1} s v p)
```

## HeckeSkeleton.LowFrozenCube.row_mark_phase

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (χ : A → MonoidHom.{u_1, 0} A ℂ) (Cop : A → A → Prop),
  (∀ (a b : A), Eq.{1} ((χ a) b) ((χ b) a)) →
    (∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((χ a) b) 6) (ite.{1} (Cop a b) 1 0)) →
      ∀ (d P : A),
        Eq.{1} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} ((χ d) P) 4) (HPow.hPow.{0, 0, 0} ((χ P) d) 2))
          (ite.{1} (Cop d P) 1 0)
```

## HeckeSkeleton.LowFrozenCube.row_parts_pairwise_disjoint

```lean
∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] (s : Finset.{u_1} ι) (v : ι → ℕ),
  HeckeSkeleton.LowFrozenCube.DisjointValuations.{u_1} (HeckeSkeleton.LowFrozenCube.powerfulRowPart.{u_1} v)
      (HeckeSkeleton.LowFrozenCube.supportedRowPart.{u_1} s v) ∧
    HeckeSkeleton.LowFrozenCube.DisjointValuations.{u_1} (HeckeSkeleton.LowFrozenCube.powerfulRowPart.{u_1} v)
        (HeckeSkeleton.LowFrozenCube.residualRowPart.{u_1} s v) ∧
      HeckeSkeleton.LowFrozenCube.DisjointValuations.{u_1} (HeckeSkeleton.LowFrozenCube.supportedRowPart.{u_1} s v)
        (HeckeSkeleton.LowFrozenCube.residualRowPart.{u_1} s v)
```

## HeckeSkeleton.LowFrozenCube.row_product_decomposition

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A] [inst_1 : DecidableEq.{u_1 + 1} ι] (prime : ι → A)
  (primes frozen : Finset.{u_1} ι) (v : ι → ℕ),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime primes v)
    (HMul.hMul.{u_2, u_2, u_2}
      (HMul.hMul.{u_2, u_2, u_2}
        (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime primes
          (HeckeSkeleton.LowFrozenCube.powerfulRowPart.{u_1} v))
        (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime primes
          (HeckeSkeleton.LowFrozenCube.supportedRowPart.{u_1} frozen v)))
      (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime primes
        (HeckeSkeleton.LowFrozenCube.residualRowPart.{u_1} frozen v)))
```

## HeckeSkeleton.LowFrozenCube.sextic_symbol_zero_or_root

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (χ : A → MonoidHom.{u_1, 0} A ℂ) (Cop : A → A → Prop),
  (∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((χ a) b) 6) (ite.{1} (Cop a b) 1 0)) →
    ∀ (a b : A), Eq.{1} ((χ a) b) 0 ∨ Eq.{1} (HPow.hPow.{0, 0, 0} ((χ a) b) 6) 1
```

## HeckeSkeleton.LowFrozenCube.sum_fullCube_reindex

```lean
∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] {R : Type u_2} [inst_1 : AddCommMonoid.{u_2} R]
  (s : Finset.{u_1} ι) (t : Finset.{u_1} (Prod.{u_1, u_1} (ι → ℕ) (ι → ℕ))),
  (∀ (q : Prod.{u_1, u_1} (ι → ℕ) (ι → ℕ)),
      Membership.mem.{u_1, u_1} t q →
        HeckeSkeleton.LowFrozenCube.SupportedOn.{u_1} s q.1 ∧ HeckeSkeleton.LowFrozenCube.AvoidsSupport.{u_1} s q.2) →
    ∀ (G : (ι → ℕ) → (ι → ℕ) → R),
      Eq.{u_2 + 1} (∑ q ∈ t, G q.1 q.2)
        (∑ b ∈ Finset.image.{u_1, u_1} HeckeSkeleton.LowFrozenCube.mergeCubePair.{u_1} t,
          G (HeckeSkeleton.LowFrozenCube.supportedPart.{u_1} s b) (HeckeSkeleton.LowFrozenCube.awayPart.{u_1} s b))
```

## HeckeSkeleton.LowFrozenCube.sum_rows_eq_frozen_blocks

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) {R : Type u_3}
  [inst_1 : AddCommMonoid.{u_3} R] (support : Finset.{u_1} ι) (rows : Finset.{u_2} A) (F : A → R),
  Eq.{u_3 + 1} (∑ k ∈ rows, F k)
    (∑ pair ∈ HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2} coords support rows,
      ∑ k ∈ HeckeSkeleton.LowFrozenCube.PrimeCoordinates.rowBlock.{u_1, u_2} coords support pair.1 pair.2 rows, F k)
```

## HeckeSkeleton.LowFrozenCube.sum_rows_le_frozen_card_mul

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (support : Finset.{u_1} ι)
  (rows : Finset.{u_2} A) (F : A → ℝ) (E : ℝ),
  (∀ (pair : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2} coords support rows) pair →
        LE.le.{0}
          (∑ k ∈ HeckeSkeleton.LowFrozenCube.PrimeCoordinates.rowBlock.{u_1, u_2} coords support pair.1 pair.2 rows,
            F k)
          E) →
    LE.le.{0} (∑ k ∈ rows, F k)
      (HMul.hMul.{0, 0, 0}
        (↑(Finset.card.{u_2} (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2} coords support rows))) E)
```

## HeckeSkeleton.LowFrozenCube.sum_wholeIndexMark_row_overlap_zero

```lean
∀ {ι : Type u_1} [DecidableEq.{u_1 + 1} ι] {σ : Type u_2} {α : Type u_3} (slots : Finset.{u_2} σ) (prime : σ → ι)
  (row : ι → ℕ) (χ : (ι → ℕ) → ℂ),
  (∀ (v : ι → ℕ) (p : ι), Ne.{1} (row p) 0 → Ne.{1} (v p) 0 → Eq.{1} (χ v) 0) →
    ∀ (i : σ),
      Membership.mem.{u_2, u_2} slots i →
        Ne.{1} (row (prime i)) 0 →
          ∀ (t : Finset.{u_3} α) (index : α → ι → ℕ) (weight : α → ℂ),
            Eq.{1}
              (∑ a ∈ t,
                HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (weight a) (χ (index a)))
                  (HeckeSkeleton.LowFrozenCube.wholeIndexMark.{u_1, u_2} slots prime (index a)))
              0
```

## HeckeSkeleton.LowFrozenCube.supportedPart_supported

```lean
∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] (s : Finset.{u_1} ι) (v : ι → ℕ),
  HeckeSkeleton.LowFrozenCube.SupportedOn.{u_1} s (HeckeSkeleton.LowFrozenCube.supportedPart.{u_1} s v)
```

## HeckeSkeleton.LowFrozenCube.supportedRowPart_squarefree

```lean
∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] (s : Finset.{u_1} ι) (v : ι → ℕ) (p : ι),
  LE.le.{0} (HeckeSkeleton.LowFrozenCube.supportedRowPart.{u_1} s v p) 1
```

## HeckeSkeleton.LowFrozenCube.supportedRowPart_supported

```lean
∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] (s : Finset.{u_1} ι) (v : ι → ℕ),
  HeckeSkeleton.LowFrozenCube.SupportedOn.{u_1} s (HeckeSkeleton.LowFrozenCube.supportedRowPart.{u_1} s v)
```

## HeckeSkeleton.LowFrozenCube.supported_squarefree_count_le

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (support : Finset.{u_1} ι)
  (s : Finset.{u_2} A),
  (∀ (a : A),
      Membership.mem.{u_2, u_2} s a →
        HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords a ∧
          HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords support a) →
    LE.le.{0} (Finset.card.{u_2} s) (HPow.hPow.{0, 0, 0} 2 (Finset.card.{u_1} support))
```

## HeckeSkeleton.LowFrozenCube.supported_squarefree_count_small_power

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    ∀ (Ccount : ℝ),
      (∀ (a : A), LE.le.{0} 1 (q a)) →
        HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
          ∀ (eps : ℝ),
            LT.lt.{0} 0 eps →
              ∃ C,
                LT.lt.{0} 0 C ∧
                  ∀ (support : Finset.{u_1} ι) (s : Finset.{u_2} A),
                    (∀ (a : A),
                        Membership.mem.{u_2, u_2} s a →
                          HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords a ∧
                            HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords support a) →
                      LE.le.{0} (↑(Finset.card.{u_2} s))
                        (HMul.hMul.{0, 0, 0} C
                          (HPow.hPow.{0, 0, 0}
                            (normI (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2} coords support))
                            eps))
```

## HeckeSkeleton.LowFrozenCube.symbol_zpow_neg_four

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (χ : A → MonoidHom.{u_1, 0} A ℂ) (Cop : A → A → Prop),
  (∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((χ a) b) 6) (ite.{1} (Cop a b) 1 0)) →
    ∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((χ a) b) (-4)) (HPow.hPow.{0, 0, 0} ((χ a) b) 2)
```

## HeckeSkeleton.LowFrozenCube.symbol_zpow_neg_two

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (χ : A → MonoidHom.{u_1, 0} A ℂ) (Cop : A → A → Prop),
  (∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((χ a) b) 6) (ite.{1} (Cop a b) 1 0)) →
    ∀ (a b : A), Eq.{1} (HPow.hPow.{0, 0, 0} ((χ a) b) (-2)) (HPow.hPow.{0, 0, 0} ((χ a) b) 4)
```

## HeckeSkeleton.LowFrozenCube.terminalBound_le_half_margin

```lean
∀ (F M c d0 tau : ℝ),
  LE.le.{0} 0 M →
    LE.le.{0} 0 c →
      LE.le.{0} d0 (HDiv.hDiv.{0, 0, 0} c 100) →
        LE.le.{0} tau (HDiv.hDiv.{0, 0, 0} c 8) →
          LE.le.{0} (HeckeSkeleton.LowFrozenCube.terminalBound F M c d0 tau)
            (HSub.hSub.{0, 0, 0} F (HDiv.hDiv.{0, 0, 0} c 2))
```

## HeckeSkeleton.LowFrozenCube.terminal_column_equal_branch

```lean
∀ (F M N Nstar V bh d0 O H v ell S B z T Q z0 c tau : ℝ),
  Eq.{1} F (HAdd.hAdd.{0, 0, 0} N V) →
    Eq.{1} Nstar (HSub.hSub.{0, 0, 0} N (HMul.hMul.{0, 0, 0} 3 bh)) →
      LE.le.{0} 0 O →
        LE.le.{0} 0 ell →
          LE.le.{0} 0 Q →
            LE.le.{0} V d0 →
              LE.le.{0} bh d0 →
                LE.le.{0} z z0 →
                  LE.le.{0} c (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} F M) Q) z0) →
                    LE.le.{0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} T S) B)
                        (HAdd.hAdd.{0, 0, 0}
                          (HSub.hSub.{0, 0, 0}
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 M) O) Q) V)
                            Nstar)
                          (HMul.hMul.{0, 0, 0} 2 z)) →
                      LE.le.{0} (HAdd.hAdd.{0, 0, 0} v (HMul.hMul.{0, 0, 0} 3 ell)) (HAdd.hAdd.{0, 0, 0} T tau) →
                        LE.le.{0} H (HAdd.hAdd.{0, 0, 0} v ell) →
                          Eq.{1} (HeckeSkeleton.LowFrozenCube.cubicSaving v z) z →
                            LE.le.{0} (HeckeSkeleton.LowFrozenCube.reflectedExponent O H v ell S B z T)
                              (HAdd.hAdd.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0} (HSub.hSub.{0, 0, 0} F (HMul.hMul.{0, 0, 0} 2 c))
                                  (HMul.hMul.{0, 0, 0} 5 d0))
                                tau)
```

## HeckeSkeleton.LowFrozenCube.terminal_column_other_branch

```lean
∀ (F M N Nstar V bh d0 O H v ell S B z T Q z0 c tau : ℝ),
  Eq.{1} F (HAdd.hAdd.{0, 0, 0} N V) →
    Eq.{1} Nstar (HSub.hSub.{0, 0, 0} N (HMul.hMul.{0, 0, 0} 3 bh)) →
      LE.le.{0} 0 S →
        LE.le.{0} 0 B →
          LE.le.{0} 0 ell →
            LE.le.{0} V d0 →
              LE.le.{0} bh d0 →
                LE.le.{0} z z0 →
                  LE.le.{0} c (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} F M) Q) z0) →
                    LE.le.{0} c
                        (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} 4 F) (HMul.hMul.{0, 0, 0} 3 M))
                          (HMul.hMul.{0, 0, 0} 6 z0)) →
                      LE.le.{0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} T S) B)
                          (HAdd.hAdd.{0, 0, 0}
                            (HSub.hSub.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 M) O) Q) V)
                              Nstar)
                            (HMul.hMul.{0, 0, 0} 2 z)) →
                        LE.le.{0} (HAdd.hAdd.{0, 0, 0} v (HMul.hMul.{0, 0, 0} 3 ell)) (HAdd.hAdd.{0, 0, 0} T tau) →
                          LE.le.{0} H (HAdd.hAdd.{0, 0, 0} v ell) →
                            LE.le.{0} v (HMul.hMul.{0, 0, 0} 2 (HeckeSkeleton.LowFrozenCube.cubicSaving v z)) →
                              LE.le.{0} (HeckeSkeleton.LowFrozenCube.reflectedExponent O H v ell S B z T)
                                (HAdd.hAdd.{0, 0, 0}
                                  (HAdd.hAdd.{0, 0, 0}
                                    (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} F (HDiv.hDiv.{0, 0, 0} M 4))
                                      (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 3 c) 4))
                                    (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 5 d0) 2))
                                  (HDiv.hDiv.{0, 0, 0} tau 2))
```

## HeckeSkeleton.LowFrozenCube.terminal_ledger

```lean
∀ (F M N Nstar V bh d0 O H v ell S B z T Q z0 c tau : ℝ),
  Eq.{1} F (HAdd.hAdd.{0, 0, 0} N V) →
    Eq.{1} Nstar (HSub.hSub.{0, 0, 0} N (HMul.hMul.{0, 0, 0} 3 bh)) →
      LE.le.{0} 0 O →
        LE.le.{0} 0 S →
          LE.le.{0} 0 B →
            LE.le.{0} 0 ell →
              LE.le.{0} 0 v →
                LE.le.{0} 0 z →
                  LE.le.{0} 0 Q →
                    LE.le.{0} V d0 →
                      LE.le.{0} bh d0 →
                        LE.le.{0} z z0 →
                          LE.le.{0} H (HSub.hSub.{0, 0, 0} M O) →
                            LE.le.{0} c (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} F M) Q) z0) →
                              LE.le.{0} c
                                  (HSub.hSub.{0, 0, 0}
                                    (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} 4 F) (HMul.hMul.{0, 0, 0} 3 M))
                                    (HMul.hMul.{0, 0, 0} 6 z0)) →
                                LE.le.{0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} T S) B)
                                    (HAdd.hAdd.{0, 0, 0}
                                      (HSub.hSub.{0, 0, 0}
                                        (HAdd.hAdd.{0, 0, 0}
                                          (HAdd.hAdd.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 M) O) Q) V)
                                        Nstar)
                                      (HMul.hMul.{0, 0, 0} 2 z)) →
                                  LE.le.{0} (HAdd.hAdd.{0, 0, 0} v (HMul.hMul.{0, 0, 0} 3 ell))
                                      (HAdd.hAdd.{0, 0, 0} T tau) →
                                    LE.le.{0} (HeckeSkeleton.LowFrozenCube.reflectedExponent O H v ell S B z T)
                                      (HeckeSkeleton.LowFrozenCube.terminalBound F M c d0 tau)
```

## HeckeSkeleton.LowFrozenCube.terminal_row_branch

```lean
∀ (F M O H v ell S B z T Q z0 c : ℝ),
  LE.le.{0} 0 O →
    LE.le.{0} 0 S →
      LE.le.{0} 0 B →
        LE.le.{0} 0 ell →
          LE.le.{0} 0 v →
            LE.le.{0} 0 z →
              LE.le.{0} 0 Q →
                LE.le.{0} z z0 →
                  LE.le.{0} H (HSub.hSub.{0, 0, 0} M O) →
                    LE.le.{0} c (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} F M) Q) z0) →
                      LE.le.{0} (HAdd.hAdd.{0, 0, 0} v ell) H →
                        LE.le.{0} (HeckeSkeleton.LowFrozenCube.reflectedExponent O H v ell S B z T)
                          (HSub.hSub.{0, 0, 0} F c)
```

## HeckeSkeleton.LowFrozenCube.valuationProduct_add

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A] (prime : ι → A) (s : Finset.{u_1} ι) (v w : ι → ℕ),
  Eq.{u_2 + 1}
    (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime s fun p => HAdd.hAdd.{0, 0, 0} (v p) (w p))
    (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime s v)
      (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime s w))
```

## HeckeSkeleton.LowFrozenCube.valuationProduct_scale

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A] (prime : ι → A) (s : Finset.{u_1} ι) (v : ι → ℕ)
  (n : ℕ),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime s fun p => HMul.hMul.{0, 0, 0} n (v p))
    (HPow.hPow.{u_2, 0, u_2} (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime s v) n)
```

## HeckeSkeleton.LowFrozenCube.wholeIndexMark_row_overlap_zero

```lean
∀ {ι : Type u_1} [DecidableEq.{u_1 + 1} ι] {σ : Type u_2} (slots : Finset.{u_2} σ) (prime : σ → ι) (row : ι → ℕ)
  (χ : (ι → ℕ) → ℂ),
  (∀ (v : ι → ℕ) (p : ι), Ne.{1} (row p) 0 → Ne.{1} (v p) 0 → Eq.{1} (χ v) 0) →
    ∀ (i : σ),
      Membership.mem.{u_2, u_2} slots i →
        Ne.{1} (row (prime i)) 0 →
          ∀ (v : ι → ℕ),
            Eq.{1} (HMul.hMul.{0, 0, 0} (χ v) (HeckeSkeleton.LowFrozenCube.wholeIndexMark.{u_1, u_2} slots prime v)) 0
```

## HeckeSkeleton.LowFrozenCube.zpow_neg_four_eq_square

```lean
∀ (z : ℂ),
  Eq.{1} z 0 ∨ Eq.{1} (HPow.hPow.{0, 0, 0} z 6) 1 → Eq.{1} (HPow.hPow.{0, 0, 0} z (-4)) (HPow.hPow.{0, 0, 0} z 2)
```

## HeckeSkeleton.LowFrozenCube.zpow_neg_two_eq_fourth

```lean
∀ (z : ℂ),
  Eq.{1} z 0 ∨ Eq.{1} (HPow.hPow.{0, 0, 0} z 6) 1 → Eq.{1} (HPow.hPow.{0, 0, 0} z (-2)) (HPow.hPow.{0, 0, 0} z 4)
```

## HeckeSkeleton.LowHybrid.annular_normalized_mass_le

```lean
∀ {P : Type u_1} (columns : Finset.{u_1} P) (a : P → ℂ) (normP : P → ℝ) (L C : ℝ),
  LT.lt.{0} 0 L →
    (∀ (p : P), Membership.mem.{u_1, u_1} columns p → LE.le.{0} (Norm.norm.{0} (a p)) 1) →
      (∀ (p : P), Membership.mem.{u_1, u_1} columns p → LE.le.{0} L (normP p)) →
        LE.le.{0} (↑(Finset.card.{u_1} columns)) (HMul.hMul.{0, 0, 0} C (HMul.hMul.{0, 0, 0} 2 L)) →
          LE.le.{0} (∑ p ∈ columns, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (HDiv.hDiv.{0, 0, 0} (a p) ↑√(normP p))) 2)
            (HMul.hMul.{0, 0, 0} 2 C)
```

## HeckeSkeleton.LowHybrid.assembled_blocks_energy_of_two_sieves

```lean
∀ {K : Type u_1} {D : Type u_2} {M : Type u_3} {H : Type u_4} {C : Type u_5} {J : Type u_6} {P : Type u_7}
  [DecidableEq.{u_1 + 1} K] [inst : DecidableEq.{u_2 + 1} D] [DecidableEq.{u_3 + 1} M] [DecidableEq.{u_4 + 1} H]
  [DecidableEq.{u_5 + 1} C] [inst_4 : DecidableEq.{u_6 + 1} J] (rows : Finset.{u_1} K)
  (localBlocks : K → Finset.{u_2} D) (blocks : Finset.{u_2} D) (pairs : D → Finset.{max u_4 u_3} (Prod.{u_3, u_4} M H))
  (cset : D → M → Finset.{u_5} C) (hset : D → Finset.{u_4} H) (mc : D → Finset.{max u_5 u_3} (Prod.{u_3, u_5} M C))
  (jset : D → Finset.{u_6} J) (pset : D → Finset.{u_7} P) (q : D → K → Prod.{u_3, u_4} M H → ℂ)
  (phi : D → Prod.{u_3, u_5} M C → J) (chi : D → P → J → ℂ) (a : D → H → P → ℂ) (beta : D → C → M → H → ℂ)
  (mu : K → D → ℂ) (weight : D → ℂ) (Q S Cbound Fbound Ebound : D → ℝ) (Delta : ℝ),
  LE.le.{0} 0 Delta →
    (∀ (k : K),
        Membership.mem.{u_1, u_1} rows k →
          ∀ (d : D), Membership.mem.{u_2, u_2} (localBlocks k) d → LE.le.{0} (Norm.norm.{0} (mu k d)) 1) →
      (∀ (k : K), Membership.mem.{u_1, u_1} rows k → LE.le.{0} (↑(Finset.card.{u_2} (localBlocks k))) Delta) →
        (∀ (k : K),
            Membership.mem.{u_1, u_1} rows k →
              ∀ (d : D), Membership.mem.{u_2, u_2} (localBlocks k) d → Membership.mem.{u_2, u_2} blocks d) →
          (∀ (d : D), Membership.mem.{u_2, u_2} blocks d → LE.le.{0} 0 (Q d)) →
            (∀ (d : D), Membership.mem.{u_2, u_2} blocks d → LE.le.{0} 0 (S d)) →
              (∀ (d : D), Membership.mem.{u_2, u_2} blocks d → LE.le.{0} 0 (Cbound d)) →
                (∀ (d : D), Membership.mem.{u_2, u_2} blocks d → LE.le.{0} 0 (Fbound d)) →
                  (∀ (d : D),
                      Membership.mem.{u_2, u_2} blocks d →
                        ∀ (u : Prod.{u_3, u_4} M H),
                          Membership.mem.{max u_3 u_4, max u_3 u_4} (pairs d) u →
                            LE.le.{0} (↑(Finset.card.{u_5} (cset d u.1))) (Cbound d)) →
                    (∀ (d : D),
                        Membership.mem.{u_2, u_2} blocks d →
                          ∀ (u : Prod.{u_3, u_4} M H),
                            Membership.mem.{max u_3 u_4, max u_3 u_4} (pairs d) u →
                              ∀ (c : C),
                                Membership.mem.{u_5, u_5} (cset d u.1) c →
                                  LE.le.{0} (Norm.norm.{0} (beta d c u.1 u.2)) 1) →
                      (∀ (d : D),
                          Membership.mem.{u_2, u_2} blocks d →
                            ∀ (u : Prod.{u_3, u_4} M H),
                              Membership.mem.{max u_3 u_4, max u_3 u_4} (pairs d) u →
                                Membership.mem.{u_4, u_4} (hset d) u.2) →
                        (∀ (d : D),
                            Membership.mem.{u_2, u_2} blocks d →
                              ∀ (u : Prod.{u_3, u_4} M H),
                                Membership.mem.{max u_3 u_4, max u_3 u_4} (pairs d) u →
                                  ∀ (c : C),
                                    Membership.mem.{u_5, u_5} (cset d u.1) c →
                                      Membership.mem.{max u_5 u_3, max u_3 u_5} (mc d) (Prod.mk.{u_3, u_5} u.1 c)) →
                          (∀ (d : D),
                              Membership.mem.{u_2, u_2} blocks d →
                                ∀ (u : Prod.{u_3, u_5} M C),
                                  Membership.mem.{max u_3 u_5, max u_3 u_5} (mc d) u →
                                    Membership.mem.{u_6, u_6} (jset d) (phi d u)) →
                            (∀ (d : D),
                                Membership.mem.{u_2, u_2} blocks d →
                                  ∀ (j : J),
                                    Membership.mem.{u_6, u_6} (jset d) j →
                                      LE.le.{0} (↑(Finset.card.{max u_3 u_5} ({u ∈ mc d | Eq.{u_6 + 1} (phi d u) j})))
                                        (Fbound d)) →
                              (∀ (d : D),
                                  Membership.mem.{u_2, u_2} blocks d →
                                    ∀ (h : H),
                                      Membership.mem.{u_4, u_4} (hset d) h →
                                        LE.le.{0} (∑ p ∈ pset d, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a d h p)) 2)
                                          (Ebound d)) →
                                (∀ (d : D),
                                    Membership.mem.{u_2, u_2} blocks d →
                                      ∀ (f : Prod.{u_3, u_4} M H → ℂ),
                                        LE.le.{0}
                                          (∑ k ∈ rows with Membership.mem.{u_2, u_2} (localBlocks k) d,
                                            HPow.hPow.{0, 0, 0}
                                              (Norm.norm.{0} (∑ u ∈ pairs d, HMul.hMul.{0, 0, 0} (q d k u) (f u))) 2)
                                          (HMul.hMul.{0, 0, 0} (Q d)
                                            (∑ u ∈ pairs d, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (f u)) 2))) →
                                  (∀ (d : D),
                                      Membership.mem.{u_2, u_2} blocks d →
                                        ∀ (u : P → ℂ),
                                          LE.le.{0}
                                            (∑ j ∈ jset d,
                                              HPow.hPow.{0, 0, 0}
                                                (Norm.norm.{0} (∑ p ∈ pset d, HMul.hMul.{0, 0, 0} (u p) (chi d p j))) 2)
                                            (HMul.hMul.{0, 0, 0} (S d)
                                              (∑ p ∈ pset d, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (u p)) 2))) →
                                    LE.le.{0}
                                      (∑ k ∈ rows,
                                        HPow.hPow.{0, 0, 0}
                                          (Norm.norm.{0}
                                            (∑ d ∈ localBlocks k,
                                              HMul.hMul.{0, 0, 0} (mu k d)
                                                (HMul.hMul.{0, 0, 0} (weight d)
                                                  (∑ u ∈ pairs d,
                                                    HMul.hMul.{0, 0, 0} (q d k u)
                                                      (∑ c ∈ cset d u.1,
                                                        HMul.hMul.{0, 0, 0} (beta d c u.1 u.2)
                                                          (∑ p ∈ pset d,
                                                            HMul.hMul.{0, 0, 0} (a d u.2 p)
                                                              (chi d p (phi d (Prod.mk.{u_3, u_5} u.1 c)))))))))
                                          2)
                                      (HMul.hMul.{0, 0, 0} Delta
                                        (∑ d ∈ blocks,
                                          HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (weight d)) 2)
                                            (HMul.hMul.{0, 0, 0}
                                              (HMul.hMul.{0, 0, 0}
                                                (HMul.hMul.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Q d) (Cbound d))
                                                    ↑(Finset.card.{u_4} (hset d)))
                                                  (Fbound d))
                                                (S d))
                                              (Ebound d))))
```

## HeckeSkeleton.LowHybrid.betaSquaredMass_empty_columns

```lean
∀ {I : Type u_1} [CommMonoid.{u_1} I] (beta : I → I → ℂ) (cubes : Finset.{u_1} I),
  Eq.{1} (HeckeSkeleton.LowHybrid.betaSquaredMass.{u_1} beta EmptyCollection.emptyCollection.{u_1} cubes) 0
```

## HeckeSkeleton.LowHybrid.betaSquaredMass_empty_cubes

```lean
∀ {I : Type u_1} [CommMonoid.{u_1} I] (beta : I → I → ℂ) (columns : Finset.{u_1} I),
  Eq.{1} (HeckeSkeleton.LowHybrid.betaSquaredMass.{u_1} beta columns EmptyCollection.emptyCollection.{u_1}) 0
```

## HeckeSkeleton.LowHybrid.betaSquaredMass_nonneg

```lean
∀ {I : Type u_1} [CommMonoid.{u_1} I] (beta : I → I → ℂ) (columns cubes : Finset.{u_1} I),
  LE.le.{0} 0 (HeckeSkeleton.LowHybrid.betaSquaredMass.{u_1} beta columns cubes)
```

## HeckeSkeleton.LowHybrid.block_envelope

```lean
∀ (K N L D r C T G B A : ℝ),
  LE.le.{0} 1 K →
    LE.le.{0} 1 N →
      LE.le.{0} 1 L →
        LE.le.{0} 1 D →
          LE.le.{0} 1 r →
            LE.le.{0} 1 C →
              LE.le.{0} 1 T →
                LE.le.{0} 0 G →
                  LE.le.{0} 0 A →
                    Eq.{1} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} T 2) G) B →
                      LE.le.{0} (HeckeSkeleton.LowHybrid.completedBlock K N L D r C T G A)
                        (HMul.hMul.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0}
                            (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K (HMul.hMul.{0, 0, 0} N B))
                              (HDiv.hDiv.{0, 0, 0} B r))
                            (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} N L)
                              (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} N L) (2 / 3))))
                          A)
```

## HeckeSkeleton.LowHybrid.bounded_coefficient_sum_sq

```lean
∀ {I : Type u_1} (s : Finset.{u_1} I) (b f : I → ℂ),
  (∀ (i : I), Membership.mem.{u_1, u_1} s i → LE.le.{0} (Norm.norm.{0} (b i)) 1) →
    LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ i ∈ s, HMul.hMul.{0, 0, 0} (b i) (f i))) 2)
      (HMul.hMul.{0, 0, 0} (↑(Finset.card.{u_1} s)) (∑ i ∈ s, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (f i)) 2))
```

## HeckeSkeleton.LowHybrid.bounded_coefficient_sum_sq_of_card

```lean
∀ {I : Type u_1} (s : Finset.{u_1} I) (b f : I → ℂ) (D : ℝ),
  (∀ (i : I), Membership.mem.{u_1, u_1} s i → LE.le.{0} (Norm.norm.{0} (b i)) 1) →
    LE.le.{0} (↑(Finset.card.{u_1} s)) D →
      LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ i ∈ s, HMul.hMul.{0, 0, 0} (b i) (f i))) 2)
        (HMul.hMul.{0, 0, 0} D (∑ i ∈ s, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (f i)) 2))
```

## HeckeSkeleton.LowHybrid.column_fiber_sieve

```lean
∀ {K : Type u_1} {X : Type u_2} {Y : Type u_3} [inst : DecidableEq.{u_3 + 1} Y] (rows : Finset.{u_1} K)
  (source : Finset.{u_2} X) (target : Finset.{u_3} Y) (phi : X → Y) (q : K → Y → ℂ) (a : X → ℂ) (Q D : ℝ),
  LE.le.{0} 0 Q →
    (∀ (x : X), Membership.mem.{u_2, u_2} source x → Membership.mem.{u_3, u_3} target (phi x)) →
      (∀ (y : Y),
          Membership.mem.{u_3, u_3} target y →
            LE.le.{0} (↑(Finset.card.{u_2} ({x ∈ source | Eq.{u_3 + 1} (phi x) y}))) D) →
        (∀ (f : Y → ℂ),
            LE.le.{0}
              (∑ k ∈ rows, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ y ∈ target, HMul.hMul.{0, 0, 0} (q k y) (f y))) 2)
              (HMul.hMul.{0, 0, 0} Q (∑ y ∈ target, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (f y)) 2))) →
          LE.le.{0}
            (∑ k ∈ rows, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ x ∈ source, HMul.hMul.{0, 0, 0} (q k (phi x)) (a x))) 2)
            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} Q D) (∑ x ∈ source, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a x)) 2))
```

## HeckeSkeleton.LowHybrid.completed_cube_count

```lean
∀ (T G C r B : ℝ),
  LE.le.{0} 1 C →
    LE.le.{0} 1 r →
      Eq.{1} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} T 2) G) B →
        Eq.{1}
          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} T 2) (HDiv.hDiv.{0, 0, 0} C r))
            (HDiv.hDiv.{0, 0, 0} G C))
          (HDiv.hDiv.{0, 0, 0} B r)
```

## HeckeSkeleton.LowHybrid.completed_cubic_parameter_le

```lean
∀ (N L D r : ℝ),
  LE.le.{0} 1 N →
    LE.le.{0} 1 L →
      LE.le.{0} 1 D →
        LE.le.{0} 1 r →
          LE.le.{0}
            (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} N r) (HDiv.hDiv.{0, 0, 0} L D))
              (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} N L) (HMul.hMul.{0, 0, 0} r D)) (2 / 3)))
            (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} N L) (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} N L) (2 / 3)))
```

## HeckeSkeleton.LowHybrid.completed_cubic_parameter_nonneg

```lean
∀ (N L D r : ℝ),
  LE.le.{0} 1 N →
    LE.le.{0} 1 L →
      LE.le.{0} 1 D →
        LE.le.{0} 1 r →
          LE.le.{0} 0
            (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} N r) (HDiv.hDiv.{0, 0, 0} L D))
              (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} N L) (HMul.hMul.{0, 0, 0} r D)) (2 / 3)))
```

## HeckeSkeleton.LowHybrid.completed_quadratic_energy_bounded

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    (∀ (a : A), LE.le.{0} 1 (q a)) →
      ∀ (Ccount : ℝ),
        LT.lt.{0} 0 Ccount →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
            ∀ (symbol : A → A → ℂ),
              (∀ (a b c : A),
                  Eq.{1} (symbol a (HMul.hMul.{u_2, u_2, u_2} b c)) (HMul.hMul.{0, 0, 0} (symbol a b) (symbol a c))) →
                (∀ (a b : A),
                    Eq.{1} (HPow.hPow.{0, 0, 0} (symbol a b) 6)
                      (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
                  HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) symbol →
                    ∀ (eps : ℝ),
                      LT.lt.{0} 0 eps →
                        ∃ C0,
                          LT.lt.{0} 0 C0 ∧
                            ∀ (K N B : ℝ),
                              LE.le.{0} 1 K →
                                LE.le.{0} 1 N →
                                  LE.le.{0} 1 B →
                                    ∀ (rows columns cubes : Finset.{u_2} A) (beta : A → A → ℂ),
                                      (∀ (k : A),
                                          Membership.mem.{u_2, u_2} rows k →
                                            HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords k ∧
                                              LE.le.{0} (normI k) K) →
                                        (∀ (n : A),
                                            Membership.mem.{u_2, u_2} columns n →
                                              HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords n ∧
                                                LE.le.{0} (normI n) N) →
                                          (∀ (b : A), Membership.mem.{u_2, u_2} cubes b → LE.le.{0} (normI b) B) →
                                            (∀ (n : A),
                                                Membership.mem.{u_2, u_2} columns n →
                                                  ∀ (b : A),
                                                    Membership.mem.{u_2, u_2} cubes b →
                                                      LE.le.{0} (Norm.norm.{0} (beta n b)) 1) →
                                              LE.le.{0}
                                                (∑ k ∈ rows,
                                                  HPow.hPow.{0, 0, 0}
                                                    (Norm.norm.{0}
                                                      (∑ n ∈ columns,
                                                        ∑ b ∈ cubes,
                                                          HMul.hMul.{0, 0, 0} (beta n b)
                                                            (HPow.hPow.{0, 0, 0}
                                                              (symbol k (HMul.hMul.{u_2, u_2, u_2} n b)) 3)))
                                                    2)
                                                (HMul.hMul.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0}
                                                    (HMul.hMul.{0, 0, 0} C0
                                                      (HPow.hPow.{0, 0, 0}
                                                        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B) eps))
                                                    (HAdd.hAdd.{0, 0, 0} K (HMul.hMul.{0, 0, 0} N B)))
                                                  (HMul.hMul.{0, 0, 0} N B))
```

## HeckeSkeleton.LowHybrid.completed_quadratic_parameter_le

```lean
∀ (K N D r C T G B : ℝ),
  LE.le.{0} 1 K →
    LE.le.{0} 1 N →
      LE.le.{0} 1 D →
        LE.le.{0} 1 r →
          LE.le.{0} 1 C →
            LE.le.{0} 1 T →
              LE.le.{0} 0 G →
                Eq.{1} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} T 2) G) B →
                  LE.le.{0}
                    (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} K (HMul.hMul.{0, 0, 0} D r))
                      (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} N G) (HPow.hPow.{0, 0, 0} C 2)))
                    (HAdd.hAdd.{0, 0, 0} K (HMul.hMul.{0, 0, 0} N B))
```

## HeckeSkeleton.LowHybrid.complex_mask_norm_le_one

```lean
∀ (p : Prop), LE.le.{0} (Norm.norm.{0} (ite.{1} p 1 0)) 1
```

## HeckeSkeleton.LowHybrid.complex_support_mobius_sum

```lean
∀ {Prime : Type u_1} [inst : DecidableEq.{u_1 + 1} Prime] (support : Finset.{u_1} Prime),
  Eq.{1} (∑ d ∈ Finset.powerset.{u_1} support, HPow.hPow.{0, 0, 0} (-1) (Finset.card.{u_1} d))
    (ite.{1} (Eq.{u_1 + 1} support EmptyCollection.emptyCollection.{u_1}) 1 0)
```

## HeckeSkeleton.LowHybrid.cube_block_squarefree_le

```lean
∀ (T G B : ℝ),
  LE.le.{0} 1 T → LE.le.{0} 0 G → Eq.{1} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} T 2) G) B → LE.le.{0} G B
```

## HeckeSkeleton.LowHybrid.cube_support_weight_budget

```lean
∀ (wt wc wh r B : ℝ) (beta : ℂ),
  LT.lt.{0} 0 wt →
    LE.le.{0} 0 wc →
      LT.lt.{0} 0 wh →
        LT.lt.{0} 0 r →
          LE.le.{0} 0 B →
            LE.le.{0} (Norm.norm.{0} beta) 1 →
              (Ne.{1} beta 0 →
                  LE.le.{0}
                    (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} r wc) wh) (HPow.hPow.{0, 0, 0} wt 2))
                    B) →
                LE.le.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} wt wc) (HPow.hPow.{0, 0, 0} (Norm.norm.{0} beta) 2))
                  (HDiv.hDiv.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} B r) (HMul.hMul.{0, 0, 0} wt wh))
```

## HeckeSkeleton.LowHybrid.cube_support_weight_budget_mass

```lean
∀ (wt wc wh r B betaMass : ℝ) (beta : ℂ),
  LT.lt.{0} 0 wt →
    LE.le.{0} 0 wc →
      LT.lt.{0} 0 wh →
        LT.lt.{0} 0 r →
          LE.le.{0} 0 B →
            LE.le.{0} 0 betaMass →
              LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} beta) 2) betaMass →
                (Ne.{1} beta 0 →
                    LE.le.{0}
                      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} r wc) wh)
                        (HPow.hPow.{0, 0, 0} wt 2))
                      B) →
                  LE.le.{0}
                    (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} wt wc) (HPow.hPow.{0, 0, 0} (Norm.norm.{0} beta) 2))
                    (HDiv.hDiv.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} betaMass B) r)
                      (HMul.hMul.{0, 0, 0} wt wh))
```

## HeckeSkeleton.LowHybrid.divisorCountEnvelope_nonneg

```lean
∀ {I : Type u_1} (cutoff : ℝ → Finset.{u_1} I) (divisors : I → Finset.{u_1} I) (X : ℝ),
  LE.le.{0} 0 (HeckeSkeleton.LowHybrid.divisorCountEnvelope.{u_1} cutoff divisors X)
```

## HeckeSkeleton.LowHybrid.divisorCountEnvelope_subpower

```lean
∀ {I : Type u_1} (cutoff : ℝ → Finset.{u_1} I) (divisors : I → Finset.{u_1} I) (normI : I → ℝ),
  (∀ (i : I), LE.le.{0} 0 (normI i)) →
    (∀ (X : ℝ), LE.le.{0} 1 X → ∀ (i : I), Membership.mem.{u_1, u_1} (cutoff X) i → LE.le.{0} (normI i) X) →
      (∀ (eta : ℝ),
          LT.lt.{0} 0 eta →
            ∃ C,
              LT.lt.{0} 0 C ∧
                ∀ (i : I),
                  LE.le.{0} (↑(Finset.card.{u_1} (divisors i)))
                    (HMul.hMul.{0, 0, 0} C (HPow.hPow.{0, 0, 0} (normI i) eta))) →
        HeckeSkeleton.LowHybrid.SubpowerBound (HeckeSkeleton.LowHybrid.divisorCountEnvelope.{u_1} cutoff divisors)
```

## HeckeSkeleton.LowHybrid.divisorEnvelopeOfCounting_nonneg

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (q : A → ℕ) (hnorm : ∀ (a : A), Eq.{1} (normI a) ↑(q a)) (Ccount : ℝ)
  (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount) (X : ℝ),
  LE.le.{0} 0 (HeckeSkeleton.LowHybrid.divisorEnvelopeOfCounting.{u_1, u_2} coords normI q hnorm Ccount hcount X)
```

## HeckeSkeleton.LowHybrid.divisorEnvelopeOfCounting_subpower

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (q : A → ℕ) (hnorm : ∀ (a : A), Eq.{1} (normI a) ↑(q a)) (Ccount : ℝ)
  (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount),
  (∀ (a : A), LE.le.{0} 1 (q a)) →
    HeckeSkeleton.LowHybrid.SubpowerBound
      (HeckeSkeleton.LowHybrid.divisorEnvelopeOfCounting.{u_1, u_2} coords normI q hnorm Ccount hcount)
```

## HeckeSkeleton.LowHybrid.divisor_column_normalization

```lean
∀ (D Q : ℝ),
  LE.le.{0} 0 D →
    LE.le.{0} 0 Q →
      ∀ (a : ℂ),
        Eq.{1} (HDiv.hDiv.{0, 0, 0} a ↑√(HMul.hMul.{0, 0, 0} D Q))
          (HMul.hMul.{0, 0, 0} (Inv.inv.{0} ↑√D) (HDiv.hDiv.{0, 0, 0} a ↑√Q))
```

## HeckeSkeleton.LowHybrid.divisor_count_le_envelope

```lean
∀ {I : Type u_1} (cutoff : ℝ → Finset.{u_1} I) (divisors : I → Finset.{u_1} I) (X : ℝ) (i : I),
  Membership.mem.{u_1, u_1} (cutoff X) i →
    LE.le.{0} (↑(Finset.card.{u_1} (divisors i))) (HeckeSkeleton.LowHybrid.divisorCountEnvelope.{u_1} cutoff divisors X)
```

## HeckeSkeleton.LowHybrid.divisor_count_le_envelopeOfCounting

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (q : A → ℕ) (hnorm : ∀ (a : A), Eq.{1} (normI a) ↑(q a)) (Ccount : ℝ)
  (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount) (X : ℝ) (a : A),
  LE.le.{0} (normI a) X →
    LE.le.{0} (↑(Finset.card.{u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords a)))
      (HeckeSkeleton.LowHybrid.divisorEnvelopeOfCounting.{u_1, u_2} coords normI q hnorm Ccount hcount X)
```

## HeckeSkeleton.LowHybrid.divisor_envelope_subpower_from_prime_norms

```lean
∀ {I : Type u_1} {P : Type u_2} (support : I → Finset.{u_2} P) (divisors : I → Finset.{u_1} I) (primeNorm : P → ℝ)
  (normI : I → ℝ) (cutoff : ℝ → Finset.{u_1} I),
  (∀ (p : P), LE.le.{0} 1 (primeNorm p)) →
    (∀ (X : ℝ), Set.Finite.{u_2} (Set.ofPred.{u_2} fun p => LE.le.{0} (primeNorm p) X)) →
      (∀ (i : I),
          LE.le.{0} (↑(Finset.card.{u_1} (divisors i))) (HPow.hPow.{0, 0, 0} 2 (Finset.card.{u_2} (support i)))) →
        (∀ (i : I), LE.le.{0} (∏ p ∈ support i, primeNorm p) (normI i)) →
          (∀ (X : ℝ), LE.le.{0} 1 X → ∀ (i : I), Membership.mem.{u_1, u_1} (cutoff X) i → LE.le.{0} (normI i) X) →
            HeckeSkeleton.LowHybrid.SubpowerBound (HeckeSkeleton.LowHybrid.divisorCountEnvelope.{u_1} cutoff divisors)
```

## HeckeSkeleton.LowHybrid.divisor_weight_sq

```lean
∀ (D : ℝ),
  LE.le.{0} 0 D → Eq.{1} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (Inv.inv.{0} ↑√D)) 2) (HDiv.hDiv.{0, 0, 0} 1 D)
```

## HeckeSkeleton.LowHybrid.factor_norm_le_product

```lean
∀ {I : Type u_1} [inst : Monoid.{u_1} I] (normI : I → ℝ),
  (∀ (i : I), LE.le.{0} 1 (normI i)) →
    (∀ (i j : I), Eq.{1} (normI (HMul.hMul.{u_1, u_1, u_1} i j)) (HMul.hMul.{0, 0, 0} (normI i) (normI j))) →
      ∀ (i j : I), LE.le.{0} (normI j) (normI (HMul.hMul.{u_1, u_1, u_1} i j))
```

## HeckeSkeleton.LowHybrid.factorized_column_mass_le

```lean
∀ {D : Type u_1} {Q : Type u_2} {P : Type u_3} [DecidableEq.{u_1 + 1} D] [DecidableEq.{u_2 + 1} Q]
  [inst : DecidableEq.{u_3 + 1} P] (blocks : Finset.{u_1} D) (columns : D → Finset.{u_2} Q) (target : Finset.{u_3} P)
  (product : D → Q → P) (normD : D → ℝ) (normQ : Q → ℝ) (normP : P → ℝ) (a : P → ℂ) (multiplicity : ℝ),
  (∀ (d : D), Membership.mem.{u_1, u_1} blocks d → LT.lt.{0} 0 (normD d)) →
    (∀ (d : D),
        Membership.mem.{u_1, u_1} blocks d →
          ∀ (q : Q), Membership.mem.{u_2, u_2} (columns d) q → LT.lt.{0} 0 (normQ q)) →
      (∀ (p : P), Membership.mem.{u_3, u_3} target p → LT.lt.{0} 0 (normP p)) →
        (∀ (d : D),
            Membership.mem.{u_1, u_1} blocks d →
              ∀ (q : Q), Membership.mem.{u_2, u_2} (columns d) q → Membership.mem.{u_3, u_3} target (product d q)) →
          (∀ (d : D),
              Membership.mem.{u_1, u_1} blocks d →
                ∀ (q : Q),
                  Membership.mem.{u_2, u_2} (columns d) q →
                    Eq.{1} (normP (product d q)) (HMul.hMul.{0, 0, 0} (normD d) (normQ q))) →
            (∀ (p : P),
                Membership.mem.{u_3, u_3} target p →
                  LE.le.{0}
                    (↑(Finset.card.{max u_1 u_2}
                        ({dq ∈ Finset.sigma.{u_1, u_2} blocks columns |
                          Eq.{u_3 + 1} (product (Sigma.fst.{u_1, u_2} dq) (Sigma.snd.{u_1, u_2} dq)) p})))
                    multiplicity) →
              LE.le.{0}
                (∑ d ∈ blocks,
                  HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} 1 (normD d))
                    (∑ q ∈ columns d,
                      HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a (product d q))) 2) (normQ q)))
                (HMul.hMul.{0, 0, 0} multiplicity
                  (∑ p ∈ target, HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a p)) 2) (normP p)))
```

## HeckeSkeleton.LowHybrid.finite_complex_sum_mul_sq_le

```lean
∀ {I : Type u_1} (s : Finset.{u_1} I) (x y : I → ℂ),
  LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ i ∈ s, HMul.hMul.{0, 0, 0} (x i) (y i))) 2)
    (HMul.hMul.{0, 0, 0} (∑ i ∈ s, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (x i)) 2)
      (∑ i ∈ s, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (y i)) 2))
```

## HeckeSkeleton.LowHybrid.finite_nat_norms_of_linear_counting

```lean
∀ {I : Type u_1} (q : I → ℕ) (C : ℝ),
  HeckeSkeleton.LowHybrid.LinearNormCounting.{u_1} q C →
    ∀ (N : ℕ), Set.Finite.{u_1} (Set.ofPred.{u_1} fun i => LE.le.{0} (q i) N)
```

## HeckeSkeleton.LowHybrid.finite_operator_bound_transpose

```lean
∀ {I : Type u_1} {J : Type u_2} (rows : Finset.{u_1} I) (columns : Finset.{u_2} J) (matrix : I → J → ℂ) (C : ℝ),
  LE.le.{0} 0 C →
    (∀ (z : J → ℂ),
        LE.le.{0}
          (∑ i ∈ rows, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ j ∈ columns, HMul.hMul.{0, 0, 0} (matrix i j) (z j))) 2)
          (HMul.hMul.{0, 0, 0} C (∑ j ∈ columns, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (z j)) 2))) →
      ∀ (x : I → ℂ),
        LE.le.{0}
          (∑ j ∈ columns, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ i ∈ rows, HMul.hMul.{0, 0, 0} (x i) (matrix i j))) 2)
          (HMul.hMul.{0, 0, 0} C (∑ i ∈ rows, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (x i)) 2))
```

## HeckeSkeleton.LowHybrid.finite_real_norms_of_linear_counting

```lean
∀ {I : Type u_1} (q : I → ℕ) (normI : I → ℝ),
  (∀ (i : I), Eq.{1} (normI i) ↑(q i)) →
    ∀ (C : ℝ),
      HeckeSkeleton.LowHybrid.LinearNormCounting.{u_1} q C →
        ∀ (X : ℝ), Set.Finite.{u_1} (Set.ofPred.{u_1} fun i => LE.le.{0} (normI i) X)
```

## HeckeSkeleton.LowHybrid.fixed_base_support_power_subpower

```lean
∀ {P : Type u_1} (q : P → ℝ),
  (∀ (p : P), LE.le.{0} 1 (q p)) →
    (∀ (X : ℝ), Set.Finite.{u_1} (Set.ofPred.{u_1} fun p => LE.le.{0} (q p) X)) →
      ∀ (base : ℝ),
        LE.le.{0} 0 base →
          ∀ (eta : ℝ),
            LT.lt.{0} 0 eta →
              ∃ C,
                LT.lt.{0} 0 C ∧
                  ∀ (s : Finset.{u_1} P),
                    LE.le.{0} (HPow.hPow.{0, 0, 0} base (Finset.card.{u_1} s))
                      (HMul.hMul.{0, 0, 0} C (HPow.hPow.{0, 0, 0} (∏ p ∈ s, q p) eta))
```

## HeckeSkeleton.LowHybrid.fixed_base_support_power_subpower_ge_one

```lean
∀ {P : Type u_1} (q : P → ℝ),
  (∀ (p : P), LE.le.{0} 1 (q p)) →
    (∀ (X : ℝ), Set.Finite.{u_1} (Set.ofPred.{u_1} fun p => LE.le.{0} (q p) X)) →
      ∀ (base : ℝ),
        LE.le.{0} 1 base →
          ∀ (eta : ℝ),
            LT.lt.{0} 0 eta →
              ∃ C,
                LT.lt.{0} 0 C ∧
                  ∀ (s : Finset.{u_1} P),
                    LE.le.{0} (HPow.hPow.{0, 0, 0} base (Finset.card.{u_1} s))
                      (HMul.hMul.{0, 0, 0} C (HPow.hPow.{0, 0, 0} (∏ p ∈ s, q p) eta))
```

## HeckeSkeleton.LowHybrid.fixed_block_energy_of_two_sieves

```lean
∀ {K : Type u_1} {M : Type u_2} {H : Type u_3} {C : Type u_4} {J : Type u_5} {P : Type u_6}
  [DecidableEq.{u_2 + 1} M] [DecidableEq.{u_3 + 1} H] [DecidableEq.{u_4 + 1} C] [inst : DecidableEq.{u_5 + 1} J]
  (rows : Finset.{u_1} K) (pairs : Finset.{max u_3 u_2} (Prod.{u_2, u_3} M H)) (cset : M → Finset.{u_4} C)
  (hset : Finset.{u_3} H) (mc : Finset.{max u_4 u_2} (Prod.{u_2, u_4} M C)) (jset : Finset.{u_5} J)
  (pset : Finset.{u_6} P) (q : K → Prod.{u_2, u_3} M H → ℂ) (phi : Prod.{u_2, u_4} M C → J) (chi : P → J → ℂ)
  (a : H → P → ℂ) (beta : C → M → H → ℂ) (Q S Cbound D Ebound : ℝ),
  LE.le.{0} 0 Q →
    LE.le.{0} 0 S →
      LE.le.{0} 0 Cbound →
        LE.le.{0} 0 D →
          (∀ (p : Prod.{u_2, u_3} M H),
              Membership.mem.{max u_2 u_3, max u_2 u_3} pairs p → LE.le.{0} (↑(Finset.card.{u_4} (cset p.1))) Cbound) →
            (∀ (p : Prod.{u_2, u_3} M H),
                Membership.mem.{max u_2 u_3, max u_2 u_3} pairs p →
                  ∀ (c : C), Membership.mem.{u_4, u_4} (cset p.1) c → LE.le.{0} (Norm.norm.{0} (beta c p.1 p.2)) 1) →
              (∀ (p : Prod.{u_2, u_3} M H),
                  Membership.mem.{max u_2 u_3, max u_2 u_3} pairs p → Membership.mem.{u_3, u_3} hset p.2) →
                (∀ (p : Prod.{u_2, u_3} M H),
                    Membership.mem.{max u_2 u_3, max u_2 u_3} pairs p →
                      ∀ (c : C),
                        Membership.mem.{u_4, u_4} (cset p.1) c →
                          Membership.mem.{max u_4 u_2, max u_2 u_4} mc (Prod.mk.{u_2, u_4} p.1 c)) →
                  (∀ (u : Prod.{u_2, u_4} M C),
                      Membership.mem.{max u_2 u_4, max u_2 u_4} mc u → Membership.mem.{u_5, u_5} jset (phi u)) →
                    (∀ (j : J),
                        Membership.mem.{u_5, u_5} jset j →
                          LE.le.{0} (↑(Finset.card.{max u_2 u_4} ({u ∈ mc | Eq.{u_5 + 1} (phi u) j}))) D) →
                      (∀ (h : H),
                          Membership.mem.{u_3, u_3} hset h →
                            LE.le.{0} (∑ p ∈ pset, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a h p)) 2) Ebound) →
                        (∀ (f : Prod.{u_2, u_3} M H → ℂ),
                            LE.le.{0}
                              (∑ k ∈ rows,
                                HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ u ∈ pairs, HMul.hMul.{0, 0, 0} (q k u) (f u))) 2)
                              (HMul.hMul.{0, 0, 0} Q (∑ u ∈ pairs, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (f u)) 2))) →
                          (∀ (u : P → ℂ),
                              LE.le.{0}
                                (∑ j ∈ jset,
                                  HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ p ∈ pset, HMul.hMul.{0, 0, 0} (u p) (chi p j)))
                                    2)
                                (HMul.hMul.{0, 0, 0} S (∑ p ∈ pset, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (u p)) 2))) →
                            LE.le.{0}
                              (∑ k ∈ rows,
                                HPow.hPow.{0, 0, 0}
                                  (Norm.norm.{0}
                                    (∑ u ∈ pairs,
                                      HMul.hMul.{0, 0, 0} (q k u)
                                        (∑ c ∈ cset u.1,
                                          HMul.hMul.{0, 0, 0} (beta c u.1 u.2)
                                            (∑ p ∈ pset,
                                              HMul.hMul.{0, 0, 0} (a u.2 p) (chi p (phi (Prod.mk.{u_2, u_4} u.1 c)))))))
                                  2)
                              (HMul.hMul.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} Q Cbound) ↑(Finset.card.{u_3} hset)) D)
                                  S)
                                Ebound)
```

## HeckeSkeleton.LowHybrid.fixed_block_scalar_ledger

```lean
∀ (T G C r B Q S A : ℝ),
  Ne.{1} C 0 →
    Ne.{1} r 0 →
      Eq.{1} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} T 2) G) B →
        Eq.{1}
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0}
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} T 2) Q) (HDiv.hDiv.{0, 0, 0} C r))
                (HDiv.hDiv.{0, 0, 0} G C))
              S)
            A)
          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} Q (HDiv.hDiv.{0, 0, 0} B r)) S) A)
```

## HeckeSkeleton.LowHybrid.harmonicEnvelope_nonneg

```lean
∀ (C : ℝ), LE.le.{0} 0 C → ∀ (X : ℝ), LE.le.{0} 1 X → LE.le.{0} 0 (HeckeSkeleton.LowHybrid.harmonicEnvelope C X)
```

## HeckeSkeleton.LowHybrid.harmonicEnvelope_subpower

```lean
∀ (C : ℝ), LT.lt.{0} 0 C → HeckeSkeleton.LowHybrid.SubpowerBound (HeckeSkeleton.LowHybrid.harmonicEnvelope C)
```

## HeckeSkeleton.LowHybrid.harmonicPartial_le_log

```lean
∀ (N : ℕ), LE.le.{0} (HeckeSkeleton.LowHybrid.harmonicPartial N) (HAdd.hAdd.{0, 0, 0} 1 (Real.log ↑N))
```

## HeckeSkeleton.LowHybrid.harmonic_cutoff_subpower_of_linear_counting

```lean
∀ {I : Type u_1} (q : I → ℕ) (C : ℝ),
  LT.lt.{0} 0 C →
    (∀ (i : I), LE.le.{0} 1 (q i)) →
      HeckeSkeleton.LowHybrid.LinearNormCounting.{u_1} q C →
        ∀ (cutoff : ℝ → Finset.{u_1} I),
          (∀ (X : ℝ), LE.le.{0} 1 X → ∀ (i : I), Membership.mem.{u_1, u_1} (cutoff X) i → LE.le.{0} (↑(q i)) X) →
            HeckeSkeleton.LowHybrid.SubpowerBound fun X => ∑ i ∈ cutoff X, HDiv.hDiv.{0, 0, 0} 1 ↑(q i)
```

## HeckeSkeleton.LowHybrid.hybridEnergy_beta_bound_of_unit

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ) (a : I → ℂ)
  (beta : I → I → ℂ) (rows marks columns cubes : Finset.{u_1} I) (U R : ℝ),
  LE.le.{0} 0 U →
    (∀ (n : I),
        Membership.mem.{u_1, u_1} columns n →
          ∀ (b : I), Membership.mem.{u_1, u_1} cubes b → LE.le.{0} (Norm.norm.{0} (beta n b)) U) →
      (∀ (gamma : I → I → ℂ),
          (∀ (n : I),
              Membership.mem.{u_1, u_1} columns n →
                ∀ (b : I), Membership.mem.{u_1, u_1} cubes b → LE.le.{0} (Norm.norm.{0} (gamma n b)) 1) →
            LE.le.{0} (HeckeSkeleton.LowHybrid.hybridEnergy.{u_1} symbol cop normI a gamma rows marks columns cubes)
              R) →
        LE.le.{0} (HeckeSkeleton.LowHybrid.hybridEnergy.{u_1} symbol cop normI a beta rows marks columns cubes)
          (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} U 2) R)
```

## HeckeSkeleton.LowHybrid.hybridEnergy_beta_mass_of_unit

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ) (a : I → ℂ)
  (beta : I → I → ℂ) (rows marks columns cubes : Finset.{u_1} I) (R : ℝ),
  (∀ (gamma : I → I → ℂ),
      (∀ (n : I),
          Membership.mem.{u_1, u_1} columns n →
            ∀ (b : I), Membership.mem.{u_1, u_1} cubes b → LE.le.{0} (Norm.norm.{0} (gamma n b)) 1) →
        LE.le.{0} (HeckeSkeleton.LowHybrid.hybridEnergy.{u_1} symbol cop normI a gamma rows marks columns cubes) R) →
    LE.le.{0} (HeckeSkeleton.LowHybrid.hybridEnergy.{u_1} symbol cop normI a beta rows marks columns cubes)
      (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.betaSquaredMass.{u_1} beta columns cubes) R)
```

## HeckeSkeleton.LowHybrid.hybridEnergy_beta_mul

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ) (a : I → ℂ)
  (beta : I → I → ℂ) (z : ℂ) (rows marks columns cubes : Finset.{u_1} I),
  Eq.{1}
    (HeckeSkeleton.LowHybrid.hybridEnergy.{u_1} symbol cop normI a (fun n b => HMul.hMul.{0, 0, 0} z (beta n b)) rows
      marks columns cubes)
    (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} z) 2)
      (HeckeSkeleton.LowHybrid.hybridEnergy.{u_1} symbol cop normI a beta rows marks columns cubes))
```

## HeckeSkeleton.LowHybrid.hybridEnergy_beta_squared_bound_of_unit

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ) (a : I → ℂ)
  (beta : I → I → ℂ) (rows marks columns cubes : Finset.{u_1} I) (V R : ℝ),
  LE.le.{0} 0 V →
    (∀ (n : I),
        Membership.mem.{u_1, u_1} columns n →
          ∀ (b : I),
            Membership.mem.{u_1, u_1} cubes b → LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (beta n b)) 2) V) →
      (∀ (gamma : I → I → ℂ),
          (∀ (n : I),
              Membership.mem.{u_1, u_1} columns n →
                ∀ (b : I), Membership.mem.{u_1, u_1} cubes b → LE.le.{0} (Norm.norm.{0} (gamma n b)) 1) →
            LE.le.{0} (HeckeSkeleton.LowHybrid.hybridEnergy.{u_1} symbol cop normI a gamma rows marks columns cubes)
              R) →
        LE.le.{0} (HeckeSkeleton.LowHybrid.hybridEnergy.{u_1} symbol cop normI a beta rows marks columns cubes)
          (HMul.hMul.{0, 0, 0} V R)
```

## HeckeSkeleton.LowHybrid.hybridEnergy_eq_zero_of_beta_zero

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ) (a : I → ℂ)
  (beta : I → I → ℂ) (rows marks columns cubes : Finset.{u_1} I),
  (∀ (n : I),
      Membership.mem.{u_1, u_1} columns n → ∀ (b : I), Membership.mem.{u_1, u_1} cubes b → Eq.{1} (beta n b) 0) →
    Eq.{1} (HeckeSkeleton.LowHybrid.hybridEnergy.{u_1} symbol cop normI a beta rows marks columns cubes) 0
```

## HeckeSkeleton.LowHybrid.hybridEnergy_nonneg

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ) (a : I → ℂ)
  (beta : I → I → ℂ) (rows marks columns cubes : Finset.{u_1} I),
  LE.le.{0} 0 (HeckeSkeleton.LowHybrid.hybridEnergy.{u_1} symbol cop normI a beta rows marks columns cubes)
```

## HeckeSkeleton.LowHybrid.hybridRow_beta_congr

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ) (a : I → ℂ)
  (beta gamma : I → I → ℂ) (marks columns cubes : Finset.{u_1} I) (k : I),
  (∀ (n : I),
      Membership.mem.{u_1, u_1} columns n →
        ∀ (b : I), Membership.mem.{u_1, u_1} cubes b → Eq.{1} (beta n b) (gamma n b)) →
    Eq.{1} (HeckeSkeleton.LowHybrid.hybridRow.{u_1} symbol cop normI a beta marks columns cubes k)
      (HeckeSkeleton.LowHybrid.hybridRow.{u_1} symbol cop normI a gamma marks columns cubes k)
```

## HeckeSkeleton.LowHybrid.hybridRow_beta_mul

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ) (a : I → ℂ)
  (beta : I → I → ℂ) (z : ℂ) (marks columns cubes : Finset.{u_1} I) (k : I),
  Eq.{1}
    (HeckeSkeleton.LowHybrid.hybridRow.{u_1} symbol cop normI a (fun n b => HMul.hMul.{0, 0, 0} z (beta n b)) marks
      columns cubes k)
    (HMul.hMul.{0, 0, 0} z (HeckeSkeleton.LowHybrid.hybridRow.{u_1} symbol cop normI a beta marks columns cubes k))
```

## HeckeSkeleton.LowHybrid.hybrid_arithmetic_loss_le

```lean
∀ (divisor harmonic : ℝ → ℝ) (CD CH eta K N B L : ℝ),
  LE.le.{0} 0 CD →
    LE.le.{0} 0 CH →
      LE.le.{0} 0 eta →
        LE.le.{0} 1 K →
          LE.le.{0} 1 N →
            LE.le.{0} 1 B →
              LE.le.{0} 1 L →
                (∀ (X : ℝ), LE.le.{0} 1 X → LE.le.{0} 0 (divisor X)) →
                  (∀ (X : ℝ), LE.le.{0} 1 X → LE.le.{0} 0 (harmonic X)) →
                    (∀ (X : ℝ),
                        LE.le.{0} 1 X → LE.le.{0} (divisor X) (HMul.hMul.{0, 0, 0} CD (HPow.hPow.{0, 0, 0} X eta))) →
                      (∀ (X : ℝ),
                          LE.le.{0} 1 X → LE.le.{0} (harmonic X) (HMul.hMul.{0, 0, 0} CH (HPow.hPow.{0, 0, 0} X eta))) →
                        LE.le.{0} (HeckeSkeleton.LowHybrid.hybridArithmeticLoss divisor harmonic eta K N B L)
                          (HMul.hMul.{0, 0, 0}
                            (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} CD 5) (HPow.hPow.{0, 0, 0} CH 5))
                            (HPow.hPow.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B) L)
                              (HMul.hMul.{0, 0, 0} 12 eta)))
```

## HeckeSkeleton.LowHybrid.hybrid_arithmetic_loss_subpower

```lean
∀ (divisor harmonic : ℝ → ℝ),
  (∀ (X : ℝ), LE.le.{0} 1 X → LE.le.{0} 0 (divisor X)) →
    (∀ (X : ℝ), LE.le.{0} 1 X → LE.le.{0} 0 (harmonic X)) →
      HeckeSkeleton.LowHybrid.SubpowerBound divisor →
        HeckeSkeleton.LowHybrid.SubpowerBound harmonic →
          ∀ (eps : ℝ),
            LT.lt.{0} 0 eps →
              ∃ eta C,
                LT.lt.{0} 0 eta ∧
                  LT.lt.{0} 0 C ∧
                    ∀ (K N B L : ℝ),
                      LE.le.{0} 1 K →
                        LE.le.{0} 1 N →
                          LE.le.{0} 1 B →
                            LE.le.{0} 1 L →
                              LE.le.{0} (HeckeSkeleton.LowHybrid.hybridArithmeticLoss divisor harmonic eta K N B L)
                                (HMul.hMul.{0, 0, 0} C
                                  (HPow.hPow.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B) L) eps))
```

## HeckeSkeleton.LowHybrid.hybrid_energy

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    (∀ (a : A), LE.le.{0} 1 (q a)) →
      ∀ (Ccount : ℝ),
        LT.lt.{0} 0 Ccount →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
            ∀ (symbol : A → A → ℂ),
              (∀ (a b c : A),
                  Eq.{1} (symbol (HMul.hMul.{u_2, u_2, u_2} a b) c) (HMul.hMul.{0, 0, 0} (symbol a c) (symbol b c))) →
                (∀ (a b c : A),
                    Eq.{1} (symbol a (HMul.hMul.{u_2, u_2, u_2} b c)) (HMul.hMul.{0, 0, 0} (symbol a b) (symbol a c))) →
                  (∀ (a b : A),
                      Eq.{1} (HPow.hPow.{0, 0, 0} (symbol a b) 6)
                        (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
                    HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                        (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) symbol →
                      HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                          (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) symbol →
                        ∀ (eps : ℝ),
                          LT.lt.{0} 0 eps →
                            ∃ C0,
                              LT.lt.{0} 0 C0 ∧
                                ∀ (K N B L : ℝ),
                                  LE.le.{0} 1 K →
                                    LE.le.{0} 1 N →
                                      LE.le.{0} 1 B →
                                        LE.le.{0} 1 L →
                                          ∀ (rows marks columns cubes : Finset.{u_2} A) (a : A → ℂ) (beta : A → A → ℂ),
                                            (∀ (k : A),
                                                Membership.mem.{u_2, u_2} rows k →
                                                  HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords
                                                      k ∧
                                                    LE.le.{0} (normI k) K) →
                                              (∀ (p : A),
                                                  Membership.mem.{u_2, u_2} marks p →
                                                    HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords
                                                        p ∧
                                                      LE.le.{0} (normI p) L) →
                                                (∀ (n : A),
                                                    Membership.mem.{u_2, u_2} columns n →
                                                      HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                                                          coords n ∧
                                                        LE.le.{0} (normI n) N) →
                                                  (∀ (b : A),
                                                      Membership.mem.{u_2, u_2} cubes b → LE.le.{0} (normI b) B) →
                                                    (∀ (n : A),
                                                        Membership.mem.{u_2, u_2} columns n →
                                                          ∀ (b : A),
                                                            Membership.mem.{u_2, u_2} cubes b →
                                                              LE.le.{0} (Norm.norm.{0} (beta n b)) 1) →
                                                      LE.le.{0}
                                                        (HeckeSkeleton.LowHybrid.hybridEnergy.{u_2} symbol
                                                          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1,
                                                              u_2}
                                                            coords)
                                                          (⇑normI) a beta rows marks columns cubes)
                                                        (HMul.hMul.{0, 0, 0}
                                                          (HMul.hMul.{0, 0, 0}
                                                            (HMul.hMul.{0, 0, 0}
                                                              (HMul.hMul.{0, 0, 0}
                                                                (HMul.hMul.{0, 0, 0} C0
                                                                  (HPow.hPow.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0}
                                                                      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B)
                                                                      L)
                                                                    eps))
                                                                (HAdd.hAdd.{0, 0, 0} K (HMul.hMul.{0, 0, 0} N B)))
                                                              B)
                                                            (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} N L)
                                                              (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} N L) (2 / 3))))
                                                          (∑ p ∈ marks,
                                                            HDiv.hDiv.{0, 0, 0}
                                                              (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a p)) 2) (normI p)))
```

## HeckeSkeleton.LowHybrid.hybrid_energy_bounded

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    (∀ (a : A), LE.le.{0} 1 (q a)) →
      ∀ (Ccount : ℝ),
        LT.lt.{0} 0 Ccount →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
            ∀ (symbol : A → A → ℂ),
              (∀ (a b c : A),
                  Eq.{1} (symbol (HMul.hMul.{u_2, u_2, u_2} a b) c) (HMul.hMul.{0, 0, 0} (symbol a c) (symbol b c))) →
                (∀ (a b c : A),
                    Eq.{1} (symbol a (HMul.hMul.{u_2, u_2, u_2} b c)) (HMul.hMul.{0, 0, 0} (symbol a b) (symbol a c))) →
                  (∀ (a b : A),
                      Eq.{1} (HPow.hPow.{0, 0, 0} (symbol a b) 6)
                        (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
                    HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                        (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) symbol →
                      HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                          (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) symbol →
                        ∀ (eps : ℝ),
                          LT.lt.{0} 0 eps →
                            ∃ C0,
                              LT.lt.{0} 0 C0 ∧
                                ∀ (K N B L : ℝ),
                                  LE.le.{0} 1 K →
                                    LE.le.{0} 1 N →
                                      LE.le.{0} 1 B →
                                        LE.le.{0} 1 L →
                                          ∀ (rows marks columns cubes : Finset.{u_2} A) (a : A → ℂ) (beta : A → A → ℂ),
                                            (∀ (k : A),
                                                Membership.mem.{u_2, u_2} rows k →
                                                  HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords
                                                      k ∧
                                                    LE.le.{0} (normI k) K) →
                                              (∀ (p : A),
                                                  Membership.mem.{u_2, u_2} marks p →
                                                    HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords
                                                        p ∧
                                                      LE.le.{0} (normI p) L) →
                                                (∀ (n : A),
                                                    Membership.mem.{u_2, u_2} columns n →
                                                      HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                                                          coords n ∧
                                                        LE.le.{0} (normI n) N) →
                                                  (∀ (b : A),
                                                      Membership.mem.{u_2, u_2} cubes b → LE.le.{0} (normI b) B) →
                                                    (∀ (p : A),
                                                        Membership.mem.{u_2, u_2} marks p →
                                                          LE.le.{0} (Norm.norm.{0} (a p)) 1) →
                                                      (∀ (n : A),
                                                          Membership.mem.{u_2, u_2} columns n →
                                                            ∀ (b : A),
                                                              Membership.mem.{u_2, u_2} cubes b →
                                                                LE.le.{0} (Norm.norm.{0} (beta n b)) 1) →
                                                        LE.le.{0}
                                                          (HeckeSkeleton.LowHybrid.hybridEnergy.{u_2} symbol
                                                            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1,
                                                                u_2}
                                                              coords)
                                                            (⇑normI) a beta rows marks columns cubes)
                                                          (HMul.hMul.{0, 0, 0}
                                                            (HMul.hMul.{0, 0, 0}
                                                              (HMul.hMul.{0, 0, 0}
                                                                (HMul.hMul.{0, 0, 0} C0
                                                                  (HPow.hPow.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0}
                                                                      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B)
                                                                      L)
                                                                    eps))
                                                                (HAdd.hAdd.{0, 0, 0} K (HMul.hMul.{0, 0, 0} N B)))
                                                              B)
                                                            (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} N L)
                                                              (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} N L) (2 / 3))))
```

## HeckeSkeleton.LowHybrid.hybrid_energy_of_weighted_blocks

```lean
∀ {I : Type u} {D : Type uD} {R : Type uR} [DecidableEq.{u + 1} I] [inst : DecidableEq.{uD + 1} D]
  [inst_1 : DecidableEq.{uR + 1} R] (rows : Finset.{u} I) (ds : Finset.{uD} D) (rs : Finset.{uR} R)
  (localBlocks : I → Finset.{max uR uD} (Prod.{uD, uR} D R))
  (block : D → R → HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I) (mu : I → Prod.{uD, uR} D R → ℂ) (ND : D → ℝ)
  (NR : R → ℝ) (AD : D → ℝ) (Delta Q S B Ht Hc Hh : ℝ),
  LE.le.{0} 0 Delta →
    LE.le.{0} 0 Q →
      LE.le.{0} 0 S →
        LE.le.{0} 0 B →
          LE.le.{0} 0 Ht →
            LE.le.{0} 0 Hc →
              LE.le.{0} 0 Hh →
                (∀ (d : D), Membership.mem.{uD, uD} ds d → LT.lt.{0} 0 (ND d)) →
                  (∀ (r : R), Membership.mem.{uR, uR} rs r → LT.lt.{0} 0 (NR r)) →
                    (∀ (d : D), Membership.mem.{uD, uD} ds d → LE.le.{0} 0 (AD d)) →
                      (∀ (i : I),
                          Membership.mem.{u, u} rows i → localBlocks i ⊆ SProd.sprod.{uD, uR, max uD uR} ds rs) →
                        (∀ (i : I),
                            Membership.mem.{u, u} rows i →
                              ∀ (dr : Prod.{uD, uR} D R),
                                Membership.mem.{max uD uR, max uD uR} (localBlocks i) dr →
                                  LE.le.{0} (Norm.norm.{0} (mu i dr)) 1) →
                          (∀ (i : I),
                              Membership.mem.{u, u} rows i →
                                LE.le.{0} (↑(Finset.card.{max uD uR} (localBlocks i))) Delta) →
                            (∀ (d : D),
                                Membership.mem.{uD, uD} ds d →
                                  ∀ (r : R),
                                    Membership.mem.{uR, uR} rs r →
                                      HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.{u, v} (block d r)
                                        ({i ∈ rows |
                                          Membership.mem.{max uR uD, max uD uR} (localBlocks i) (Prod.mk.{uD, uR} d r)})
                                        Q S (HDiv.hDiv.{0, 0, 0} B (NR r)) (AD d)) →
                              (∀ (d : D),
                                  Membership.mem.{uD, uD} ds d →
                                    ∀ (r : R),
                                      Membership.mem.{uR, uR} rs r →
                                        LE.le.{0} (HeckeSkeleton.LowHybrid.WeightedBlock.tHarmonic.{u, v} (block d r))
                                          Ht) →
                                (∀ (d : D),
                                    Membership.mem.{uD, uD} ds d →
                                      ∀ (r : R),
                                        Membership.mem.{uR, uR} rs r →
                                          LE.le.{0} (HeckeSkeleton.LowHybrid.WeightedBlock.cHarmonic.{u, v} (block d r))
                                            Hc) →
                                  (∀ (d : D),
                                      Membership.mem.{uD, uD} ds d →
                                        ∀ (r : R),
                                          Membership.mem.{uR, uR} rs r →
                                            LE.le.{0}
                                              (HeckeSkeleton.LowHybrid.WeightedBlock.hHarmonic.{u, v} (block d r)) Hh) →
                                    LE.le.{0}
                                      (∑ i ∈ rows,
                                        HPow.hPow.{0, 0, 0}
                                          (Norm.norm.{0}
                                            (∑ dr ∈ localBlocks i,
                                              HMul.hMul.{0, 0, 0} (mu i dr)
                                                (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} 1 ↑√(ND dr.1))
                                                  (HeckeSkeleton.LowHybrid.WeightedBlock.row.{u, v} (block dr.1 dr.2)
                                                    i))))
                                          2)
                                      (HMul.hMul.{0, 0, 0}
                                        (HMul.hMul.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0}
                                              (HMul.hMul.{0, 0, 0}
                                                (HMul.hMul.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} Delta Q) S) B)
                                                (HPow.hPow.{0, 0, 0} Ht 2))
                                              Hc)
                                            Hh)
                                          (∑ d ∈ ds, HDiv.hDiv.{0, 0, 0} (AD d) (ND d)))
                                        (∑ r ∈ rs, HDiv.hDiv.{0, 0, 0} 1 (NR r)))
```

## HeckeSkeleton.LowHybrid.hybrid_energy_with_beta_mass

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    (∀ (a : A), LE.le.{0} 1 (q a)) →
      ∀ (Ccount : ℝ),
        LT.lt.{0} 0 Ccount →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
            ∀ (symbol : A → A → ℂ),
              (∀ (a b c : A),
                  Eq.{1} (symbol (HMul.hMul.{u_2, u_2, u_2} a b) c) (HMul.hMul.{0, 0, 0} (symbol a c) (symbol b c))) →
                (∀ (a b c : A),
                    Eq.{1} (symbol a (HMul.hMul.{u_2, u_2, u_2} b c)) (HMul.hMul.{0, 0, 0} (symbol a b) (symbol a c))) →
                  (∀ (a b : A),
                      Eq.{1} (HPow.hPow.{0, 0, 0} (symbol a b) 6)
                        (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
                    HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                        (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) symbol →
                      HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                          (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) symbol →
                        ∀ (eps : ℝ),
                          LT.lt.{0} 0 eps →
                            ∃ C0,
                              LT.lt.{0} 0 C0 ∧
                                ∀ (K N B L : ℝ),
                                  LE.le.{0} 1 K →
                                    LE.le.{0} 1 N →
                                      LE.le.{0} 1 B →
                                        LE.le.{0} 1 L →
                                          ∀ (rows marks columns cubes : Finset.{u_2} A) (a : A → ℂ) (beta : A → A → ℂ),
                                            (∀ (k : A),
                                                Membership.mem.{u_2, u_2} rows k →
                                                  HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords
                                                      k ∧
                                                    LE.le.{0} (normI k) K) →
                                              (∀ (p : A),
                                                  Membership.mem.{u_2, u_2} marks p →
                                                    HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords
                                                        p ∧
                                                      LE.le.{0} (normI p) L) →
                                                (∀ (n : A),
                                                    Membership.mem.{u_2, u_2} columns n →
                                                      HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                                                          coords n ∧
                                                        LE.le.{0} (normI n) N) →
                                                  (∀ (b : A),
                                                      Membership.mem.{u_2, u_2} cubes b → LE.le.{0} (normI b) B) →
                                                    LE.le.{0}
                                                      (HeckeSkeleton.LowHybrid.hybridEnergy.{u_2} symbol
                                                        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
                                                          coords)
                                                        (⇑normI) a beta rows marks columns cubes)
                                                      (HMul.hMul.{0, 0, 0}
                                                        (HMul.hMul.{0, 0, 0}
                                                          (HMul.hMul.{0, 0, 0}
                                                            (HMul.hMul.{0, 0, 0}
                                                              (HMul.hMul.{0, 0, 0}
                                                                (HMul.hMul.{0, 0, 0} C0
                                                                  (HPow.hPow.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0}
                                                                      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B)
                                                                      L)
                                                                    eps))
                                                                (HAdd.hAdd.{0, 0, 0} K (HMul.hMul.{0, 0, 0} N B)))
                                                              B)
                                                            (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} N L)
                                                              (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} N L) (2 / 3))))
                                                          (∑ p ∈ marks,
                                                            HDiv.hDiv.{0, 0, 0}
                                                              (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a p)) 2) (normI p)))
                                                        (HeckeSkeleton.LowHybrid.betaSquaredMass.{u_2} beta columns
                                                          cubes))
```

## HeckeSkeleton.LowHybrid.hybrid_fixed_block_from_sieve_bounds

```lean
∀ {I : Type u_1} [inst : DecidableEq.{u_1 + 1} I] (normI : I → ℝ) (sf : I → Prop) (symbol : I → I → ℂ),
  HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_1} normI sf symbol →
    HeckeSkeleton.LowHybrid.CubicSieveInput.{u_1} normI sf symbol →
      ∀ (eps : ℝ),
        LT.lt.{0} 0 eps →
          ∃ C,
            LT.lt.{0} 0 C ∧
              ∀ (K0 Y0 N0 L0 : ℝ),
                LE.le.{0} 1 K0 →
                  LE.le.{0} 1 Y0 →
                    LE.le.{0} 1 N0 →
                      LE.le.{0} 1 L0 →
                        ∀ (rows : Finset.{u_1} I) (pairs : Finset.{u_1} (Prod.{u_1, u_1} I I)) (qset : Finset.{u_1} I)
                          (cset : I → Finset.{u_1} I) (hset : Finset.{u_1} I) (mc : Finset.{u_1} (Prod.{u_1, u_1} I I))
                          (jset pset : Finset.{u_1} I) (qprod cprod : Prod.{u_1, u_1} I I → I) (a : I → I → ℂ)
                          (beta : I → I → I → ℂ) (Dq Dc Cbound Ebound : ℝ),
                          LE.le.{0} 0 Dq →
                            LE.le.{0} 0 Dc →
                              LE.le.{0} 0 Cbound →
                                (∀ (k : I), Membership.mem.{u_1, u_1} rows k → sf k ∧ LE.le.{0} (normI k) K0) →
                                  (∀ (j : I), Membership.mem.{u_1, u_1} qset j → sf j ∧ LE.le.{0} (normI j) Y0) →
                                    (∀ (j : I), Membership.mem.{u_1, u_1} jset j → sf j ∧ LE.le.{0} (normI j) N0) →
                                      (∀ (p : I), Membership.mem.{u_1, u_1} pset p → sf p ∧ LE.le.{0} (normI p) L0) →
                                        (∀ (u : Prod.{u_1, u_1} I I),
                                            Membership.mem.{u_1, u_1} pairs u →
                                              Membership.mem.{u_1, u_1} qset (qprod u)) →
                                          (∀ (j : I),
                                              Membership.mem.{u_1, u_1} qset j →
                                                LE.le.{0}
                                                  (↑(Finset.card.{u_1} ({u ∈ pairs | Eq.{u_1 + 1} (qprod u) j}))) Dq) →
                                            (∀ (u : Prod.{u_1, u_1} I I),
                                                Membership.mem.{u_1, u_1} pairs u →
                                                  LE.le.{0} (↑(Finset.card.{u_1} (cset u.1))) Cbound) →
                                              (∀ (u : Prod.{u_1, u_1} I I),
                                                  Membership.mem.{u_1, u_1} pairs u →
                                                    ∀ (c : I),
                                                      Membership.mem.{u_1, u_1} (cset u.1) c →
                                                        LE.le.{0} (Norm.norm.{0} (beta c u.1 u.2)) 1) →
                                                (∀ (u : Prod.{u_1, u_1} I I),
                                                    Membership.mem.{u_1, u_1} pairs u →
                                                      Membership.mem.{u_1, u_1} hset u.2) →
                                                  (∀ (u : Prod.{u_1, u_1} I I),
                                                      Membership.mem.{u_1, u_1} pairs u →
                                                        ∀ (c : I),
                                                          Membership.mem.{u_1, u_1} (cset u.1) c →
                                                            Membership.mem.{u_1, u_1} mc (Prod.mk.{u_1, u_1} u.1 c)) →
                                                    (∀ (u : Prod.{u_1, u_1} I I),
                                                        Membership.mem.{u_1, u_1} mc u →
                                                          Membership.mem.{u_1, u_1} jset (cprod u)) →
                                                      (∀ (j : I),
                                                          Membership.mem.{u_1, u_1} jset j →
                                                            LE.le.{0}
                                                              (↑(Finset.card.{u_1}
                                                                  ({u ∈ mc | Eq.{u_1 + 1} (cprod u) j})))
                                                              Dc) →
                                                        (∀ (h : I),
                                                            Membership.mem.{u_1, u_1} hset h →
                                                              LE.le.{0}
                                                                (∑ p ∈ pset,
                                                                  HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a h p)) 2)
                                                                Ebound) →
                                                          LE.le.{0}
                                                            (∑ k ∈ rows,
                                                              HPow.hPow.{0, 0, 0}
                                                                (Norm.norm.{0}
                                                                  (∑ u ∈ pairs,
                                                                    HMul.hMul.{0, 0, 0}
                                                                      (HPow.hPow.{0, 0, 0} (symbol (qprod u) k) 3)
                                                                      (∑ c ∈ cset u.1,
                                                                        HMul.hMul.{0, 0, 0} (beta c u.1 u.2)
                                                                          (∑ p ∈ pset,
                                                                            HMul.hMul.{0, 0, 0} (a u.2 p)
                                                                              (HPow.hPow.{0, 0, 0}
                                                                                (symbol p
                                                                                  (cprod (Prod.mk.{u_1, u_1} u.1 c)))
                                                                                (-2))))))
                                                                2)
                                                            (HMul.hMul.{0, 0, 0}
                                                              (HMul.hMul.{0, 0, 0}
                                                                (HMul.hMul.{0, 0, 0}
                                                                  (HMul.hMul.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0}
                                                                      (HMul.hMul.{0, 0, 0}
                                                                        (HMul.hMul.{0, 0, 0}
                                                                          (HMul.hMul.{0, 0, 0} C
                                                                            (HPow.hPow.{0, 0, 0}
                                                                              (HMul.hMul.{0, 0, 0}
                                                                                (HMul.hMul.{0, 0, 0}
                                                                                  (HMul.hMul.{0, 0, 0} K0 Y0) N0)
                                                                                L0)
                                                                              eps))
                                                                          (HAdd.hAdd.{0, 0, 0} K0 Y0))
                                                                        Cbound)
                                                                      ↑(Finset.card.{u_1} hset))
                                                                    Dq)
                                                                  Dc)
                                                                (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} N0 L0)
                                                                  (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} N0 L0)
                                                                    (2 / 3))))
                                                              Ebound)
```

## HeckeSkeleton.LowHybrid.hybrid_total_scale_bounds

```lean
∀ (K N B L : ℝ),
  LE.le.{0} 1 K →
    LE.le.{0} 1 N →
      LE.le.{0} 1 B →
        LE.le.{0} 1 L →
          LE.le.{0} 1 (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B) L) ∧
            LE.le.{0} K (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B) L) ∧
              LE.le.{0} N (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B) L) ∧
                LE.le.{0} B (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B) L) ∧
                  LE.le.{0} L (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B) L) ∧
                    LE.le.{0} (HMul.hMul.{0, 0, 0} N B)
                        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B) L) ∧
                      LE.le.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B)
                          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B) L) ∧
                        LE.le.{0} (HMul.hMul.{0, 0, 0} N L)
                          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B) L)
```

## HeckeSkeleton.LowHybrid.inverse_sqrt_norm_sq

```lean
∀ (x : ℝ),
  LT.lt.{0} 0 x → Eq.{1} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (HDiv.hDiv.{0, 0, 0} 1 ↑√x)) 2) (HDiv.hDiv.{0, 0, 0} 1 x)
```

## HeckeSkeleton.LowHybrid.linear_norm_counting_constant_pos

```lean
∀ {I : Type u_1} [Nonempty.{u_1 + 1} I] (q : I → ℕ) (C : ℝ),
  HeckeSkeleton.LowHybrid.LinearNormCounting.{u_1} q C → LT.lt.{0} 0 C
```

## HeckeSkeleton.LowHybrid.linear_norm_counting_constant_pos_of_element

```lean
∀ {I : Type u_1} (q : I → ℕ) (C : ℝ),
  HeckeSkeleton.LowHybrid.LinearNormCounting.{u_1} q C → ∀ (i : I), LT.lt.{0} 0 C
```

## HeckeSkeleton.LowHybrid.linear_norm_counting_norm_one_le

```lean
∀ {I : Type u_1} (q : I → ℕ) (C : ℝ),
  HeckeSkeleton.LowHybrid.LinearNormCounting.{u_1} q C → ∀ (i : I), LE.le.{0} 1 (q i)
```

## HeckeSkeleton.LowHybrid.linear_norm_counting_of_cutoffs

```lean
∀ {I : Type u_1} (q : I → ℕ) (C : ℝ) (cutoff : ℕ → Finset.{u_1} I),
  (∀ (N : ℕ) (i : I), LE.le.{0} (q i) N → Membership.mem.{u_1, u_1} (cutoff N) i) →
    (∀ (N : ℕ), LE.le.{0} (↑(Finset.card.{u_1} (cutoff N))) (HMul.hMul.{0, 0, 0} C ↑N)) →
      HeckeSkeleton.LowHybrid.LinearNormCounting.{u_1} q C
```

## HeckeSkeleton.LowHybrid.mul_contraction_norm

```lean
∀ (z u : ℂ), LE.le.{0} (Norm.norm.{0} u) 1 → LE.le.{0} (Norm.norm.{0} (HMul.hMul.{0, 0, 0} z u)) (Norm.norm.{0} z)
```

## HeckeSkeleton.LowHybrid.natural_arithmetic_loss_subpower_of_counting

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (q : A → ℕ) (hnorm : ∀ (a : A), Eq.{1} (normI a) ↑(q a)) (Ccount : ℝ)
  (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount),
  LT.lt.{0} 0 Ccount →
    (∀ (a : A), LE.le.{0} 1 (q a)) →
      ∀ (eps : ℝ),
        LT.lt.{0} 0 eps →
          ∃ eta C,
            LT.lt.{0} 0 eta ∧
              LT.lt.{0} 0 C ∧
                ∀ (K N B L : ℝ),
                  LE.le.{0} 1 K →
                    LE.le.{0} 1 N →
                      LE.le.{0} 1 B →
                        LE.le.{0} 1 L →
                          LE.le.{0}
                            (HeckeSkeleton.LowHybrid.naturalHybridArithmeticLoss
                              (HeckeSkeleton.LowHybrid.divisorEnvelopeOfCounting.{u_1, u_2} coords normI q hnorm Ccount
                                hcount)
                              (HeckeSkeleton.LowHybrid.harmonicEnvelope Ccount) eta K N B L)
                            (HMul.hMul.{0, 0, 0} C
                              (HPow.hPow.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B) L) eps))
```

## HeckeSkeleton.LowHybrid.natural_hybrid_arithmetic_loss_le

```lean
∀ (divisor harmonic : ℝ → ℝ) (CD CH eta K N B L : ℝ),
  LE.le.{0} 0 CD →
    LE.le.{0} 0 CH →
      LE.le.{0} 0 eta →
        LE.le.{0} 1 K →
          LE.le.{0} 1 N →
            LE.le.{0} 1 B →
              LE.le.{0} 1 L →
                (∀ (X : ℝ), LE.le.{0} 1 X → LE.le.{0} 0 (divisor X)) →
                  (∀ (X : ℝ), LE.le.{0} 1 X → LE.le.{0} 0 (harmonic X)) →
                    (∀ (X : ℝ),
                        LE.le.{0} 1 X → LE.le.{0} (divisor X) (HMul.hMul.{0, 0, 0} CD (HPow.hPow.{0, 0, 0} X eta))) →
                      (∀ (X : ℝ),
                          LE.le.{0} 1 X → LE.le.{0} (harmonic X) (HMul.hMul.{0, 0, 0} CH (HPow.hPow.{0, 0, 0} X eta))) →
                        LE.le.{0} (HeckeSkeleton.LowHybrid.naturalHybridArithmeticLoss divisor harmonic eta K N B L)
                          (HMul.hMul.{0, 0, 0}
                            (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} CD 5) (HPow.hPow.{0, 0, 0} CH 5))
                            (HPow.hPow.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B) L)
                              (HMul.hMul.{0, 0, 0} 12 eta)))
```

## HeckeSkeleton.LowHybrid.natural_hybrid_arithmetic_loss_subpower

```lean
∀ (divisor harmonic : ℝ → ℝ),
  (∀ (X : ℝ), LE.le.{0} 1 X → LE.le.{0} 0 (divisor X)) →
    (∀ (X : ℝ), LE.le.{0} 1 X → LE.le.{0} 0 (harmonic X)) →
      HeckeSkeleton.LowHybrid.SubpowerBound divisor →
        HeckeSkeleton.LowHybrid.SubpowerBound harmonic →
          ∀ (eps : ℝ),
            LT.lt.{0} 0 eps →
              ∃ eta C,
                LT.lt.{0} 0 eta ∧
                  LT.lt.{0} 0 C ∧
                    ∀ (K N B L : ℝ),
                      LE.le.{0} 1 K →
                        LE.le.{0} 1 N →
                          LE.le.{0} 1 B →
                            LE.le.{0} 1 L →
                              LE.le.{0}
                                (HeckeSkeleton.LowHybrid.naturalHybridArithmeticLoss divisor harmonic eta K N B L)
                                (HMul.hMul.{0, 0, 0} C
                                  (HPow.hPow.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B) L) eps))
```

## HeckeSkeleton.LowHybrid.norm_div_sqrt_sq

```lean
∀ (a : ℂ) (q : ℝ),
  LE.le.{0} 0 q →
    Eq.{1} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (HDiv.hDiv.{0, 0, 0} a ↑√q)) 2)
      (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} a) 2) q)
```

## HeckeSkeleton.LowHybrid.norm_sextic_le_one

```lean
∀ (z : ℂ), Eq.{1} z 0 ∨ Eq.{1} (HPow.hPow.{0, 0, 0} z 6) 1 → LE.le.{0} (Norm.norm.{0} z) 1
```

## HeckeSkeleton.LowHybrid.norm_sextic_neg_two_le_one

```lean
∀ (z : ℂ),
  Eq.{1} z 0 ∨ Eq.{1} (HPow.hPow.{0, 0, 0} z 6) 1 → LE.le.{0} (Norm.norm.{0} (HPow.hPow.{0, 0, 0} z (-2))) 1
```

## HeckeSkeleton.LowHybrid.norm_sq_le_betaSquaredMass

```lean
∀ {I : Type u_1} [CommMonoid.{u_1} I] (beta : I → I → ℂ) (columns cubes : Finset.{u_1} I) (n : I),
  Membership.mem.{u_1, u_1} columns n →
    ∀ (b : I),
      Membership.mem.{u_1, u_1} cubes b →
        LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (beta n b)) 2)
          (HeckeSkeleton.LowHybrid.betaSquaredMass.{u_1} beta columns cubes)
```

## HeckeSkeleton.LowHybrid.norm_support_mobius

```lean
∀ {Prime : Type u_1} (d : Finset.{u_1} Prime),
  Eq.{1} (Norm.norm.{0} (HPow.hPow.{0, 0, 0} (-1) (Finset.card.{u_1} d))) 1
```

## HeckeSkeleton.LowHybrid.norm_symbol_le_one

```lean
∀ {I : Type u_1} (symbol : I → I → ℂ) (cop : I → I → Prop),
  (∀ (i j : I), Eq.{1} (HPow.hPow.{0, 0, 0} (symbol i j) 6) (ite.{1} (cop i j) 1 0)) →
    ∀ (i j : I), LE.le.{0} (Norm.norm.{0} (symbol i j)) 1
```

## HeckeSkeleton.LowHybrid.norm_symbol_neg_two_le_one

```lean
∀ {I : Type u_1} (symbol : I → I → ℂ) (cop : I → I → Prop),
  (∀ (i j : I), Eq.{1} (HPow.hPow.{0, 0, 0} (symbol i j) 6) (ite.{1} (cop i j) 1 0)) →
    ∀ (i j : I), LE.le.{0} (Norm.norm.{0} (HPow.hPow.{0, 0, 0} (symbol i j) (-2))) 1
```

## HeckeSkeleton.LowHybrid.normalized_block_envelope

```lean
∀ (K N L D r C T G B A : ℝ),
  LE.le.{0} 1 K →
    LE.le.{0} 1 N →
      LE.le.{0} 1 L →
        LE.le.{0} 1 D →
          LE.le.{0} 1 r →
            LE.le.{0} 1 C →
              LE.le.{0} 1 T →
                LE.le.{0} 0 G →
                  LE.le.{0} 0 A →
                    Eq.{1} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} T 2) G) B →
                      LE.le.{0}
                        (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} 1 D)
                          (HeckeSkeleton.LowHybrid.completedBlock K N L D r C T G A))
                        (HMul.hMul.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0}
                            (HMul.hMul.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K (HMul.hMul.{0, 0, 0} N B)) B)
                              (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} N L)
                                (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} N L) (2 / 3))))
                            (HDiv.hDiv.{0, 0, 0} A D))
                          (HDiv.hDiv.{0, 0, 0} 1 r))
```

## HeckeSkeleton.LowHybrid.normalized_blocks_sum_le

```lean
∀ {DIndex : Type u_1} {RIndex : Type u_2} (ds : Finset.{u_1} DIndex) (rs : Finset.{u_2} RIndex)
  (dNorm : DIndex → ℝ) (rNorm : RIndex → ℝ) (C T G : DIndex → RIndex → ℝ) (A : DIndex → ℝ) (K N L B : ℝ),
  LE.le.{0} 1 K →
    LE.le.{0} 1 N →
      LE.le.{0} 1 L →
        (∀ (d : DIndex), Membership.mem.{u_1, u_1} ds d → LE.le.{0} 1 (dNorm d)) →
          (∀ (r : RIndex), Membership.mem.{u_2, u_2} rs r → LE.le.{0} 1 (rNorm r)) →
            (∀ (d : DIndex),
                Membership.mem.{u_1, u_1} ds d → ∀ (r : RIndex), Membership.mem.{u_2, u_2} rs r → LE.le.{0} 1 (C d r)) →
              (∀ (d : DIndex),
                  Membership.mem.{u_1, u_1} ds d →
                    ∀ (r : RIndex), Membership.mem.{u_2, u_2} rs r → LE.le.{0} 1 (T d r)) →
                (∀ (d : DIndex),
                    Membership.mem.{u_1, u_1} ds d →
                      ∀ (r : RIndex), Membership.mem.{u_2, u_2} rs r → LE.le.{0} 0 (G d r)) →
                  (∀ (d : DIndex), Membership.mem.{u_1, u_1} ds d → LE.le.{0} 0 (A d)) →
                    (∀ (d : DIndex),
                        Membership.mem.{u_1, u_1} ds d →
                          ∀ (r : RIndex),
                            Membership.mem.{u_2, u_2} rs r →
                              Eq.{1} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (T d r) 2) (G d r)) B) →
                      LE.le.{0}
                        (∑ d ∈ ds,
                          ∑ r ∈ rs,
                            HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} 1 (dNorm d))
                              (HeckeSkeleton.LowHybrid.completedBlock K N L (dNorm d) (rNorm r) (C d r) (T d r) (G d r)
                                (A d)))
                        (HMul.hMul.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0}
                            (HMul.hMul.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K (HMul.hMul.{0, 0, 0} N B)) B)
                              (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} N L)
                                (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} N L) (2 / 3))))
                            (∑ d ∈ ds, HDiv.hDiv.{0, 0, 0} (A d) (dNorm d)))
                          (∑ r ∈ rs, HDiv.hDiv.{0, 0, 0} 1 (rNorm r)))
```

## HeckeSkeleton.LowHybrid.normalized_column_mass

```lean
∀ {P : Type u_1} (columns : Finset.{u_1} P) (a : P → ℂ) (normP : P → ℝ),
  (∀ (p : P), Membership.mem.{u_1, u_1} columns p → LE.le.{0} 0 (normP p)) →
    Eq.{1} (∑ p ∈ columns, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (HDiv.hDiv.{0, 0, 0} (a p) ↑√(normP p))) 2)
      (∑ p ∈ columns, HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a p)) 2) (normP p))
```

## HeckeSkeleton.LowHybrid.one_add_log_le_small_power

```lean
∀ (X eps : ℝ),
  LE.le.{0} 1 X →
    LT.lt.{0} 0 eps →
      LE.le.{0} (HAdd.hAdd.{0, 0, 0} 1 (Real.log X))
        (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 (HDiv.hDiv.{0, 0, 0} 1 eps)) (HPow.hPow.{0, 0, 0} X eps))
```

## HeckeSkeleton.LowHybrid.one_le_real_norm_of_natural

```lean
∀ {I : Type u_1} (q : I → ℕ) (normI : I → ℝ),
  (∀ (i : I), Eq.{1} (normI i) ↑(q i)) → (∀ (i : I), LE.le.{0} 1 (q i)) → ∀ (i : I), LE.le.{0} 1 (normI i)
```

## HeckeSkeleton.LowHybrid.operator_bound_pullback

```lean
∀ {I : Type u_1} {J : Type u_2} {P : Type u_3} [DecidableEq.{u_2 + 1} J] (rows : Finset.{u_1} I)
  (target : Finset.{u_2} J) (columns : Finset.{u_3} P) (phi : I → J) (kernel : J → P → ℂ) (Q : ℝ),
  Set.InjOn.{u_1, u_2} phi ↑rows →
    (∀ (i : I), Membership.mem.{u_1, u_1} rows i → Membership.mem.{u_2, u_2} target (phi i)) →
      (∀ (a : P → ℂ),
          LE.le.{0}
            (∑ j ∈ target,
              HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ p ∈ columns, HMul.hMul.{0, 0, 0} (kernel j p) (a p))) 2)
            (HMul.hMul.{0, 0, 0} Q (∑ p ∈ columns, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a p)) 2))) →
        ∀ (a : P → ℂ),
          LE.le.{0}
            (∑ i ∈ rows,
              HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ p ∈ columns, HMul.hMul.{0, 0, 0} (kernel (phi i) p) (a p))) 2)
            (HMul.hMul.{0, 0, 0} Q (∑ p ∈ columns, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a p)) 2))
```

## HeckeSkeleton.LowHybrid.positive_fiber_sum_le

```lean
∀ {X : Type u_1} {Y : Type u_2} [inst : DecidableEq.{u_2 + 1} Y] (source : Finset.{u_1} X)
  (target : Finset.{u_2} Y) (phi : X → Y) (E : Y → ℝ) (D : ℝ),
  (∀ (x : X), Membership.mem.{u_1, u_1} source x → Membership.mem.{u_2, u_2} target (phi x)) →
    (∀ (y : Y), Membership.mem.{u_2, u_2} target y → LE.le.{0} 0 (E y)) →
      (∀ (y : Y),
          Membership.mem.{u_2, u_2} target y →
            LE.le.{0} (↑(Finset.card.{u_1} ({x ∈ source | Eq.{u_2 + 1} (phi x) y}))) D) →
        LE.le.{0} (∑ x ∈ source, E (phi x)) (HMul.hMul.{0, 0, 0} D (∑ y ∈ target, E y))
```

## HeckeSkeleton.LowHybrid.positive_triple_enlarge

```lean
∀ {M : Type u_1} {H : Type u_2} {C : Type u_3} [DecidableEq.{u_1 + 1} M] [DecidableEq.{u_2 + 1} H]
  [DecidableEq.{u_3 + 1} C] (pairs : Finset.{max u_2 u_1} (Prod.{u_1, u_2} M H)) (cset : M → Finset.{u_3} C)
  (hs : Finset.{u_2} H) (mc : Finset.{max u_3 u_1} (Prod.{u_1, u_3} M C)) (E : H → M → C → ℝ),
  (∀ (p : Prod.{u_1, u_2} M H), Membership.mem.{max u_1 u_2, max u_1 u_2} pairs p → Membership.mem.{u_2, u_2} hs p.2) →
    (∀ (p : Prod.{u_1, u_2} M H),
        Membership.mem.{max u_1 u_2, max u_1 u_2} pairs p →
          ∀ (c : C),
            Membership.mem.{u_3, u_3} (cset p.1) c →
              Membership.mem.{max u_3 u_1, max u_1 u_3} mc (Prod.mk.{u_1, u_3} p.1 c)) →
      (∀ (h : H) (m : M) (c : C), LE.le.{0} 0 (E h m c)) →
        LE.le.{0} (∑ p ∈ pairs, ∑ c ∈ cset p.1, E p.2 p.1 c) (∑ h ∈ hs, ∑ u ∈ mc, E h u.1 u.2)
```

## HeckeSkeleton.LowHybrid.prime_power_ge_two_outside_cutoff

```lean
∀ {P : Type u_1} (q : P → ℝ) (bad : Finset.{u_1} P) (eta : ℝ),
  LT.lt.{0} 0 eta →
    (∀ (p : P), LT.lt.{0} (q p) (HPow.hPow.{0, 0, 0} 2 (HDiv.hDiv.{0, 0, 0} 1 eta)) → Membership.mem.{u_1, u_1} bad p) →
      ∀ p ∉ bad, LE.le.{0} 2 (HPow.hPow.{0, 0, 0} (q p) eta)
```

## HeckeSkeleton.LowHybrid.prime_support_power_subpower_of_counting

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    ∀ (Ccount : ℝ),
      HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
        ∀ (base : ℝ),
          LE.le.{0} 0 base →
            ∀ (eta : ℝ),
              LT.lt.{0} 0 eta →
                ∃ C,
                  LT.lt.{0} 0 C ∧
                    ∀ (a : A),
                      LE.le.{0}
                        (HPow.hPow.{0, 0, 0} base
                          (Finset.card.{u_1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.support.{u_1, u_2} coords a)))
                        (HMul.hMul.{0, 0, 0} C (HPow.hPow.{0, 0, 0} (normI a) eta))
```

## HeckeSkeleton.LowHybrid.product_fiber_card_le_divisors

```lean
∀ {I : Type u_1} [inst : CancelCommMonoid.{u_1} I] [inst_1 : DecidableEq.{u_1 + 1} I]
  (pairs : Finset.{u_1} (Prod.{u_1, u_1} I I)) (j : I) (divisors : Finset.{u_1} I),
  (∀ (d : I), Dvd.dvd.{u_1} d j → Membership.mem.{u_1, u_1} divisors d) →
    LE.le.{0} (Finset.card.{u_1} ({x ∈ pairs | Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} x.1 x.2) j}))
      (Finset.card.{u_1} divisors)
```

## HeckeSkeleton.LowHybrid.quadratic_sieve_input_transpose

```lean
∀ {I : Type u_1} (normI : I → ℝ) (sf : I → Prop) (symbol : I → I → ℂ),
  HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_1} normI sf symbol →
    HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_1} normI sf fun a b => symbol b a
```

## HeckeSkeleton.LowHybrid.quotient_injOn

```lean
∀ {I : Type u_1} [inst : CancelCommMonoid.{u_1} I] [DecidableEq.{u_1 + 1} I] (rows : Finset.{u_1} I) (d : I)
  (quotient : I → I),
  (∀ (k : I), Membership.mem.{u_1, u_1} rows k → Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} d (quotient k)) k) →
    Set.InjOn.{u_1, u_1} quotient ↑rows
```

## HeckeSkeleton.LowHybrid.quotient_norm_le

```lean
∀ {I : Type u_1} [inst : Monoid.{u_1} I] (normI : I → ℝ),
  (∀ (i : I), LE.le.{0} 1 (normI i)) →
    (∀ (i j : I), Eq.{1} (normI (HMul.hMul.{u_1, u_1, u_1} i j)) (HMul.hMul.{0, 0, 0} (normI i) (normI j))) →
      ∀ (d q k : I), Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} d q) k → LE.le.{0} (normI q) (normI k)
```

## HeckeSkeleton.LowHybrid.real_norm_reciprocal_sum_subpower

```lean
∀ {I : Type u_1} (q : I → ℕ) (normI : I → ℝ),
  (∀ (i : I), Eq.{1} (normI i) ↑(q i)) →
    ∀ (C : ℝ),
      LT.lt.{0} 0 C →
        (∀ (i : I), LE.le.{0} 1 (q i)) →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_1} q C →
            ∀ (eps : ℝ),
              LT.lt.{0} 0 eps →
                ∃ CH,
                  LT.lt.{0} 0 CH ∧
                    ∀ (X : ℝ),
                      LE.le.{0} 1 X →
                        ∀ (s : Finset.{u_1} I),
                          (∀ (i : I), Membership.mem.{u_1, u_1} s i → LE.le.{0} (normI i) X) →
                            LE.le.{0} (∑ i ∈ s, HDiv.hDiv.{0, 0, 0} 1 (normI i))
                              (HMul.hMul.{0, 0, 0} CH (HPow.hPow.{0, 0, 0} X eps))
```

## HeckeSkeleton.LowHybrid.reciprocal_grid_sum

```lean
∀ {T : Type u_1} {H : Type u_2} (ts : Finset.{u_1} T) (hs : Finset.{u_2} H) (wt : T → ℝ) (wh : H → ℝ) (R : ℝ),
  (∀ (t : T), Membership.mem.{u_1, u_1} ts t → LT.lt.{0} 0 (wt t)) →
    (∀ (h : H), Membership.mem.{u_2, u_2} hs h → LT.lt.{0} 0 (wh h)) →
      Eq.{1} (∑ t ∈ ts, ∑ h ∈ hs, HDiv.hDiv.{0, 0, 0} R (HMul.hMul.{0, 0, 0} (wt t) (wh h)))
        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} R (∑ t ∈ ts, HDiv.hDiv.{0, 0, 0} 1 (wt t)))
          (∑ h ∈ hs, HDiv.hDiv.{0, 0, 0} 1 (wh h)))
```

## HeckeSkeleton.LowHybrid.reciprocal_sum_le_harmonicEnvelope

```lean
∀ {I : Type u_1} (q : I → ℕ) (normI : I → ℝ),
  (∀ (i : I), Eq.{1} (normI i) ↑(q i)) →
    ∀ (C : ℝ),
      LE.le.{0} 0 C →
        (∀ (i : I), LE.le.{0} 1 (q i)) →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_1} q C →
            ∀ (X : ℝ),
              LE.le.{0} 1 X →
                ∀ (s : Finset.{u_1} I),
                  (∀ (i : I), Membership.mem.{u_1, u_1} s i → LE.le.{0} (normI i) X) →
                    LE.le.{0} (∑ i ∈ s, HDiv.hDiv.{0, 0, 0} 1 (normI i)) (HeckeSkeleton.LowHybrid.harmonicEnvelope C X)
```

## HeckeSkeleton.LowHybrid.reciprocal_sum_le_harmonic_of_prefix_count

```lean
∀ {I : Type u_1} (s : Finset.{u_1} I) (q : I → ℕ) (N : ℕ) (C : ℝ),
  (∀ (i : I), Membership.mem.{u_1, u_1} s i → LE.le.{0} 1 (q i)) →
    (∀ (i : I), Membership.mem.{u_1, u_1} s i → LE.le.{0} (q i) N) →
      (∀ (n : ℕ),
          LE.le.{0} n N → LE.le.{0} (↑(Finset.card.{u_1} ({i ∈ s | LE.le.{0} (q i) n}))) (HMul.hMul.{0, 0, 0} C ↑n)) →
        LE.le.{0} (∑ i ∈ s, HDiv.hDiv.{0, 0, 0} 1 ↑(q i))
          (HMul.hMul.{0, 0, 0} C (HeckeSkeleton.LowHybrid.harmonicPartial N))
```

## HeckeSkeleton.LowHybrid.reciprocal_sum_le_log_of_linear_counting

```lean
∀ {I : Type u_1} (q : I → ℕ) (C : ℝ),
  LE.le.{0} 0 C →
    (∀ (i : I), LE.le.{0} 1 (q i)) →
      HeckeSkeleton.LowHybrid.LinearNormCounting.{u_1} q C →
        ∀ (X : ℝ),
          LE.le.{0} 1 X →
            ∀ (s : Finset.{u_1} I),
              (∀ (i : I), Membership.mem.{u_1, u_1} s i → LE.le.{0} (↑(q i)) X) →
                LE.le.{0} (∑ i ∈ s, HDiv.hDiv.{0, 0, 0} 1 ↑(q i))
                  (HMul.hMul.{0, 0, 0} C (HAdd.hAdd.{0, 0, 0} 1 (Real.log X)))
```

## HeckeSkeleton.LowHybrid.reciprocal_sum_subpower_of_linear_counting

```lean
∀ {I : Type u_1} (q : I → ℕ) (C : ℝ),
  LT.lt.{0} 0 C →
    (∀ (i : I), LE.le.{0} 1 (q i)) →
      HeckeSkeleton.LowHybrid.LinearNormCounting.{u_1} q C →
        ∀ (eps : ℝ),
          LT.lt.{0} 0 eps →
            ∃ CH,
              LT.lt.{0} 0 CH ∧
                ∀ (X : ℝ),
                  LE.le.{0} 1 X →
                    ∀ (s : Finset.{u_1} I),
                      (∀ (i : I), Membership.mem.{u_1, u_1} s i → LE.le.{0} (↑(q i)) X) →
                        LE.le.{0} (∑ i ∈ s, HDiv.hDiv.{0, 0, 0} 1 ↑(q i))
                          (HMul.hMul.{0, 0, 0} CH (HPow.hPow.{0, 0, 0} X eps))
```

## HeckeSkeleton.LowHybrid.row_fiber_sieve

```lean
∀ {X : Type u_1} {Y : Type u_2} {P : Type u_3} [inst : DecidableEq.{u_2 + 1} Y] (source : Finset.{u_1} X)
  (target : Finset.{u_2} Y) (columns : Finset.{u_3} P) (phi : X → Y) (chi : P → Y → ℂ) (a : P → ℂ) (D S : ℝ),
  LE.le.{0} 0 D →
    (∀ (x : X), Membership.mem.{u_1, u_1} source x → Membership.mem.{u_2, u_2} target (phi x)) →
      (∀ (y : Y),
          Membership.mem.{u_2, u_2} target y →
            LE.le.{0} (↑(Finset.card.{u_1} ({x ∈ source | Eq.{u_2 + 1} (phi x) y}))) D) →
        (∀ (u : P → ℂ),
            LE.le.{0}
              (∑ y ∈ target, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ p ∈ columns, HMul.hMul.{0, 0, 0} (u p) (chi p y))) 2)
              (HMul.hMul.{0, 0, 0} S (∑ p ∈ columns, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (u p)) 2))) →
          LE.le.{0}
            (∑ x ∈ source,
              HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ p ∈ columns, HMul.hMul.{0, 0, 0} (a p) (chi p (phi x)))) 2)
            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} D S) (∑ p ∈ columns, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a p)) 2))
```

## HeckeSkeleton.LowHybrid.row_local_cauchy

```lean
∀ {K : Type u_1} {D : Type u_2} (rows : Finset.{u_1} K) (localBlocks : K → Finset.{u_2} D) (mu value : K → D → ℂ)
  (Delta : ℝ),
  (∀ (k : K),
      Membership.mem.{u_1, u_1} rows k →
        ∀ (d : D), Membership.mem.{u_2, u_2} (localBlocks k) d → LE.le.{0} (Norm.norm.{0} (mu k d)) 1) →
    (∀ (k : K), Membership.mem.{u_1, u_1} rows k → LE.le.{0} (↑(Finset.card.{u_2} (localBlocks k))) Delta) →
      LE.le.{0}
        (∑ k ∈ rows,
          HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ d ∈ localBlocks k, HMul.hMul.{0, 0, 0} (mu k d) (value k d))) 2)
        (HMul.hMul.{0, 0, 0} Delta (∑ k ∈ rows, ∑ d ∈ localBlocks k, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (value k d)) 2))
```

## HeckeSkeleton.LowHybrid.row_local_positive_transpose

```lean
∀ {K : Type u_1} {D : Type u_2} [DecidableEq.{u_1 + 1} K] [inst : DecidableEq.{u_2 + 1} D] (rows : Finset.{u_1} K)
  (localBlocks : K → Finset.{u_2} D) (blocks : Finset.{u_2} D) (E : K → D → ℝ),
  (∀ (k : K),
      Membership.mem.{u_1, u_1} rows k →
        ∀ (d : D), Membership.mem.{u_2, u_2} (localBlocks k) d → Membership.mem.{u_2, u_2} blocks d) →
    Eq.{1} (∑ k ∈ rows, ∑ d ∈ localBlocks k, E k d)
      (∑ d ∈ blocks, ∑ k ∈ rows with Membership.mem.{u_2, u_2} (localBlocks k) d, E k d)
```

## HeckeSkeleton.LowHybrid.row_local_weighted_cauchy

```lean
∀ {K : Type u_1} {D : Type u_2} [DecidableEq.{u_1 + 1} K] [inst : DecidableEq.{u_2 + 1} D] (rows : Finset.{u_1} K)
  (localBlocks : K → Finset.{u_2} D) (blocks : Finset.{u_2} D) (mu : K → D → ℂ) (weight : D → ℂ) (value : K → D → ℂ)
  (Delta : ℝ),
  (∀ (k : K),
      Membership.mem.{u_1, u_1} rows k →
        ∀ (d : D), Membership.mem.{u_2, u_2} (localBlocks k) d → LE.le.{0} (Norm.norm.{0} (mu k d)) 1) →
    (∀ (k : K), Membership.mem.{u_1, u_1} rows k → LE.le.{0} (↑(Finset.card.{u_2} (localBlocks k))) Delta) →
      (∀ (k : K),
          Membership.mem.{u_1, u_1} rows k →
            ∀ (d : D), Membership.mem.{u_2, u_2} (localBlocks k) d → Membership.mem.{u_2, u_2} blocks d) →
        LE.le.{0}
          (∑ k ∈ rows,
            HPow.hPow.{0, 0, 0}
              (Norm.norm.{0}
                (∑ d ∈ localBlocks k, HMul.hMul.{0, 0, 0} (mu k d) (HMul.hMul.{0, 0, 0} (weight d) (value k d))))
              2)
          (HMul.hMul.{0, 0, 0} Delta
            (∑ d ∈ blocks,
              HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (weight d)) 2)
                (∑ k ∈ rows with Membership.mem.{u_2, u_2} (localBlocks k) d,
                  HPow.hPow.{0, 0, 0} (Norm.norm.{0} (value k d)) 2)))
```

## HeckeSkeleton.LowHybrid.row_local_weighted_cauchy_of_block_bounds

```lean
∀ {K : Type u_1} {D : Type u_2} [DecidableEq.{u_1 + 1} K] [inst : DecidableEq.{u_2 + 1} D] (rows : Finset.{u_1} K)
  (localBlocks : K → Finset.{u_2} D) (blocks : Finset.{u_2} D) (mu : K → D → ℂ) (weight : D → ℂ) (value : K → D → ℂ)
  (Delta : ℝ) (bound : D → ℝ),
  LE.le.{0} 0 Delta →
    (∀ (k : K),
        Membership.mem.{u_1, u_1} rows k →
          ∀ (d : D), Membership.mem.{u_2, u_2} (localBlocks k) d → LE.le.{0} (Norm.norm.{0} (mu k d)) 1) →
      (∀ (k : K), Membership.mem.{u_1, u_1} rows k → LE.le.{0} (↑(Finset.card.{u_2} (localBlocks k))) Delta) →
        (∀ (k : K),
            Membership.mem.{u_1, u_1} rows k →
              ∀ (d : D), Membership.mem.{u_2, u_2} (localBlocks k) d → Membership.mem.{u_2, u_2} blocks d) →
          (∀ (d : D),
              Membership.mem.{u_2, u_2} blocks d →
                LE.le.{0}
                  (∑ k ∈ rows with Membership.mem.{u_2, u_2} (localBlocks k) d,
                    HPow.hPow.{0, 0, 0} (Norm.norm.{0} (value k d)) 2)
                  (bound d)) →
            LE.le.{0}
              (∑ k ∈ rows,
                HPow.hPow.{0, 0, 0}
                  (Norm.norm.{0}
                    (∑ d ∈ localBlocks k, HMul.hMul.{0, 0, 0} (mu k d) (HMul.hMul.{0, 0, 0} (weight d) (value k d))))
                  2)
              (HMul.hMul.{0, 0, 0} Delta
                (∑ d ∈ blocks, HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (weight d)) 2) (bound d)))
```

## HeckeSkeleton.LowHybrid.row_powerset_filter_eq_common_powerset

```lean
∀ {Prime : Type u_1} [inst : DecidableEq.{u_1 + 1} Prime] (columnSupport rowSupport : Finset.{u_1} Prime),
  Eq.{u_1 + 1} ({d ∈ Finset.powerset.{u_1} rowSupport | d ⊆ columnSupport})
    (Finset.powerset.{u_1} (Inter.inter.{u_1} columnSupport rowSupport))
```

## HeckeSkeleton.LowHybrid.row_pullback_le

```lean
∀ {I : Type u_1} {J : Type u_2} [DecidableEq.{u_2 + 1} J] (rows : Finset.{u_1} I) (target : Finset.{u_2} J)
  (phi : I → J) (f : J → ℝ),
  Set.InjOn.{u_1, u_2} phi ↑rows →
    (∀ (i : I), Membership.mem.{u_1, u_1} rows i → Membership.mem.{u_2, u_2} target (phi i)) →
      (∀ (j : J), Membership.mem.{u_2, u_2} target j → LE.le.{0} 0 (f j)) →
        LE.le.{0} (∑ i ∈ rows, f (phi i)) (∑ j ∈ target, f j)
```

## HeckeSkeleton.LowHybrid.scalar_row_energy

```lean
∀ {K : Type u_1} (rows : Finset.{u_1} K) (f : K → ℂ) (a : ℂ),
  Eq.{1} (∑ k ∈ rows, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (HMul.hMul.{0, 0, 0} a (f k))) 2)
    (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} a) 2)
      (∑ k ∈ rows, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (f k)) 2))
```

## HeckeSkeleton.LowHybrid.squarefree_divisor_count_subpower

```lean
∀ {I : Type u_1} {P : Type u_2} (support : I → Finset.{u_2} P) (divisors : I → Finset.{u_1} I) (primeNorm : P → ℝ)
  (normI : I → ℝ),
  (∀ (p : P), LE.le.{0} 1 (primeNorm p)) →
    (∀ (X : ℝ), Set.Finite.{u_2} (Set.ofPred.{u_2} fun p => LE.le.{0} (primeNorm p) X)) →
      (∀ (i : I),
          LE.le.{0} (↑(Finset.card.{u_1} (divisors i))) (HPow.hPow.{0, 0, 0} 2 (Finset.card.{u_2} (support i)))) →
        (∀ (i : I), LE.le.{0} (∏ p ∈ support i, primeNorm p) (normI i)) →
          ∀ (eta : ℝ),
            LT.lt.{0} 0 eta →
              ∃ C,
                LT.lt.{0} 0 C ∧
                  ∀ (i : I),
                    LE.le.{0} (↑(Finset.card.{u_1} (divisors i)))
                      (HMul.hMul.{0, 0, 0} C (HPow.hPow.{0, 0, 0} (normI i) eta))
```

## HeckeSkeleton.LowHybrid.squarefree_support_subpower

```lean
∀ {P : Type u_1} (q : P → ℝ),
  (∀ (p : P), LE.le.{0} 1 (q p)) →
    (∀ (X : ℝ), Set.Finite.{u_1} (Set.ofPred.{u_1} fun p => LE.le.{0} (q p) X)) →
      ∀ (eta : ℝ),
        LT.lt.{0} 0 eta →
          ∃ C,
            LT.lt.{0} 0 C ∧
              ∀ (s : Finset.{u_1} P),
                LE.le.{0} (HPow.hPow.{0, 0, 0} 2 (Finset.card.{u_1} s))
                  (HMul.hMul.{0, 0, 0} C (HPow.hPow.{0, 0, 0} (∏ p ∈ s, q p) eta))
```

## HeckeSkeleton.LowHybrid.squarefree_support_subpower_of_cutoffs

```lean
∀ {P : Type u_1} (q : P → ℝ),
  (∀ (p : P), LE.le.{0} 1 (q p)) →
    ∀ (cutoff : ℝ → Finset.{u_1} P),
      (∀ (X : ℝ) (p : P), LE.le.{0} (q p) X → Membership.mem.{u_1, u_1} (cutoff X) p) →
        ∀ (eta : ℝ),
          LT.lt.{0} 0 eta →
            ∃ C,
              LT.lt.{0} 0 C ∧
                ∀ (s : Finset.{u_1} P),
                  LE.le.{0} (HPow.hPow.{0, 0, 0} 2 (Finset.card.{u_1} s))
                    (HMul.hMul.{0, 0, 0} C (HPow.hPow.{0, 0, 0} (∏ p ∈ s, q p) eta))
```

## HeckeSkeleton.LowHybrid.subpower_of_logarithmic_bound

```lean
∀ (f : ℝ → ℝ) (C : ℝ),
  LT.lt.{0} 0 C →
    (∀ (X : ℝ), LE.le.{0} 1 X → LE.le.{0} (f X) (HMul.hMul.{0, 0, 0} C (HAdd.hAdd.{0, 0, 0} 1 (Real.log X)))) →
      HeckeSkeleton.LowHybrid.SubpowerBound f
```

## HeckeSkeleton.LowHybrid.sum_mul_le_of_prefix_bound

```lean
∀ (a w : ℕ → ℝ) (N : ℕ) (C : ℝ),
  (∀ (n : ℕ), LE.le.{0} 0 (w n)) →
    Antitone.{0, 0} w →
      (∀ (n : ℕ), LE.le.{0} n N → LE.le.{0} (∑ j ∈ Finset.range n, a j) (HMul.hMul.{0, 0, 0} C ↑n)) →
        LE.le.{0} (∑ n ∈ Finset.range N, HMul.hMul.{0, 0, 0} (a n) (w n))
          (HMul.hMul.{0, 0, 0} C (∑ n ∈ Finset.range N, w n))
```

## HeckeSkeleton.LowHybrid.support_coprime_mask_eq_mobius_sum

```lean
∀ {Prime : Type u_1} [inst : DecidableEq.{u_1 + 1} Prime] (columnSupport rowSupport : Finset.{u_1} Prime),
  Eq.{1} (ite.{1} (Disjoint.{u_1} columnSupport rowSupport) 1 0)
    (∑ d ∈ Finset.powerset.{u_1} (Inter.inter.{u_1} columnSupport rowSupport),
      HPow.hPow.{0, 0, 0} (-1) (Finset.card.{u_1} d))
```

## HeckeSkeleton.LowHybrid.support_coprime_mask_eq_row_divisor_sum

```lean
∀ {Prime : Type u_1} [inst : DecidableEq.{u_1 + 1} Prime] (columnSupport rowSupport : Finset.{u_1} Prime),
  Eq.{1} (ite.{1} (Disjoint.{u_1} columnSupport rowSupport) 1 0)
    (∑ d ∈ Finset.powerset.{u_1} rowSupport,
      ite.{1} (d ⊆ columnSupport) (HPow.hPow.{0, 0, 0} (-1) (Finset.card.{u_1} d)) 0)
```

## HeckeSkeleton.LowHybrid.support_mask_column_expansion

```lean
∀ {Prime : Type u_1} {P : Type u_2} [inst : DecidableEq.{u_1 + 1} Prime] (columns : Finset.{u_2} P)
  (columnSupport : P → Finset.{u_1} Prime) (rowSupport : Finset.{u_1} Prime) (F : P → ℂ),
  Eq.{1} (∑ p ∈ columns, HMul.hMul.{0, 0, 0} (ite.{1} (Disjoint.{u_1} (columnSupport p) rowSupport) 1 0) (F p))
    (∑ d ∈ Finset.powerset.{u_1} rowSupport,
      HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (-1) (Finset.card.{u_1} d))
        (∑ p ∈ columns with d ⊆ columnSupport p, F p))
```

## HeckeSkeleton.LowHybrid.support_mask_row_energy

```lean
∀ {Prime : Type u_1} {K : Type u_2} {P : Type u_3} [inst : DecidableEq.{u_1 + 1} Prime] (rows : Finset.{u_2} K)
  (columns : Finset.{u_3} P) (rowSupport : K → Finset.{u_1} Prime) (columnSupport : P → Finset.{u_1} Prime)
  (F : K → P → ℂ) (Delta : ℝ),
  (∀ (k : K),
      Membership.mem.{u_2, u_2} rows k →
        LE.le.{0} (↑(Finset.card.{u_1} (Finset.powerset.{u_1} (rowSupport k)))) Delta) →
    LE.le.{0}
      (∑ k ∈ rows,
        HPow.hPow.{0, 0, 0}
          (Norm.norm.{0}
            (∑ p ∈ columns,
              HMul.hMul.{0, 0, 0} (ite.{1} (Disjoint.{u_1} (columnSupport p) (rowSupport k)) 1 0) (F k p)))
          2)
      (HMul.hMul.{0, 0, 0} Delta
        (∑ k ∈ rows,
          ∑ d ∈ Finset.powerset.{u_1} (rowSupport k),
            HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ p ∈ columns with d ⊆ columnSupport p, F k p)) 2))
```

## HeckeSkeleton.LowHybrid.support_mask_row_energy_local_count

```lean
∀ {Prime : Type u_1} {K : Type u_2} {P : Type u_3} [inst : DecidableEq.{u_1 + 1} Prime] (rows : Finset.{u_2} K)
  (columns : Finset.{u_3} P) (rowSupport : K → Finset.{u_1} Prime) (columnSupport : P → Finset.{u_1} Prime)
  (F : K → P → ℂ),
  LE.le.{0}
    (∑ k ∈ rows,
      HPow.hPow.{0, 0, 0}
        (Norm.norm.{0}
          (∑ p ∈ columns, HMul.hMul.{0, 0, 0} (ite.{1} (Disjoint.{u_1} (columnSupport p) (rowSupport k)) 1 0) (F k p)))
        2)
    (∑ k ∈ rows,
      HMul.hMul.{0, 0, 0} (↑(Finset.card.{u_1} (Finset.powerset.{u_1} (rowSupport k))))
        (∑ d ∈ Finset.powerset.{u_1} (rowSupport k),
          HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ p ∈ columns with d ⊆ columnSupport p, F k p)) 2))
```

## HeckeSkeleton.LowHybrid.support_mask_row_expansion

```lean
∀ {Prime : Type u_1} {K : Type u_2} {P : Type u_3} [inst : DecidableEq.{u_1 + 1} Prime] (columns : Finset.{u_3} P)
  (rowSupport : K → Finset.{u_1} Prime) (columnSupport : P → Finset.{u_1} Prime) (F : K → P → ℂ) (k : K),
  Eq.{1} (∑ p ∈ columns, HMul.hMul.{0, 0, 0} (ite.{1} (Disjoint.{u_1} (columnSupport p) (rowSupport k)) 1 0) (F k p))
    (∑ d ∈ Finset.powerset.{u_1} (rowSupport k),
      HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (-1) (Finset.card.{u_1} d))
        (∑ p ∈ columns with d ⊆ columnSupport p, F k p))
```

## HeckeSkeleton.LowHybrid.support_power_base_le_product

```lean
∀ {P : Type u_1} (q : P → ℝ) (bad s : Finset.{u_1} P) (base eta : ℝ),
  LE.le.{0} 1 base →
    LE.le.{0} 0 eta →
      (∀ (p : P), LE.le.{0} 1 (q p)) →
        (∀ p ∉ bad, LE.le.{0} base (HPow.hPow.{0, 0, 0} (q p) eta)) →
          LE.le.{0} (HPow.hPow.{0, 0, 0} base (Finset.card.{u_1} s))
            (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} base (Finset.card.{u_1} bad))
              (∏ p ∈ s, HPow.hPow.{0, 0, 0} (q p) eta))
```

## HeckeSkeleton.LowHybrid.support_power_two_le_product

```lean
∀ {P : Type u_1} [DecidableEq.{u_1 + 1} P] (q : P → ℝ) (bad s : Finset.{u_1} P) (eta : ℝ),
  LE.le.{0} 0 eta →
    (∀ (p : P), LE.le.{0} 1 (q p)) →
      (∀ p ∉ bad, LE.le.{0} 2 (HPow.hPow.{0, 0, 0} (q p) eta)) →
        LE.le.{0} (HPow.hPow.{0, 0, 0} 2 (Finset.card.{u_1} s))
          (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} 2 (Finset.card.{u_1} bad)) (∏ p ∈ s, HPow.hPow.{0, 0, 0} (q p) eta))
```

## HeckeSkeleton.LowHybrid.twisted_beta_norm_le

```lean
∀ (beta z w : ℂ) (p : Prop),
  LE.le.{0} (Norm.norm.{0} z) 1 →
    LE.le.{0} (Norm.norm.{0} w) 1 →
      LE.le.{0}
        (Norm.norm.{0}
          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} beta (HPow.hPow.{0, 0, 0} z 3)) w)
            (ite.{1} p 1 0)))
        (Norm.norm.{0} beta)
```

## HeckeSkeleton.LowHybrid.twisted_column_mass_le

```lean
∀ {I : Type u_1} (ps : Finset.{u_1} I) (a u : I → ℂ) (normI : I → ℝ),
  (∀ (p : I), Membership.mem.{u_1, u_1} ps p → LE.le.{0} (Norm.norm.{0} (u p)) 1) →
    (∀ (p : I), Membership.mem.{u_1, u_1} ps p → LT.lt.{0} 0 (normI p)) →
      LE.le.{0}
        (∑ p ∈ ps,
          HPow.hPow.{0, 0, 0} (Norm.norm.{0} (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (a p) ↑√(normI p)) (u p))) 2)
        (∑ p ∈ ps, HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a p)) 2) (normI p))
```

## HeckeSkeleton.LowHybrid.two_row_local_cauchy

```lean
∀ {K : Type u_1} {D : Type u_2} {R : Type u_3} (rows : Finset.{u_1} K) (outer : K → Finset.{u_2} D)
  (inner : K → D → Finset.{u_3} R) (mu : K → D → ℂ) (nu value : K → D → R → ℂ) (DeltaD DeltaR : ℝ),
  LE.le.{0} 0 DeltaD →
    (∀ (k : K),
        Membership.mem.{u_1, u_1} rows k →
          ∀ (d : D), Membership.mem.{u_2, u_2} (outer k) d → LE.le.{0} (Norm.norm.{0} (mu k d)) 1) →
      (∀ (k : K),
          Membership.mem.{u_1, u_1} rows k →
            ∀ (d : D),
              Membership.mem.{u_2, u_2} (outer k) d →
                ∀ (r : R), Membership.mem.{u_3, u_3} (inner k d) r → LE.le.{0} (Norm.norm.{0} (nu k d r)) 1) →
        (∀ (k : K), Membership.mem.{u_1, u_1} rows k → LE.le.{0} (↑(Finset.card.{u_2} (outer k))) DeltaD) →
          (∀ (k : K),
              Membership.mem.{u_1, u_1} rows k →
                ∀ (d : D),
                  Membership.mem.{u_2, u_2} (outer k) d → LE.le.{0} (↑(Finset.card.{u_3} (inner k d))) DeltaR) →
            LE.le.{0}
              (∑ k ∈ rows,
                HPow.hPow.{0, 0, 0}
                  (Norm.norm.{0}
                    (∑ d ∈ outer k,
                      HMul.hMul.{0, 0, 0} (mu k d) (∑ r ∈ inner k d, HMul.hMul.{0, 0, 0} (nu k d r) (value k d r))))
                  2)
              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} DeltaD DeltaR)
                (∑ k ∈ rows, ∑ d ∈ outer k, ∑ r ∈ inner k d, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (value k d r)) 2))
```

## HeckeSkeleton.LowHybrid.weighted_column_mass_mono

```lean
∀ {D : Type u_1} {Q : Type u_2} (blocks : Finset.{u_1} D) (columns : D → Finset.{u_2} Q) (weight : D → ℝ)
  (normQ : Q → ℝ) (a b : D → Q → ℂ),
  (∀ (d : D), Membership.mem.{u_1, u_1} blocks d → LE.le.{0} 0 (weight d)) →
    (∀ (d : D),
        Membership.mem.{u_1, u_1} blocks d →
          ∀ (q : Q), Membership.mem.{u_2, u_2} (columns d) q → LE.le.{0} 0 (normQ q)) →
      (∀ (d : D),
          Membership.mem.{u_1, u_1} blocks d →
            ∀ (q : Q),
              Membership.mem.{u_2, u_2} (columns d) q → LE.le.{0} (Norm.norm.{0} (a d q)) (Norm.norm.{0} (b d q))) →
        LE.le.{0}
          (∑ d ∈ blocks,
            HMul.hMul.{0, 0, 0} (weight d)
              (∑ q ∈ columns d, HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a d q)) 2) (normQ q)))
          (∑ d ∈ blocks,
            HMul.hMul.{0, 0, 0} (weight d)
              (∑ q ∈ columns d, HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (b d q)) 2) (normQ q)))
```

## HeckeSkeleton.LowHybrid.weighted_cubic_total

```lean
∀ {T : Type u_1} {C : Type u_2} {M : Type u_3} {H : Type u_4} (ts : Finset.{u_1} T) (cs : Finset.{u_2} C)
  (ms : Finset.{u_3} M) (hs : Finset.{u_4} H) (wt : T → ℝ) (wh : H → ℝ) (E : T → H → M → C → ℝ) (R U : ℝ),
  LE.le.{0} 0 R →
    (∀ (t : T), Membership.mem.{u_1, u_1} ts t → LT.lt.{0} 0 (wt t)) →
      (∀ (h : H), Membership.mem.{u_4, u_4} hs h → LT.lt.{0} 0 (wh h)) →
        (∀ (t : T),
            Membership.mem.{u_1, u_1} ts t →
              ∀ (h : H), Membership.mem.{u_4, u_4} hs h → LE.le.{0} (∑ m ∈ ms, ∑ c ∈ cs, E t h m c) U) →
          LE.le.{0}
            (∑ t ∈ ts,
              ∑ c ∈ cs,
                ∑ m ∈ ms,
                  ∑ h ∈ hs, HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} R (HMul.hMul.{0, 0, 0} (wt t) (wh h))) (E t h m c))
            (HMul.hMul.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} R U) (∑ t ∈ ts, HDiv.hDiv.{0, 0, 0} 1 (wt t)))
              (∑ h ∈ hs, HDiv.hDiv.{0, 0, 0} 1 (wh h)))
```

## HeckeSkeleton.LowHybrid.weighted_energy_from_sieve_inputs

```lean
∀ {I : Type u_1} [inst : DecidableEq.{u_1 + 1} I] (normI : I → ℝ) (sf : I → Prop) (symbol : I → I → ℂ),
  HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_1} normI sf symbol →
    HeckeSkeleton.LowHybrid.CubicSieveInput.{u_1} normI sf symbol →
      ∀ (eps : ℝ),
        LT.lt.{0} 0 eps →
          ∃ C0,
            LT.lt.{0} 0 C0 ∧
              ∀ (K0 Y0 N0 L0 : ℝ),
                LE.le.{0} 1 K0 →
                  LE.le.{0} 1 Y0 →
                    LE.le.{0} 1 N0 →
                      LE.le.{0} 1 L0 →
                        ∀ (rows ts cs ms hs ps qset jset : Finset.{u_1} I)
                          (goodPairs goodMC : Finset.{u_1} (Prod.{u_1, u_1} I I))
                          (qprod cprod : Prod.{u_1, u_1} I I → I) (a : I → I → I → ℂ) (beta : I → I → I → I → ℂ)
                          (rowMask : I → I → ℂ) (wt wc wh : I → ℝ) (Dq Dc Rbudget A : ℝ),
                          LE.le.{0} 0 Dq →
                            LE.le.{0} 0 Dc →
                              LE.le.{0} 0 Rbudget →
                                LE.le.{0} 0 A →
                                  (∀ (k : I), Membership.mem.{u_1, u_1} rows k → sf k ∧ LE.le.{0} (normI k) K0) →
                                    (∀ (j : I), Membership.mem.{u_1, u_1} qset j → sf j ∧ LE.le.{0} (normI j) Y0) →
                                      (∀ (j : I), Membership.mem.{u_1, u_1} jset j → sf j ∧ LE.le.{0} (normI j) N0) →
                                        (∀ (p : I), Membership.mem.{u_1, u_1} ps p → sf p ∧ LE.le.{0} (normI p) L0) →
                                          goodPairs ⊆ SProd.sprod.{u_1, u_1, u_1} ms hs →
                                            goodMC ⊆ SProd.sprod.{u_1, u_1, u_1} ms cs →
                                              (∀ (x : Prod.{u_1, u_1} I I),
                                                  Membership.mem.{u_1, u_1} goodPairs x →
                                                    Membership.mem.{u_1, u_1} qset (qprod x)) →
                                                (∀ (j : I),
                                                    Membership.mem.{u_1, u_1} qset j →
                                                      LE.le.{0}
                                                        (↑(Finset.card.{u_1}
                                                            ({x ∈ goodPairs | Eq.{u_1 + 1} (qprod x) j})))
                                                        Dq) →
                                                  (∀ (x : Prod.{u_1, u_1} I I),
                                                      Membership.mem.{u_1, u_1} goodMC x →
                                                        Membership.mem.{u_1, u_1} jset (cprod x)) →
                                                    (∀ (j : I),
                                                        Membership.mem.{u_1, u_1} jset j →
                                                          LE.le.{0}
                                                            (↑(Finset.card.{u_1}
                                                                ({x ∈ goodMC | Eq.{u_1 + 1} (cprod x) j})))
                                                            Dc) →
                                                      (∀ (t : I), Membership.mem.{u_1, u_1} ts t → LT.lt.{0} 0 (wt t)) →
                                                        (∀ (c : I),
                                                            Membership.mem.{u_1, u_1} cs c → LT.lt.{0} 0 (wc c)) →
                                                          (∀ (h : I),
                                                              Membership.mem.{u_1, u_1} hs h → LT.lt.{0} 0 (wh h)) →
                                                            (∀ (k : I),
                                                                Membership.mem.{u_1, u_1} rows k →
                                                                  ∀ (t : I),
                                                                    Membership.mem.{u_1, u_1} ts t →
                                                                      LE.le.{0} (Norm.norm.{0} (rowMask k t)) 1) →
                                                              (∀ (t : I),
                                                                  Membership.mem.{u_1, u_1} ts t →
                                                                    ∀ (c : I),
                                                                      Membership.mem.{u_1, u_1} cs c →
                                                                        ∀ (m : I),
                                                                          Membership.mem.{u_1, u_1} ms m →
                                                                            ∀ (h : I),
                                                                              Membership.mem.{u_1, u_1} hs h →
                                                                                LE.le.{0}
                                                                                  (HMul.hMul.{0, 0, 0}
                                                                                    (HMul.hMul.{0, 0, 0} (wt t) (wc c))
                                                                                    (HPow.hPow.{0, 0, 0}
                                                                                      (Norm.norm.{0} (beta t c m h)) 2))
                                                                                  (HDiv.hDiv.{0, 0, 0} Rbudget
                                                                                    (HMul.hMul.{0, 0, 0} (wt t)
                                                                                      (wh h)))) →
                                                                (∀ (t : I),
                                                                    Membership.mem.{u_1, u_1} ts t →
                                                                      ∀ (h : I),
                                                                        Membership.mem.{u_1, u_1} hs h →
                                                                          LE.le.{0}
                                                                            (∑ p ∈ ps,
                                                                              HPow.hPow.{0, 0, 0}
                                                                                (Norm.norm.{0} (a t h p)) 2)
                                                                            A) →
                                                                  LE.le.{0}
                                                                    (∑ k ∈ rows,
                                                                      HPow.hPow.{0, 0, 0}
                                                                        (Norm.norm.{0}
                                                                          (∑ t ∈ ts,
                                                                            ∑ c ∈ cs,
                                                                              HMul.hMul.{0, 0, 0} (rowMask k t)
                                                                                (∑ m ∈ ms,
                                                                                  ∑ h ∈ hs,
                                                                                    HMul.hMul.{0, 0, 0}
                                                                                      (HeckeSkeleton.LowHybrid.zeroExtendedQuadratic.{u_1,
                                                                                          u_1, u_1, u_1}
                                                                                        goodPairs qprod
                                                                                        (fun k j =>
                                                                                          HPow.hPow.{0, 0, 0}
                                                                                            (symbol k j) 3)
                                                                                        k m h)
                                                                                      (HMul.hMul.{0, 0, 0}
                                                                                        (beta t c m h)
                                                                                        (∑ p ∈ ps,
                                                                                          HMul.hMul.{0, 0, 0} (a t h p)
                                                                                            (HeckeSkeleton.LowHybrid.zeroExtendedCubic.{u_1,
                                                                                                u_1, u_1, u_1}
                                                                                              goodMC cprod
                                                                                              (fun p j =>
                                                                                                HPow.hPow.{0, 0, 0}
                                                                                                  (symbol p j) (-2))
                                                                                              m c p))))))
                                                                        2)
                                                                    (HMul.hMul.{0, 0, 0}
                                                                      (HMul.hMul.{0, 0, 0}
                                                                        (HMul.hMul.{0, 0, 0}
                                                                          (HMul.hMul.{0, 0, 0}
                                                                            (HMul.hMul.{0, 0, 0}
                                                                              (HMul.hMul.{0, 0, 0}
                                                                                (HMul.hMul.{0, 0, 0}
                                                                                  (HMul.hMul.{0, 0, 0}
                                                                                    (HMul.hMul.{0, 0, 0}
                                                                                      (HMul.hMul.{0, 0, 0} C0
                                                                                        (HPow.hPow.{0, 0, 0}
                                                                                          (HMul.hMul.{0, 0, 0}
                                                                                            (HMul.hMul.{0, 0, 0}
                                                                                              (HMul.hMul.{0, 0, 0} K0
                                                                                                Y0)
                                                                                              N0)
                                                                                            L0)
                                                                                          eps))
                                                                                      (HAdd.hAdd.{0, 0, 0} K0 Y0))
                                                                                    Dq)
                                                                                  Dc)
                                                                                (HAdd.hAdd.{0, 0, 0}
                                                                                  (HAdd.hAdd.{0, 0, 0} N0 L0)
                                                                                  (HPow.hPow.{0, 0, 0}
                                                                                    (HMul.hMul.{0, 0, 0} N0 L0)
                                                                                    (2 / 3))))
                                                                              Rbudget)
                                                                            A)
                                                                          (HPow.hPow.{0, 0, 0}
                                                                            (∑ t ∈ ts, HDiv.hDiv.{0, 0, 0} 1 (wt t)) 2))
                                                                        (∑ c ∈ cs, HDiv.hDiv.{0, 0, 0} 1 (wc c)))
                                                                      (∑ h ∈ hs, HDiv.hDiv.{0, 0, 0} 1 (wh h)))
```

## HeckeSkeleton.LowHybrid.weighted_energy_of_two_sieves

```lean
∀ {K : Type u_1} {T : Type u_2} {C : Type u_3} {M : Type u_4} {H : Type u_5} {P : Type u_6} (rows : Finset.{u_1} K)
  (ts : Finset.{u_2} T) (cs : Finset.{u_3} C) (ms : Finset.{u_4} M) (hs : Finset.{u_5} H) (ps : Finset.{u_6} P)
  (q : K → M → H → ℂ) (chi : M → C → P → ℂ) (a : T → H → P → ℂ) (beta : T → C → M → H → ℂ) (rowMask : K → T → ℂ)
  (wt : T → ℝ) (wc : C → ℝ) (wh : H → ℝ) (Q S R A : ℝ),
  LE.le.{0} 0 Q →
    LE.le.{0} 0 S →
      LE.le.{0} 0 R →
        LE.le.{0} 0 A →
          (∀ (t : T), Membership.mem.{u_2, u_2} ts t → LT.lt.{0} 0 (wt t)) →
            (∀ (c : C), Membership.mem.{u_3, u_3} cs c → LT.lt.{0} 0 (wc c)) →
              (∀ (h : H), Membership.mem.{u_5, u_5} hs h → LT.lt.{0} 0 (wh h)) →
                (∀ (k : K),
                    Membership.mem.{u_1, u_1} rows k →
                      ∀ (t : T), Membership.mem.{u_2, u_2} ts t → LE.le.{0} (Norm.norm.{0} (rowMask k t)) 1) →
                  (∀ (t : T),
                      Membership.mem.{u_2, u_2} ts t →
                        ∀ (c : C),
                          Membership.mem.{u_3, u_3} cs c →
                            ∀ (m : M),
                              Membership.mem.{u_4, u_4} ms m →
                                ∀ (h : H),
                                  Membership.mem.{u_5, u_5} hs h →
                                    LE.le.{0}
                                      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (wt t) (wc c))
                                        (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (beta t c m h)) 2))
                                      (HDiv.hDiv.{0, 0, 0} R (HMul.hMul.{0, 0, 0} (wt t) (wh h)))) →
                    (∀ (t : T),
                        Membership.mem.{u_2, u_2} ts t →
                          ∀ (h : H),
                            Membership.mem.{u_5, u_5} hs h →
                              LE.le.{0} (∑ p ∈ ps, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a t h p)) 2) A) →
                      (∀ (f : M → H → ℂ),
                          LE.le.{0}
                            (∑ k ∈ rows,
                              HPow.hPow.{0, 0, 0}
                                (Norm.norm.{0} (∑ m ∈ ms, ∑ h ∈ hs, HMul.hMul.{0, 0, 0} (q k m h) (f m h))) 2)
                            (HMul.hMul.{0, 0, 0} Q
                              (∑ m ∈ ms, ∑ h ∈ hs, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (f m h)) 2))) →
                        (∀ (u : P → ℂ),
                            LE.le.{0}
                              (∑ m ∈ ms,
                                ∑ c ∈ cs,
                                  HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ p ∈ ps, HMul.hMul.{0, 0, 0} (u p) (chi m c p)))
                                    2)
                              (HMul.hMul.{0, 0, 0} S (∑ p ∈ ps, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (u p)) 2))) →
                          LE.le.{0}
                            (∑ k ∈ rows,
                              HPow.hPow.{0, 0, 0}
                                (Norm.norm.{0}
                                  (∑ t ∈ ts,
                                    ∑ c ∈ cs,
                                      HMul.hMul.{0, 0, 0} (rowMask k t)
                                        (∑ m ∈ ms,
                                          ∑ h ∈ hs,
                                            HMul.hMul.{0, 0, 0} (q k m h)
                                              (HMul.hMul.{0, 0, 0} (beta t c m h)
                                                (∑ p ∈ ps, HMul.hMul.{0, 0, 0} (a t h p) (chi m c p))))))
                                2)
                            (HMul.hMul.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} Q S) R) A)
                                  (HPow.hPow.{0, 0, 0} (∑ t ∈ ts, HDiv.hDiv.{0, 0, 0} 1 (wt t)) 2))
                                (∑ c ∈ cs, HDiv.hDiv.{0, 0, 0} 1 (wc c)))
                              (∑ h ∈ hs, HDiv.hDiv.{0, 0, 0} 1 (wh h)))
```

## HeckeSkeleton.LowHybrid.weighted_mixture_energy

```lean
∀ {K : Type u_1} {I : Type u_2} (rows : Finset.{u_1} K) (s : Finset.{u_2} I) (w : I → ℝ) (F : I → K → ℂ)
  (E : I → ℝ),
  (∀ (i : I), Membership.mem.{u_2, u_2} s i → LT.lt.{0} 0 (w i)) →
    (∀ (i : I),
        Membership.mem.{u_2, u_2} s i →
          LE.le.{0} (HMul.hMul.{0, 0, 0} (w i) (∑ k ∈ rows, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (F i k)) 2)) (E i)) →
      LE.le.{0} (∑ k ∈ rows, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ i ∈ s, F i k)) 2)
        (HMul.hMul.{0, 0, 0} (∑ i ∈ s, HDiv.hDiv.{0, 0, 0} 1 (w i)) (∑ i ∈ s, E i))
```

## HeckeSkeleton.LowHybrid.weighted_positive_fiber_sum_le

```lean
∀ {X : Type u_1} {Y : Type u_2} [inst : DecidableEq.{u_2 + 1} Y] (source : Finset.{u_1} X)
  (target : Finset.{u_2} Y) (phi : X → Y) (weight : X → ℝ) (E : Y → ℝ) (W : ℝ),
  (∀ (x : X), Membership.mem.{u_1, u_1} source x → Membership.mem.{u_2, u_2} target (phi x)) →
    (∀ (y : Y), Membership.mem.{u_2, u_2} target y → LE.le.{0} 0 (E y)) →
      (∀ (y : Y),
          Membership.mem.{u_2, u_2} target y → LE.le.{0} (∑ x ∈ source with Eq.{u_2 + 1} (phi x) y, weight x) W) →
        LE.le.{0} (∑ x ∈ source, HMul.hMul.{0, 0, 0} (weight x) (E (phi x))) (HMul.hMul.{0, 0, 0} W (∑ y ∈ target, E y))
```

## HeckeSkeleton.LowHybrid.weighted_row_fiber_sieve

```lean
∀ {X : Type u_1} {Y : Type u_2} {P : Type u_3} [inst : DecidableEq.{u_2 + 1} Y] (source : Finset.{u_1} X)
  (target : Finset.{u_2} Y) (columns : Finset.{u_3} P) (phi : X → Y) (chi : P → Y → ℂ) (a : P → ℂ) (beta : X → ℂ)
  (W S : ℝ),
  LE.le.{0} 0 W →
    (∀ (x : X), Membership.mem.{u_1, u_1} source x → Membership.mem.{u_2, u_2} target (phi x)) →
      (∀ (y : Y),
          Membership.mem.{u_2, u_2} target y →
            LE.le.{0} (∑ x ∈ source with Eq.{u_2 + 1} (phi x) y, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (beta x)) 2) W) →
        (∀ (u : P → ℂ),
            LE.le.{0}
              (∑ y ∈ target, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ p ∈ columns, HMul.hMul.{0, 0, 0} (u p) (chi p y))) 2)
              (HMul.hMul.{0, 0, 0} S (∑ p ∈ columns, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (u p)) 2))) →
          LE.le.{0}
            (∑ x ∈ source,
              HPow.hPow.{0, 0, 0}
                (Norm.norm.{0}
                  (HMul.hMul.{0, 0, 0} (beta x) (∑ p ∈ columns, HMul.hMul.{0, 0, 0} (a p) (chi p (phi x)))))
                2)
            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} W S) (∑ p ∈ columns, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a p)) 2))
```

## HeckeSkeleton.LowHybrid.weighted_sum_sq

```lean
∀ {I : Type u_1} (s : Finset.{u_1} I) (w : I → ℝ) (f : I → ℂ),
  (∀ (i : I), Membership.mem.{u_1, u_1} s i → LT.lt.{0} 0 (w i)) →
    LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ i ∈ s, f i)) 2)
      (HMul.hMul.{0, 0, 0} (∑ i ∈ s, HDiv.hDiv.{0, 0, 0} 1 (w i))
        (∑ i ∈ s, HMul.hMul.{0, 0, 0} (w i) (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (f i)) 2)))
```

## HeckeSkeleton.LowHybrid.zero_extended_column_fiber_sieve

```lean
∀ {K : Type u_1} {M : Type u_2} {H : Type u_3} {J : Type u_4} [inst : DecidableEq.{u_2 + 1} M]
  [inst_1 : DecidableEq.{u_3 + 1} H] [inst_2 : DecidableEq.{u_4 + 1} J] (rows : Finset.{u_1} K) (ms : Finset.{u_2} M)
  (hs : Finset.{u_3} H) (good : Finset.{max u_3 u_2} (Prod.{u_2, u_3} M H)) (target : Finset.{u_4} J)
  (phi : Prod.{u_2, u_3} M H → J) (q : K → J → ℂ) (Q D : ℝ),
  LE.le.{0} 0 Q →
    LE.le.{0} 0 D →
      good ⊆ SProd.sprod.{u_2, u_3, max u_2 u_3} ms hs →
        (∀ (x : Prod.{u_2, u_3} M H),
            Membership.mem.{max u_2 u_3, max u_2 u_3} good x → Membership.mem.{u_4, u_4} target (phi x)) →
          (∀ (j : J),
              Membership.mem.{u_4, u_4} target j →
                LE.le.{0} (↑(Finset.card.{max u_2 u_3} ({x ∈ good | Eq.{u_4 + 1} (phi x) j}))) D) →
            (∀ (z : J → ℂ),
                LE.le.{0}
                  (∑ k ∈ rows, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ j ∈ target, HMul.hMul.{0, 0, 0} (q k j) (z j))) 2)
                  (HMul.hMul.{0, 0, 0} Q (∑ j ∈ target, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (z j)) 2))) →
              ∀ (f : M → H → ℂ),
                LE.le.{0}
                  (∑ k ∈ rows,
                    HPow.hPow.{0, 0, 0}
                      (Norm.norm.{0}
                        (∑ m ∈ ms,
                          ∑ h ∈ hs,
                            HMul.hMul.{0, 0, 0}
                              (HeckeSkeleton.LowHybrid.zeroExtendedQuadratic.{u_1, u_2, u_3, u_4} good phi q k m h)
                              (f m h)))
                      2)
                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} Q D)
                    (∑ m ∈ ms, ∑ h ∈ hs, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (f m h)) 2))
```

## HeckeSkeleton.LowHybrid.zero_extended_row_fiber_sieve

```lean
∀ {M : Type u_1} {C : Type u_2} {J : Type u_3} {P : Type u_4} [inst : DecidableEq.{u_1 + 1} M]
  [inst_1 : DecidableEq.{u_2 + 1} C] [inst_2 : DecidableEq.{u_3 + 1} J] (ms : Finset.{u_1} M) (cs : Finset.{u_2} C)
  (good : Finset.{max u_2 u_1} (Prod.{u_1, u_2} M C)) (target : Finset.{u_3} J) (columns : Finset.{u_4} P)
  (phi : Prod.{u_1, u_2} M C → J) (chi : P → J → ℂ) (S D : ℝ),
  LE.le.{0} 0 D →
    good ⊆ SProd.sprod.{u_1, u_2, max u_1 u_2} ms cs →
      (∀ (x : Prod.{u_1, u_2} M C),
          Membership.mem.{max u_1 u_2, max u_1 u_2} good x → Membership.mem.{u_3, u_3} target (phi x)) →
        (∀ (j : J),
            Membership.mem.{u_3, u_3} target j →
              LE.le.{0} (↑(Finset.card.{max u_1 u_2} ({x ∈ good | Eq.{u_3 + 1} (phi x) j}))) D) →
          (∀ (z : P → ℂ),
              LE.le.{0}
                (∑ j ∈ target,
                  HPow.hPow.{0, 0, 0} (Norm.norm.{0} (∑ p ∈ columns, HMul.hMul.{0, 0, 0} (z p) (chi p j))) 2)
                (HMul.hMul.{0, 0, 0} S (∑ p ∈ columns, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (z p)) 2))) →
            ∀ (a : P → ℂ),
              LE.le.{0}
                (∑ m ∈ ms,
                  ∑ c ∈ cs,
                    HPow.hPow.{0, 0, 0}
                      (Norm.norm.{0}
                        (∑ p ∈ columns,
                          HMul.hMul.{0, 0, 0} (a p)
                            (HeckeSkeleton.LowHybrid.zeroExtendedCubic.{u_1, u_2, u_3, u_4} good phi chi m c p)))
                      2)
                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} S D)
                  (∑ p ∈ columns, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a p)) 2))
```

## HeckeSkeleton.LowHybrid.sum_tcmh_swap

内部名称：`_private.HeckeSkeleton.LowHybrid.Weighted.0.HeckeSkeleton.LowHybrid.sum_tcmh_swap`。

```lean
∀ {T : Type u_1} {C : Type u_2} {M : Type u_3} {H : Type u_4} (ts : Finset.{u_1} T) (cs : Finset.{u_2} C)
  (ms : Finset.{u_3} M) (hs : Finset.{u_4} H) (f : T → C → M → H → ℝ),
  Eq.{1} (∑ t ∈ ts, ∑ c ∈ cs, ∑ m ∈ ms, ∑ h ∈ hs, f t c m h) (∑ t ∈ ts, ∑ h ∈ hs, ∑ m ∈ ms, ∑ c ∈ cs, f t c m h)
```

## HeckeSkeleton.LowHybrid.sum_zero_extension

内部名称：`_private.HeckeSkeleton.LowHybrid.WeightedSieveBounds.0.HeckeSkeleton.LowHybrid.sum_zero_extension`。

```lean
∀ {X : Type u_1} {A : Type u_2} [inst : DecidableEq.{u_1 + 1} X] [inst_1 : AddCommMonoid.{u_2} A]
  (ambient good : Finset.{u_1} X) (f : X → A),
  good ⊆ ambient →
    Eq.{u_2 + 1} (∑ x ∈ ambient, ite.{u_2 + 1} (Membership.mem.{u_1, u_1} good x) (f x) 0) (∑ x ∈ good, f x)
```

## HeckeSkeleton.LowFrozenCube.AdmissibleExponent.eq_1

```lean
∀ (e : ℕ),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.AdmissibleExponent e)
    (Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 0 ∨ Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 1)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.annularColumn_eq_scalar_unit

```lean
∀ {A : Type u_2} [CommMonoid.{u_2} A] (normI : A → ℝ) (N : ℝ),
  LT.lt.{0} 0 N →
    ∀ (lam : A → ℂ) (c : A),
      Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.annularColumn.{u_2} normI lam c)
        (HMul.hMul.{0, 0, 0} (Inv.inv.{0} ↑√N)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.unitAnnularColumn.{u_2} normI N lam c))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.dyadic_coefficient_scale

```lean
∀ (C N B : ℝ),
  LT.lt.{0} 0 N →
    LT.lt.{0} 0 B →
      Eq.{1}
        (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} C (HDiv.hDiv.{0, 0, 0} B 2)) 2)
          (HDiv.hDiv.{0, 0, 0} N 2))
        (HMul.hMul.{0, 0, 0} 8 (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} C B) 2) N))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.four_scale_power

```lean
∀ (Z H v ell z eps : ℝ),
  LT.lt.{0} 0 Z →
    Eq.{1}
      (HPow.hPow.{0, 0, 0}
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z H) (HPow.hPow.{0, 0, 0} Z v))
            (HPow.hPow.{0, 0, 0} Z ell))
          (HPow.hPow.{0, 0, 0} Z z))
        eps)
      (HPow.hPow.{0, 0, 0} Z
        (HMul.hMul.{0, 0, 0} eps (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} H v) ell) z)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.inv_sqrt_norm_sq

```lean
∀ (N : ℝ),
  LT.lt.{0} 0 N → Eq.{1} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (Inv.inv.{0} ↑√N)) 2) (HDiv.hDiv.{0, 0, 0} 1 N)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.uniform_aggregate_source_energy_ledger

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (symbol : A → MonoidHom.{u_2, 0} A ℂ),
  (∀ (a b c : A),
      Eq.{1} ((symbol (HMul.hMul.{u_2, u_2, u_2} a b)) c) (HMul.hMul.{0, 0, 0} ((symbol a) c) ((symbol b) c))) →
    (∀ (a b : A),
        Eq.{1} (HPow.hPow.{0, 0, 0} ((symbol a) b) 6)
          (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
      ∀ (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
        (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
          (∀ (a : A), LE.le.{0} 1 (q a)) →
            ∀ (Ccount : ℝ),
              LT.lt.{0} 0 Ccount →
                HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
                  (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b => (symbol a) b) →
                    (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                        (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b =>
                        (symbol a) b) →
                      ∀ (eps eta : ℝ),
                        LT.lt.{0} 0 eps →
                          LT.lt.{0} 0 eta →
                            ∃ C,
                              LT.lt.{0} 0 C ∧
                                ∀ (Z O H v ell S B z T Rrad : ℝ),
                                  LE.le.{0} 1 Z →
                                    LE.le.{0} 0 O →
                                      LE.le.{0} 0 H →
                                        LE.le.{0} 0 v →
                                          LE.le.{0} 0 ell →
                                            LE.le.{0} 0 z →
                                              ∀ (base : Finset.{u_1} ι) (rows : Finset.{u_2} A),
                                                (∀ (k : A),
                                                    Membership.mem.{u_2, u_2} rows k →
                                                      LE.le.{0}
                                                        (normI
                                                          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1,
                                                              u_2}
                                                            coords k))
                                                        (HPow.hPow.{0, 0, 0} Z O)) →
                                                  LE.le.{0}
                                                      (normI
                                                        (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2}
                                                          coords base))
                                                      (HPow.hPow.{0, 0, 0} Z Rrad) →
                                                    ∀
                                                      (data :
                                                        Prod.{u_2, u_2} A A →
                                                          HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι
                                                            A)
                                                      (family :
                                                        Prod.{u_2, u_2} A A →
                                                          HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1,
                                                              u_2}
                                                            ι A),
                                                      (∀ (pair : Prod.{u_2, u_2} A A),
                                                          Membership.mem.{u_2, u_2}
                                                              (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2}
                                                                coords base rows)
                                                              pair →
                                                            Eq.{max (u_1 + 1) (u_2 + 1)}
                                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                                  u_2}
                                                                (data pair))
                                                              coords) →
                                                        (∀ (pair : Prod.{u_2, u_2} A A),
                                                            Membership.mem.{u_2, u_2}
                                                                (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2}
                                                                  coords base rows)
                                                                pair →
                                                              Eq.{u_2 + 1}
                                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1,
                                                                    u_2}
                                                                  (data pair))
                                                                symbol) →
                                                          ∀
                                                            (a :
                                                              (pair : Prod.{u_2, u_2} A A) →
                                                                Membership.mem.{u_2, u_2}
                                                                    (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                        u_2}
                                                                      coords base rows)
                                                                    pair →
                                                                  HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1,
                                                                      u_2}
                                                                    (data pair) (⇑normI) Z H v ell z (family pair)),
                                                            (∀ (pair : Prod.{u_2, u_2} A A),
                                                                Membership.mem.{u_2, u_2}
                                                                    (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                        u_2}
                                                                      coords base rows)
                                                                    pair →
                                                                  HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.{u_1,
                                                                      u_2}
                                                                    (data pair) (⇑normI) (family pair)) →
                                                              (∀ (pair : Prod.{u_2, u_2} A A),
                                                                  Membership.mem.{u_2, u_2}
                                                                      (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                          u_2}
                                                                        coords base rows)
                                                                      pair →
                                                                    LE.le.{0}
                                                                      (HPow.hPow.{0, 0, 0} Z (HAdd.hAdd.{0, 0, 0} S B))
                                                                      (normI
                                                                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.{u_1,
                                                                            u_2}
                                                                          (data pair)))) →
                                                                LE.le.{0}
                                                                  (HMul.hMul.{0, 0, 0}
                                                                    (∑
                                                                      pair ∈
                                                                        HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                            u_2}
                                                                          coords base rows,
                                                                      HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.energy.{u_1,
                                                                          u_2}
                                                                        (family pair) (data pair) ⇑normI)
                                                                    (HPow.hPow.{0, 0, 0} Z
                                                                      (HeckeSkeleton.LowFrozenCube.squaredKernelExponent
                                                                        T v ell)))
                                                                  (HMul.hMul.{0, 0, 0} C
                                                                    (HPow.hPow.{0, 0, 0} Z
                                                                      (HAdd.hAdd.{0, 0, 0}
                                                                        (HAdd.hAdd.{0, 0, 0}
                                                                          (HeckeSkeleton.LowFrozenCube.reflectedExponent
                                                                            O H v ell S B z T)
                                                                          (HMul.hMul.{0, 0, 0} eps
                                                                            (HAdd.hAdd.{0, 0, 0}
                                                                              (HAdd.hAdd.{0, 0, 0}
                                                                                (HAdd.hAdd.{0, 0, 0} H v) ell)
                                                                              z)))
                                                                        (HMul.hMul.{0, 0, 0} eta
                                                                          (HAdd.hAdd.{0, 0, 0} O Rrad)))))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.uniform_family_source_energy_ledger

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (symbol : A → MonoidHom.{u_2, 0} A ℂ),
  (∀ (a b c : A),
      Eq.{1} ((symbol (HMul.hMul.{u_2, u_2, u_2} a b)) c) (HMul.hMul.{0, 0, 0} ((symbol a) c) ((symbol b) c))) →
    (∀ (a b : A),
        Eq.{1} (HPow.hPow.{0, 0, 0} ((symbol a) b) 6)
          (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
      ∀ (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
        (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
          (∀ (a : A), LE.le.{0} 1 (q a)) →
            ∀ (Ccount : ℝ),
              LT.lt.{0} 0 Ccount →
                HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
                  (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b => (symbol a) b) →
                    (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                        (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b =>
                        (symbol a) b) →
                      ∀ (eps eta : ℝ),
                        LT.lt.{0} 0 eps →
                          LT.lt.{0} 0 eta →
                            ∃ C,
                              LT.lt.{0} 0 C ∧
                                ∀ (Z O H v ell S B z T Rrad : ℝ),
                                  LE.le.{0} 1 Z →
                                    LE.le.{0} 0 O →
                                      LE.le.{0} 0 H →
                                        LE.le.{0} 0 v →
                                          LE.le.{0} 0 ell →
                                            LE.le.{0} 0 z →
                                              ∀ (base : Finset.{u_1} ι) (rows : Finset.{u_2} A),
                                                (∀ (k : A),
                                                    Membership.mem.{u_2, u_2} rows k →
                                                      LE.le.{0}
                                                        (normI
                                                          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1,
                                                              u_2}
                                                            coords k))
                                                        (HPow.hPow.{0, 0, 0} Z O)) →
                                                  LE.le.{0}
                                                      (normI
                                                        (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2}
                                                          coords base))
                                                      (HPow.hPow.{0, 0, 0} Z Rrad) →
                                                    ∀
                                                      (data :
                                                        Prod.{u_2, u_2} A A →
                                                          HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι
                                                            A)
                                                      (family :
                                                        Prod.{u_2, u_2} A A →
                                                          HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1,
                                                              u_2}
                                                            ι A),
                                                      HeckeSkeleton.LowFrozenCube.FrozenReduction.FrozenFamilyAlignment.{u_1,
                                                            u_2}
                                                          coords base rows data family →
                                                        (∀ (pair : Prod.{u_2, u_2} A A),
                                                            Membership.mem.{u_2, u_2}
                                                                (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2}
                                                                  coords base rows)
                                                                pair →
                                                              Eq.{u_2 + 1}
                                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1,
                                                                    u_2}
                                                                  (data pair))
                                                                symbol) →
                                                          ∀
                                                            (a :
                                                              (pair : Prod.{u_2, u_2} A A) →
                                                                Membership.mem.{u_2, u_2}
                                                                    (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                        u_2}
                                                                      coords base rows)
                                                                    pair →
                                                                  HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1,
                                                                      u_2}
                                                                    (data pair) (⇑normI) Z H v ell z (family pair)),
                                                            (∀ (pair : Prod.{u_2, u_2} A A),
                                                                Membership.mem.{u_2, u_2}
                                                                    (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                        u_2}
                                                                      coords base rows)
                                                                    pair →
                                                                  HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.{u_1,
                                                                      u_2}
                                                                    (data pair) (⇑normI) (family pair)) →
                                                              (∀ (pair : Prod.{u_2, u_2} A A),
                                                                  Membership.mem.{u_2, u_2}
                                                                      (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                          u_2}
                                                                        coords base rows)
                                                                      pair →
                                                                    LE.le.{0}
                                                                      (HPow.hPow.{0, 0, 0} Z (HAdd.hAdd.{0, 0, 0} S B))
                                                                      (normI
                                                                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.{u_1,
                                                                            u_2}
                                                                          (data pair)))) →
                                                                LE.le.{0}
                                                                  (HMul.hMul.{0, 0, 0}
                                                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.varyingFamilySourceEnergy.{u_1,
                                                                        u_2}
                                                                      coords base (⇑normI) data family rows)
                                                                    (HPow.hPow.{0, 0, 0} Z
                                                                      (HeckeSkeleton.LowFrozenCube.squaredKernelExponent
                                                                        T v ell)))
                                                                  (HMul.hMul.{0, 0, 0} C
                                                                    (HPow.hPow.{0, 0, 0} Z
                                                                      (HAdd.hAdd.{0, 0, 0}
                                                                        (HAdd.hAdd.{0, 0, 0}
                                                                          (HeckeSkeleton.LowFrozenCube.reflectedExponent
                                                                            O H v ell S B z T)
                                                                          (HMul.hMul.{0, 0, 0} eps
                                                                            (HAdd.hAdd.{0, 0, 0}
                                                                              (HAdd.hAdd.{0, 0, 0}
                                                                                (HAdd.hAdd.{0, 0, 0} H v) ell)
                                                                              z)))
                                                                        (HMul.hMul.{0, 0, 0} eta
                                                                          (HAdd.hAdd.{0, 0, 0} O Rrad)))))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.uniform_family_source_energy_power_saving

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (symbol : A → MonoidHom.{u_2, 0} A ℂ),
  (∀ (a b c : A),
      Eq.{1} ((symbol (HMul.hMul.{u_2, u_2, u_2} a b)) c) (HMul.hMul.{0, 0, 0} ((symbol a) c) ((symbol b) c))) →
    (∀ (a b : A),
        Eq.{1} (HPow.hPow.{0, 0, 0} ((symbol a) b) 6)
          (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
      ∀ (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
        (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
          ∀ (Ccount : ℝ),
            HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
              (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                  (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b => (symbol a) b) →
                (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                    (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b => (symbol a) b) →
                  ∀ (W eps : ℝ),
                    LT.lt.{0} 0 W →
                      LT.lt.{0} 0 eps →
                        ∃ C,
                          LT.lt.{0} 0 C ∧
                            ∀ (Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau Rrad : ℝ),
                              LE.le.{0} 1 Z →
                                LE.le.{0} 0 H →
                                  LE.le.{0} 0 O →
                                    LE.le.{0} 0 S →
                                      LE.le.{0} 0 B →
                                        LE.le.{0} 0 ell →
                                          LE.le.{0} 0 v →
                                            LE.le.{0} 0 z →
                                              LE.le.{0} 0 Q →
                                                LE.le.{0} 0 M →
                                                  LE.le.{0} 0 c →
                                                    Eq.{1} F (HAdd.hAdd.{0, 0, 0} N V) →
                                                      Eq.{1} Nstar (HSub.hSub.{0, 0, 0} N (HMul.hMul.{0, 0, 0} 3 bh)) →
                                                        LE.le.{0} V delta →
                                                          LE.le.{0} bh delta →
                                                            LE.le.{0} z z0 →
                                                              LE.le.{0} H (HSub.hSub.{0, 0, 0} M O) →
                                                                LE.le.{0} c
                                                                    (HSub.hSub.{0, 0, 0}
                                                                      (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} F M) Q)
                                                                      z0) →
                                                                  LE.le.{0} c
                                                                      (HSub.hSub.{0, 0, 0}
                                                                        (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} 4 F)
                                                                          (HMul.hMul.{0, 0, 0} 3 M))
                                                                        (HMul.hMul.{0, 0, 0} 6 z0)) →
                                                                    LE.le.{0}
                                                                        (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} T S)
                                                                          B)
                                                                        (HAdd.hAdd.{0, 0, 0}
                                                                          (HSub.hSub.{0, 0, 0}
                                                                            (HAdd.hAdd.{0, 0, 0}
                                                                              (HAdd.hAdd.{0, 0, 0}
                                                                                (HSub.hSub.{0, 0, 0}
                                                                                  (HMul.hMul.{0, 0, 0} 2 M) O)
                                                                                Q)
                                                                              V)
                                                                            Nstar)
                                                                          (HMul.hMul.{0, 0, 0} 2 z)) →
                                                                      LE.le.{0}
                                                                          (HAdd.hAdd.{0, 0, 0} v
                                                                            (HMul.hMul.{0, 0, 0} 3 ell))
                                                                          (HAdd.hAdd.{0, 0, 0} T tau) →
                                                                        LE.le.{0} delta (HDiv.hDiv.{0, 0, 0} c 100) →
                                                                          LE.le.{0} tau (HDiv.hDiv.{0, 0, 0} c 8) →
                                                                            LE.le.{0} eps (HDiv.hDiv.{0, 0, 0} c 4) →
                                                                              LE.le.{0}
                                                                                  (HAdd.hAdd.{0, 0, 0}
                                                                                    (HAdd.hAdd.{0, 0, 0}
                                                                                      (HAdd.hAdd.{0, 0, 0}
                                                                                        (HAdd.hAdd.{0, 0, 0} H v) ell)
                                                                                      z)
                                                                                    (HAdd.hAdd.{0, 0, 0} O Rrad))
                                                                                  W →
                                                                                ∀ (base : Finset.{u_1} ι)
                                                                                  (rows : Finset.{u_2} A),
                                                                                  (∀ (k : A),
                                                                                      Membership.mem.{u_2, u_2} rows k →
                                                                                        LE.le.{0}
                                                                                          (normI
                                                                                            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1,
                                                                                                u_2}
                                                                                              coords k))
                                                                                          (HPow.hPow.{0, 0, 0} Z O)) →
                                                                                    LE.le.{0}
                                                                                        (normI
                                                                                          (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1,
                                                                                              u_2}
                                                                                            coords base))
                                                                                        (HPow.hPow.{0, 0, 0} Z Rrad) →
                                                                                      ∀
                                                                                        (data :
                                                                                          Prod.{u_2, u_2} A A →
                                                                                            HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1,
                                                                                                u_2}
                                                                                              ι A)
                                                                                        (family :
                                                                                          Prod.{u_2, u_2} A A →
                                                                                            HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1,
                                                                                                u_2}
                                                                                              ι A),
                                                                                        HeckeSkeleton.LowFrozenCube.FrozenReduction.FrozenFamilyAlignment.{u_1,
                                                                                              u_2}
                                                                                            coords base rows data
                                                                                            family →
                                                                                          (∀
                                                                                              (pair :
                                                                                                Prod.{u_2, u_2} A A),
                                                                                              Membership.mem.{u_2, u_2}
                                                                                                  (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                                                      u_2}
                                                                                                    coords base rows)
                                                                                                  pair →
                                                                                                Eq.{u_2 + 1}
                                                                                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1,
                                                                                                      u_2}
                                                                                                    (data pair))
                                                                                                  symbol) →
                                                                                            ∀
                                                                                              (a :
                                                                                                (pair :
                                                                                                    Prod.{u_2, u_2} A
                                                                                                      A) →
                                                                                                  Membership.mem.{u_2,
                                                                                                        u_2}
                                                                                                      (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                                                          u_2}
                                                                                                        coords base
                                                                                                        rows)
                                                                                                      pair →
                                                                                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1,
                                                                                                        u_2}
                                                                                                      (data pair)
                                                                                                      (⇑normI) Z H v ell
                                                                                                      z (family pair)),
                                                                                              (∀
                                                                                                  (pair :
                                                                                                    Prod.{u_2, u_2} A
                                                                                                      A),
                                                                                                  Membership.mem.{u_2,
                                                                                                        u_2}
                                                                                                      (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                                                          u_2}
                                                                                                        coords base
                                                                                                        rows)
                                                                                                      pair →
                                                                                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.{u_1,
                                                                                                        u_2}
                                                                                                      (data pair)
                                                                                                      (⇑normI)
                                                                                                      (family pair)) →
                                                                                                (∀
                                                                                                    (pair :
                                                                                                      Prod.{u_2, u_2} A
                                                                                                        A),
                                                                                                    Membership.mem.{u_2,
                                                                                                          u_2}
                                                                                                        (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                                                            u_2}
                                                                                                          coords base
                                                                                                          rows)
                                                                                                        pair →
                                                                                                      LE.le.{0}
                                                                                                        (HPow.hPow.{0,
                                                                                                            0, 0}
                                                                                                          Z
                                                                                                          (HAdd.hAdd.{0,
                                                                                                              0, 0}
                                                                                                            S B))
                                                                                                        (normI
                                                                                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.{u_1,
                                                                                                              u_2}
                                                                                                            (data
                                                                                                              pair)))) →
                                                                                                  LE.le.{0}
                                                                                                    (HMul.hMul.{0, 0, 0}
                                                                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.varyingFamilySourceEnergy.{u_1,
                                                                                                          u_2}
                                                                                                        coords base
                                                                                                        (⇑normI) data
                                                                                                        family rows)
                                                                                                      (HPow.hPow.{0, 0,
                                                                                                          0}
                                                                                                        Z
                                                                                                        (HeckeSkeleton.LowFrozenCube.squaredKernelExponent
                                                                                                          T v ell)))
                                                                                                    (HMul.hMul.{0, 0, 0}
                                                                                                      C
                                                                                                      (HPow.hPow.{0, 0,
                                                                                                          0}
                                                                                                        Z
                                                                                                        (HSub.hSub.{0,
                                                                                                            0, 0}
                                                                                                          F
                                                                                                          (HDiv.hDiv.{0,
                                                                                                              0, 0}
                                                                                                            c 4))))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.uniform_family_source_energy_subpower

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (symbol : A → MonoidHom.{u_2, 0} A ℂ),
  (∀ (a b c : A),
      Eq.{1} ((symbol (HMul.hMul.{u_2, u_2, u_2} a b)) c) (HMul.hMul.{0, 0, 0} ((symbol a) c) ((symbol b) c))) →
    (∀ (a b : A),
        Eq.{1} (HPow.hPow.{0, 0, 0} ((symbol a) b) 6)
          (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
      ∀ (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
        (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
          ∀ (Ccount : ℝ),
            HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
              (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                  (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b => (symbol a) b) →
                (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                    (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b => (symbol a) b) →
                  ∀ (W eps : ℝ),
                    LT.lt.{0} 0 W →
                      LT.lt.{0} 0 eps →
                        ∃ C,
                          LT.lt.{0} 0 C ∧
                            ∀ (Z O H v ell S B z T Rrad : ℝ),
                              LE.le.{0} 1 Z →
                                LE.le.{0} 0 O →
                                  LE.le.{0} 0 H →
                                    LE.le.{0} 0 v →
                                      LE.le.{0} 0 ell →
                                        LE.le.{0} 0 z →
                                          LE.le.{0}
                                              (HAdd.hAdd.{0, 0, 0}
                                                (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} H v) ell)
                                                  z)
                                                (HAdd.hAdd.{0, 0, 0} O Rrad))
                                              W →
                                            ∀ (base : Finset.{u_1} ι) (rows : Finset.{u_2} A),
                                              (∀ (k : A),
                                                  Membership.mem.{u_2, u_2} rows k →
                                                    LE.le.{0}
                                                      (normI
                                                        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1,
                                                            u_2}
                                                          coords k))
                                                      (HPow.hPow.{0, 0, 0} Z O)) →
                                                LE.le.{0}
                                                    (normI
                                                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2}
                                                        coords base))
                                                    (HPow.hPow.{0, 0, 0} Z Rrad) →
                                                  ∀
                                                    (data :
                                                      Prod.{u_2, u_2} A A →
                                                        HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A)
                                                    (family :
                                                      Prod.{u_2, u_2} A A →
                                                        HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1,
                                                            u_2}
                                                          ι A),
                                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.FrozenFamilyAlignment.{u_1,
                                                          u_2}
                                                        coords base rows data family →
                                                      (∀ (pair : Prod.{u_2, u_2} A A),
                                                          Membership.mem.{u_2, u_2}
                                                              (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2}
                                                                coords base rows)
                                                              pair →
                                                            Eq.{u_2 + 1}
                                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1,
                                                                  u_2}
                                                                (data pair))
                                                              symbol) →
                                                        ∀
                                                          (a :
                                                            (pair : Prod.{u_2, u_2} A A) →
                                                              Membership.mem.{u_2, u_2}
                                                                  (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2}
                                                                    coords base rows)
                                                                  pair →
                                                                HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1,
                                                                    u_2}
                                                                  (data pair) (⇑normI) Z H v ell z (family pair)),
                                                          (∀ (pair : Prod.{u_2, u_2} A A),
                                                              Membership.mem.{u_2, u_2}
                                                                  (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2}
                                                                    coords base rows)
                                                                  pair →
                                                                HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.{u_1,
                                                                    u_2}
                                                                  (data pair) (⇑normI) (family pair)) →
                                                            (∀ (pair : Prod.{u_2, u_2} A A),
                                                                Membership.mem.{u_2, u_2}
                                                                    (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                        u_2}
                                                                      coords base rows)
                                                                    pair →
                                                                  LE.le.{0}
                                                                    (HPow.hPow.{0, 0, 0} Z (HAdd.hAdd.{0, 0, 0} S B))
                                                                    (normI
                                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.{u_1,
                                                                          u_2}
                                                                        (data pair)))) →
                                                              LE.le.{0}
                                                                (HMul.hMul.{0, 0, 0}
                                                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.varyingFamilySourceEnergy.{u_1,
                                                                      u_2}
                                                                    coords base (⇑normI) data family rows)
                                                                  (HPow.hPow.{0, 0, 0} Z
                                                                    (HeckeSkeleton.LowFrozenCube.squaredKernelExponent T
                                                                      v ell)))
                                                                (HMul.hMul.{0, 0, 0} C
                                                                  (HPow.hPow.{0, 0, 0} Z
                                                                    (HAdd.hAdd.{0, 0, 0}
                                                                      (HeckeSkeleton.LowFrozenCube.reflectedExponent O H
                                                                        v ell S B z T)
                                                                      eps)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.uniform_family_source_energy_terminal

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (symbol : A → MonoidHom.{u_2, 0} A ℂ),
  (∀ (a b c : A),
      Eq.{1} ((symbol (HMul.hMul.{u_2, u_2, u_2} a b)) c) (HMul.hMul.{0, 0, 0} ((symbol a) c) ((symbol b) c))) →
    (∀ (a b : A),
        Eq.{1} (HPow.hPow.{0, 0, 0} ((symbol a) b) 6)
          (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
      ∀ (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
        (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
          ∀ (Ccount : ℝ),
            HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
              (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                  (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b => (symbol a) b) →
                (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                    (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b => (symbol a) b) →
                  ∀ (W eps : ℝ),
                    LT.lt.{0} 0 W →
                      LT.lt.{0} 0 eps →
                        ∃ C,
                          LT.lt.{0} 0 C ∧
                            ∀ (Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau Rrad : ℝ),
                              LE.le.{0} 1 Z →
                                LE.le.{0} 0 H →
                                  LE.le.{0} 0 O →
                                    LE.le.{0} 0 S →
                                      LE.le.{0} 0 B →
                                        LE.le.{0} 0 ell →
                                          LE.le.{0} 0 v →
                                            LE.le.{0} 0 z →
                                              LE.le.{0} 0 Q →
                                                Eq.{1} F (HAdd.hAdd.{0, 0, 0} N V) →
                                                  Eq.{1} Nstar (HSub.hSub.{0, 0, 0} N (HMul.hMul.{0, 0, 0} 3 bh)) →
                                                    LE.le.{0} V delta →
                                                      LE.le.{0} bh delta →
                                                        LE.le.{0} z z0 →
                                                          LE.le.{0} H (HSub.hSub.{0, 0, 0} M O) →
                                                            LE.le.{0} c
                                                                (HSub.hSub.{0, 0, 0}
                                                                  (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} F M) Q)
                                                                  z0) →
                                                              LE.le.{0} c
                                                                  (HSub.hSub.{0, 0, 0}
                                                                    (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} 4 F)
                                                                      (HMul.hMul.{0, 0, 0} 3 M))
                                                                    (HMul.hMul.{0, 0, 0} 6 z0)) →
                                                                LE.le.{0}
                                                                    (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} T S) B)
                                                                    (HAdd.hAdd.{0, 0, 0}
                                                                      (HSub.hSub.{0, 0, 0}
                                                                        (HAdd.hAdd.{0, 0, 0}
                                                                          (HAdd.hAdd.{0, 0, 0}
                                                                            (HSub.hSub.{0, 0, 0}
                                                                              (HMul.hMul.{0, 0, 0} 2 M) O)
                                                                            Q)
                                                                          V)
                                                                        Nstar)
                                                                      (HMul.hMul.{0, 0, 0} 2 z)) →
                                                                  LE.le.{0}
                                                                      (HAdd.hAdd.{0, 0, 0} v
                                                                        (HMul.hMul.{0, 0, 0} 3 ell))
                                                                      (HAdd.hAdd.{0, 0, 0} T tau) →
                                                                    LE.le.{0}
                                                                        (HAdd.hAdd.{0, 0, 0}
                                                                          (HAdd.hAdd.{0, 0, 0}
                                                                            (HAdd.hAdd.{0, 0, 0}
                                                                              (HAdd.hAdd.{0, 0, 0} H v) ell)
                                                                            z)
                                                                          (HAdd.hAdd.{0, 0, 0} O Rrad))
                                                                        W →
                                                                      ∀ (base : Finset.{u_1} ι) (rows : Finset.{u_2} A),
                                                                        (∀ (k : A),
                                                                            Membership.mem.{u_2, u_2} rows k →
                                                                              LE.le.{0}
                                                                                (normI
                                                                                  (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1,
                                                                                      u_2}
                                                                                    coords k))
                                                                                (HPow.hPow.{0, 0, 0} Z O)) →
                                                                          LE.le.{0}
                                                                              (normI
                                                                                (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1,
                                                                                    u_2}
                                                                                  coords base))
                                                                              (HPow.hPow.{0, 0, 0} Z Rrad) →
                                                                            ∀
                                                                              (data :
                                                                                Prod.{u_2, u_2} A A →
                                                                                  HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1,
                                                                                      u_2}
                                                                                    ι A)
                                                                              (family :
                                                                                Prod.{u_2, u_2} A A →
                                                                                  HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1,
                                                                                      u_2}
                                                                                    ι A),
                                                                              HeckeSkeleton.LowFrozenCube.FrozenReduction.FrozenFamilyAlignment.{u_1,
                                                                                    u_2}
                                                                                  coords base rows data family →
                                                                                (∀ (pair : Prod.{u_2, u_2} A A),
                                                                                    Membership.mem.{u_2, u_2}
                                                                                        (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                                            u_2}
                                                                                          coords base rows)
                                                                                        pair →
                                                                                      Eq.{u_2 + 1}
                                                                                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1,
                                                                                            u_2}
                                                                                          (data pair))
                                                                                        symbol) →
                                                                                  ∀
                                                                                    (a :
                                                                                      (pair : Prod.{u_2, u_2} A A) →
                                                                                        Membership.mem.{u_2, u_2}
                                                                                            (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                                                u_2}
                                                                                              coords base rows)
                                                                                            pair →
                                                                                          HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1,
                                                                                              u_2}
                                                                                            (data pair) (⇑normI) Z H v
                                                                                            ell z (family pair)),
                                                                                    (∀ (pair : Prod.{u_2, u_2} A A),
                                                                                        Membership.mem.{u_2, u_2}
                                                                                            (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                                                u_2}
                                                                                              coords base rows)
                                                                                            pair →
                                                                                          HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.{u_1,
                                                                                              u_2}
                                                                                            (data pair) (⇑normI)
                                                                                            (family pair)) →
                                                                                      (∀ (pair : Prod.{u_2, u_2} A A),
                                                                                          Membership.mem.{u_2, u_2}
                                                                                              (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1,
                                                                                                  u_2}
                                                                                                coords base rows)
                                                                                              pair →
                                                                                            LE.le.{0}
                                                                                              (HPow.hPow.{0, 0, 0} Z
                                                                                                (HAdd.hAdd.{0, 0, 0} S
                                                                                                  B))
                                                                                              (normI
                                                                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.{u_1,
                                                                                                    u_2}
                                                                                                  (data pair)))) →
                                                                                        LE.le.{0}
                                                                                          (HMul.hMul.{0, 0, 0}
                                                                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.varyingFamilySourceEnergy.{u_1,
                                                                                                u_2}
                                                                                              coords base (⇑normI) data
                                                                                              family rows)
                                                                                            (HPow.hPow.{0, 0, 0} Z
                                                                                              (HeckeSkeleton.LowFrozenCube.squaredKernelExponent
                                                                                                T v ell)))
                                                                                          (HMul.hMul.{0, 0, 0} C
                                                                                            (HPow.hPow.{0, 0, 0} Z
                                                                                              (HAdd.hAdd.{0, 0, 0}
                                                                                                (HeckeSkeleton.LowFrozenCube.terminalBound
                                                                                                  F M c delta tau)
                                                                                                eps)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.uniform_source_energy_ledger

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (symbol : A → MonoidHom.{u_2, 0} A ℂ),
  (∀ (a b c : A),
      Eq.{1} ((symbol (HMul.hMul.{u_2, u_2, u_2} a b)) c) (HMul.hMul.{0, 0, 0} ((symbol a) c) ((symbol b) c))) →
    (∀ (a b : A),
        Eq.{1} (HPow.hPow.{0, 0, 0} ((symbol a) b) 6)
          (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
      ∀ (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
        (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
          (∀ (a : A), LE.le.{0} 1 (q a)) →
            ∀ (Ccount : ℝ),
              LT.lt.{0} 0 Ccount →
                HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
                  (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b => (symbol a) b) →
                    (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                        (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b =>
                        (symbol a) b) →
                      ∀ (eps : ℝ),
                        LT.lt.{0} 0 eps →
                          ∃ C,
                            LT.lt.{0} 0 C ∧
                              ∀ (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A),
                                Eq.{max (u_1 + 1) (u_2 + 1)}
                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) coords →
                                  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D)
                                      symbol →
                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceLedgerBound.{u_1, u_2} D normI eps
                                      C
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.uniform_source_energy_power_saving

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (symbol : A → MonoidHom.{u_2, 0} A ℂ),
  (∀ (a b c : A),
      Eq.{1} ((symbol (HMul.hMul.{u_2, u_2, u_2} a b)) c) (HMul.hMul.{0, 0, 0} ((symbol a) c) ((symbol b) c))) →
    (∀ (a b : A),
        Eq.{1} (HPow.hPow.{0, 0, 0} ((symbol a) b) 6)
          (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
      ∀ (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
        (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
          (∀ (a : A), LE.le.{0} 1 (q a)) →
            ∀ (Ccount : ℝ),
              LT.lt.{0} 0 Ccount →
                HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
                  (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b => (symbol a) b) →
                    (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                        (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b =>
                        (symbol a) b) →
                      ∀ (eps : ℝ),
                        LT.lt.{0} 0 eps →
                          ∃ C,
                            LT.lt.{0} 0 C ∧
                              ∀ (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A),
                                Eq.{max (u_1 + 1) (u_2 + 1)}
                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) coords →
                                  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D)
                                      symbol →
                                    ∀ (Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau : ℝ),
                                      LE.le.{0} 1 Z →
                                        LE.le.{0} 0 H →
                                          LE.le.{0} 0 O →
                                            LE.le.{0} 0 S →
                                              LE.le.{0} 0 B →
                                                LE.le.{0} 0 ell →
                                                  LE.le.{0} 0 v →
                                                    LE.le.{0} 0 z →
                                                      LE.le.{0} 0 Q →
                                                        LE.le.{0} 0 M →
                                                          LE.le.{0} 0 c →
                                                            Eq.{1} F (HAdd.hAdd.{0, 0, 0} N V) →
                                                              Eq.{1} Nstar
                                                                  (HSub.hSub.{0, 0, 0} N (HMul.hMul.{0, 0, 0} 3 bh)) →
                                                                LE.le.{0} V delta →
                                                                  LE.le.{0} bh delta →
                                                                    LE.le.{0} z z0 →
                                                                      LE.le.{0} H (HSub.hSub.{0, 0, 0} M O) →
                                                                        LE.le.{0} c
                                                                            (HSub.hSub.{0, 0, 0}
                                                                              (HSub.hSub.{0, 0, 0}
                                                                                (HSub.hSub.{0, 0, 0} F M) Q)
                                                                              z0) →
                                                                          LE.le.{0} c
                                                                              (HSub.hSub.{0, 0, 0}
                                                                                (HSub.hSub.{0, 0, 0}
                                                                                  (HMul.hMul.{0, 0, 0} 4 F)
                                                                                  (HMul.hMul.{0, 0, 0} 3 M))
                                                                                (HMul.hMul.{0, 0, 0} 6 z0)) →
                                                                            LE.le.{0}
                                                                                (HSub.hSub.{0, 0, 0}
                                                                                  (HSub.hSub.{0, 0, 0} T S) B)
                                                                                (HAdd.hAdd.{0, 0, 0}
                                                                                  (HSub.hSub.{0, 0, 0}
                                                                                    (HAdd.hAdd.{0, 0, 0}
                                                                                      (HAdd.hAdd.{0, 0, 0}
                                                                                        (HSub.hSub.{0, 0, 0}
                                                                                          (HMul.hMul.{0, 0, 0} 2 M) O)
                                                                                        Q)
                                                                                      V)
                                                                                    Nstar)
                                                                                  (HMul.hMul.{0, 0, 0} 2 z)) →
                                                                              LE.le.{0}
                                                                                  (HAdd.hAdd.{0, 0, 0} v
                                                                                    (HMul.hMul.{0, 0, 0} 3 ell))
                                                                                  (HAdd.hAdd.{0, 0, 0} T tau) →
                                                                                LE.le.{0} delta
                                                                                    (HDiv.hDiv.{0, 0, 0} c 100) →
                                                                                  LE.le.{0} tau
                                                                                      (HDiv.hDiv.{0, 0, 0} c 8) →
                                                                                    LE.le.{0}
                                                                                        (HMul.hMul.{0, 0, 0} eps
                                                                                          (HAdd.hAdd.{0, 0, 0}
                                                                                            (HAdd.hAdd.{0, 0, 0}
                                                                                              (HAdd.hAdd.{0, 0, 0} H v)
                                                                                              ell)
                                                                                            z))
                                                                                        (HDiv.hDiv.{0, 0, 0} c 4) →
                                                                                      ∀
                                                                                        (b :
                                                                                          HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1,
                                                                                              u_2}
                                                                                            ι A)
                                                                                        (a :
                                                                                          HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1,
                                                                                              u_2}
                                                                                            D (⇑normI) Z H v ell z b),
                                                                                        HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.{u_1,
                                                                                              u_2}
                                                                                            D (⇑normI) b →
                                                                                          LE.le.{0}
                                                                                              (HPow.hPow.{0, 0, 0} Z
                                                                                                (HAdd.hAdd.{0, 0, 0} S
                                                                                                  B))
                                                                                              (normI
                                                                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.{u_1,
                                                                                                    u_2}
                                                                                                  D)) →
                                                                                            LE.le.{0}
                                                                                              (HMul.hMul.{0, 0, 0}
                                                                                                (HMul.hMul.{0, 0, 0}
                                                                                                  (HPow.hPow.{0, 0, 0} Z
                                                                                                    (HDiv.hDiv.{0, 0, 0}
                                                                                                      O 2))
                                                                                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.energy.{u_1,
                                                                                                      u_2}
                                                                                                    b D ⇑normI))
                                                                                                (HPow.hPow.{0, 0, 0} Z
                                                                                                  (HeckeSkeleton.LowFrozenCube.squaredKernelExponent
                                                                                                    T v ell)))
                                                                                              (HMul.hMul.{0, 0, 0} C
                                                                                                (HPow.hPow.{0, 0, 0} Z
                                                                                                  (HSub.hSub.{0, 0, 0} F
                                                                                                    (HDiv.hDiv.{0, 0, 0}
                                                                                                      c 4))))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.uniform_source_energy_terminal

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (symbol : A → MonoidHom.{u_2, 0} A ℂ),
  (∀ (a b c : A),
      Eq.{1} ((symbol (HMul.hMul.{u_2, u_2, u_2} a b)) c) (HMul.hMul.{0, 0, 0} ((symbol a) c) ((symbol b) c))) →
    (∀ (a b : A),
        Eq.{1} (HPow.hPow.{0, 0, 0} ((symbol a) b) 6)
          (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
      ∀ (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
        (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
          (∀ (a : A), LE.le.{0} 1 (q a)) →
            ∀ (Ccount : ℝ),
              LT.lt.{0} 0 Ccount →
                HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
                  (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b => (symbol a) b) →
                    (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                        (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b =>
                        (symbol a) b) →
                      ∀ (eps : ℝ),
                        LT.lt.{0} 0 eps →
                          ∃ C,
                            LT.lt.{0} 0 C ∧
                              ∀ (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A),
                                Eq.{max (u_1 + 1) (u_2 + 1)}
                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) coords →
                                  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D)
                                      symbol →
                                    ∀ (Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau : ℝ),
                                      LE.le.{0} 1 Z →
                                        LE.le.{0} 0 H →
                                          LE.le.{0} 0 O →
                                            LE.le.{0} 0 S →
                                              LE.le.{0} 0 B →
                                                LE.le.{0} 0 ell →
                                                  LE.le.{0} 0 v →
                                                    LE.le.{0} 0 z →
                                                      LE.le.{0} 0 Q →
                                                        Eq.{1} F (HAdd.hAdd.{0, 0, 0} N V) →
                                                          Eq.{1} Nstar
                                                              (HSub.hSub.{0, 0, 0} N (HMul.hMul.{0, 0, 0} 3 bh)) →
                                                            LE.le.{0} V delta →
                                                              LE.le.{0} bh delta →
                                                                LE.le.{0} z z0 →
                                                                  LE.le.{0} H (HSub.hSub.{0, 0, 0} M O) →
                                                                    LE.le.{0} c
                                                                        (HSub.hSub.{0, 0, 0}
                                                                          (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} F M)
                                                                            Q)
                                                                          z0) →
                                                                      LE.le.{0} c
                                                                          (HSub.hSub.{0, 0, 0}
                                                                            (HSub.hSub.{0, 0, 0}
                                                                              (HMul.hMul.{0, 0, 0} 4 F)
                                                                              (HMul.hMul.{0, 0, 0} 3 M))
                                                                            (HMul.hMul.{0, 0, 0} 6 z0)) →
                                                                        LE.le.{0}
                                                                            (HSub.hSub.{0, 0, 0}
                                                                              (HSub.hSub.{0, 0, 0} T S) B)
                                                                            (HAdd.hAdd.{0, 0, 0}
                                                                              (HSub.hSub.{0, 0, 0}
                                                                                (HAdd.hAdd.{0, 0, 0}
                                                                                  (HAdd.hAdd.{0, 0, 0}
                                                                                    (HSub.hSub.{0, 0, 0}
                                                                                      (HMul.hMul.{0, 0, 0} 2 M) O)
                                                                                    Q)
                                                                                  V)
                                                                                Nstar)
                                                                              (HMul.hMul.{0, 0, 0} 2 z)) →
                                                                          LE.le.{0}
                                                                              (HAdd.hAdd.{0, 0, 0} v
                                                                                (HMul.hMul.{0, 0, 0} 3 ell))
                                                                              (HAdd.hAdd.{0, 0, 0} T tau) →
                                                                            ∀
                                                                              (b :
                                                                                HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1,
                                                                                    u_2}
                                                                                  ι A)
                                                                              (a :
                                                                                HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1,
                                                                                    u_2}
                                                                                  D (⇑normI) Z H v ell z b),
                                                                              HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.{u_1,
                                                                                    u_2}
                                                                                  D (⇑normI) b →
                                                                                LE.le.{0}
                                                                                    (HPow.hPow.{0, 0, 0} Z
                                                                                      (HAdd.hAdd.{0, 0, 0} S B))
                                                                                    (normI
                                                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.{u_1,
                                                                                          u_2}
                                                                                        D)) →
                                                                                  LE.le.{0}
                                                                                    (HMul.hMul.{0, 0, 0}
                                                                                      (HMul.hMul.{0, 0, 0}
                                                                                        (HPow.hPow.{0, 0, 0} Z
                                                                                          (HDiv.hDiv.{0, 0, 0} O 2))
                                                                                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.energy.{u_1,
                                                                                            u_2}
                                                                                          b D ⇑normI))
                                                                                      (HPow.hPow.{0, 0, 0} Z
                                                                                        (HeckeSkeleton.LowFrozenCube.squaredKernelExponent
                                                                                          T v ell)))
                                                                                    (HMul.hMul.{0, 0, 0} C
                                                                                      (HPow.hPow.{0, 0, 0} Z
                                                                                        (HAdd.hAdd.{0, 0, 0}
                                                                                          (HeckeSkeleton.LowFrozenCube.terminalBound
                                                                                            F M c delta tau)
                                                                                          (HMul.hMul.{0, 0, 0} eps
                                                                                            (HAdd.hAdd.{0, 0, 0}
                                                                                              (HAdd.hAdd.{0, 0, 0}
                                                                                                (HAdd.hAdd.{0, 0, 0} H
                                                                                                  v)
                                                                                                ell)
                                                                                              z)))))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.unitAnnularColumn_norm_le

```lean
∀ {A : Type u_2} [CommMonoid.{u_2} A] (normI : A → ℝ) (N : ℝ),
  LT.lt.{0} 0 N →
    ∀ (lam : A → ℂ) (c : A),
      LE.le.{0} N (normI c) →
        LE.le.{0} (Norm.norm.{0} (lam c)) 1 →
          LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.unitAnnularColumn.{u_2} normI N lam c))
            1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.varyingFamilySourceEnergy_eq_blocks

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (base : Finset.{u_1} ι) (normI : A → ℝ)
  (data : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A)
  (family : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A)
  (rows : Finset.{u_2} A),
  HeckeSkeleton.LowFrozenCube.FrozenReduction.FrozenFamilyAlignment.{u_1, u_2} coords base rows data family →
    Eq.{1}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.varyingFamilySourceEnergy.{u_1, u_2} coords base normI data family
        rows)
      (∑ pair ∈ HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2} coords base rows,
        HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.energy.{u_1, u_2} (family pair) (data pair) normI)
```

## HeckeSkeleton.LowFrozenCube.LocalTable.cubeNorm_pos

```lean
∀ {ι : Type u_1} (s : Finset.{u_1} ι) (q : ι → ℝ) (exponent : ι → ℕ),
  (∀ (p : ι), Membership.mem.{u_1, u_1} s p → LT.lt.{0} 0 (q p)) →
    LT.lt.{0} 0 (HeckeSkeleton.LowFrozenCube.LocalTable.cubeNorm.{u_1} s q exponent)
```

## HeckeSkeleton.LowFrozenCube.LocalTable.localProduct_frozen_norm

```lean
∀ {ι : Type u_1} (s : Finset.{u_1} ι) (q : ι → ℝ) (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
  (digit exponent : ι → ℕ),
  (∀ (p : ι), Membership.mem.{u_1, u_1} s p → LT.lt.{0} 0 (q p)) →
    (∀ (p : ι), Membership.mem.{u_1, u_1} s p → HeckeSkeleton.LowFrozenCube.AdmissibleExponent (exponent p)) →
      Eq.{1}
        (Norm.norm.{0}
          (HeckeSkeleton.LowFrozenCube.LocalTable.localProduct.{u_1} s q first prefactor atZero digit exponent))
        (HDiv.hDiv.{0, 0, 0}
          (HeckeSkeleton.LowFrozenCube.LocalTable.minimumMajorant.{u_1} s q first prefactor atZero digit exponent)
          (HeckeSkeleton.LowFrozenCube.LocalTable.cubeNorm.{u_1} s q exponent))
```

## HeckeSkeleton.LowFrozenCube.LocalTable.localProduct_nonzero_admissible

```lean
∀ {ι : Type u_1} (s : Finset.{u_1} ι) (q : ι → ℝ) (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
  (digit exponent : ι → ℕ),
  Ne.{1} (HeckeSkeleton.LowFrozenCube.LocalTable.localProduct.{u_1} s q first prefactor atZero digit exponent) 0 →
    ∀ (p : ι), Membership.mem.{u_1, u_1} s p → HeckeSkeleton.LowFrozenCube.AdmissibleExponent (exponent p)
```

## HeckeSkeleton.LowFrozenCube.LocalTable.minimumCharge_le_one

```lean
∀ (j m : ℕ), LE.le.{0} (HeckeSkeleton.LowFrozenCube.LocalTable.minimumCharge j m) 1
```

## HeckeSkeleton.LowFrozenCube.LocalTable.minimumMajorant_nonneg

```lean
∀ {ι : Type u_1} (s : Finset.{u_1} ι) (q : ι → ℝ) (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
  (digit exponent : ι → ℕ),
  LE.le.{0} 0 (HeckeSkeleton.LowFrozenCube.LocalTable.minimumMajorant.{u_1} s q first prefactor atZero digit exponent)
```

## HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar_add_cube

```lean
∀ (q first prefactor : ℂ) (atZero : ℕ → ℂ) (j e x : ℕ),
  LT.lt.{0} 0 e →
    Eq.{1}
      (HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar q first prefactor atZero j
        (HAdd.hAdd.{0, 0, 0} e (HMul.hMul.{0, 0, 0} 3 x)))
      (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar q first prefactor atZero j e)
        (HPow.hPow.{0, 0, 0} (Inv.inv.{0} q) x))
```

## HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar_frozen

```lean
∀ (q first prefactor : ℂ) (atZero : ℕ → ℂ) (j e : ℕ),
  HeckeSkeleton.LowFrozenCube.AdmissibleExponent e →
    Eq.{1} (HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar q first prefactor atZero j e)
      (HMul.hMul.{0, 0, 0}
        (HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar q first prefactor atZero j
          (HeckeSkeleton.LowFrozenCube.frozenMin e))
        (HPow.hPow.{0, 0, 0} (Inv.inv.{0} q) (HeckeSkeleton.LowFrozenCube.frozenCubeExp e)))
```

## HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar_frozen_norm

```lean
∀ (q : ℝ),
  LT.lt.{0} 0 q →
    ∀ (first prefactor : ℂ) (atZero : ℕ → ℂ) (j e : ℕ),
      HeckeSkeleton.LowFrozenCube.AdmissibleExponent e →
        Eq.{1} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar (↑q) first prefactor atZero j e))
          (HDiv.hDiv.{0, 0, 0}
            (Norm.norm.{0}
              (HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar (↑q) first prefactor atZero j
                (HeckeSkeleton.LowFrozenCube.frozenMin e)))
            (HPow.hPow.{0, 0, 0} q (HeckeSkeleton.LowFrozenCube.frozenCubeExp e)))
```

## HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar_minimum_sq_le

```lean
∀ (q : ℝ),
  LT.lt.{0} 0 q →
    ∀ (first prefactor : ℂ) (atZero : ℕ → ℂ) (j m : ℕ),
      Eq.{1} m 0 ∨ Eq.{1} m 1 ∨ Eq.{1} m 3 →
        LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} first) 2) (HDiv.hDiv.{0, 0, 0} 1 q) →
          LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} prefactor) 2) q →
            LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (atZero j)) 2)
                (ite.{1} (Eq.{1} j 0 ∨ Eq.{1} j 4) (HDiv.hDiv.{0, 0, 0} 1 q) 1) →
              LE.le.{0}
                (HPow.hPow.{0, 0, 0}
                  (Norm.norm.{0}
                    (HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar (↑q) first prefactor atZero j m))
                  2)
                (Inv.inv.{0} (HPow.hPow.{0, 0, 0} q (HeckeSkeleton.LowFrozenCube.LocalTable.minimumCharge j m)))
```

## HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar_nonzero_admissible

```lean
∀ (q first prefactor : ℂ) (atZero : ℕ → ℂ) (j e : ℕ),
  Ne.{1} (HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar q first prefactor atZero j e) 0 →
    HeckeSkeleton.LowFrozenCube.AdmissibleExponent e
```

## HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar_positive_only_four

```lean
∀ (q first prefactor : ℂ) (atZero : ℕ → ℂ) (j e : ℕ),
  LT.lt.{0} 0 e →
    Ne.{1} j 4 → Eq.{1} (HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar q first prefactor atZero j e) 0
```

## HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar_residue_two

```lean
∀ (q first prefactor : ℂ) (atZero : ℕ → ℂ) (j e : ℕ),
  Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 2 →
    Eq.{1} (HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar q first prefactor atZero j e) 0
```

## HeckeSkeleton.LowFrozenCube.LocalTable.phased_localProduct_norm_le

```lean
∀ {ι : Type u_1} (s : Finset.{u_1} ι) (q : ι → ℝ) (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
  (digit exponent : ι → ℕ),
  (∀ (p : ι), Membership.mem.{u_1, u_1} s p → LT.lt.{0} 0 (q p)) →
    (∀ (p : ι), Membership.mem.{u_1, u_1} s p → HeckeSkeleton.LowFrozenCube.AdmissibleExponent (exponent p)) →
      ∀ (phase : ℂ),
        LE.le.{0} (Norm.norm.{0} phase) 1 →
          LE.le.{0}
            (Norm.norm.{0}
              (HMul.hMul.{0, 0, 0} phase
                (HeckeSkeleton.LowFrozenCube.LocalTable.localProduct.{u_1} s q first prefactor atZero digit exponent)))
            (HDiv.hDiv.{0, 0, 0}
              (HeckeSkeleton.LowFrozenCube.LocalTable.minimumMajorant.{u_1} s q first prefactor atZero digit exponent)
              (HeckeSkeleton.LowFrozenCube.LocalTable.cubeNorm.{u_1} s q exponent))
```

## HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar_add_cube

```lean
∀ (q first : ℂ) (e x : ℕ),
  Eq.{1}
    (HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar q first (HAdd.hAdd.{0, 0, 0} e (HMul.hMul.{0, 0, 0} 3 x)))
    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar q first e)
      (HPow.hPow.{0, 0, 0} (Inv.inv.{0} q) x))
```

## HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar_one

```lean
∀ (q first : ℂ), Eq.{1} (HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar q first 1) first
```

## HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar_residue_two

```lean
∀ (q first : ℂ) (e : ℕ),
  Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 2 → Eq.{1} (HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar q first e) 0
```

## HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar_three

```lean
∀ (q first : ℂ), Eq.{1} (HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar q first 3) (Inv.inv.{0} q)
```

## HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar_zero

```lean
∀ (q first : ℂ), Eq.{1} (HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar q first 0) 1
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.awayFactor_avoids

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (a : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2} coords s
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.awayFactor.{u_1, u_2} coords s a)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.coprime_fullCube

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (P x n : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2} coords s P →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords s x →
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords P (HMul.hMul.{u_2, u_2, u_2} x n) ↔
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords P n)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.coprime_mul_right

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a b c : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a (HMul.hMul.{u_2, u_2, u_2} b c) ↔
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b ∧
      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a c
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.coprime_of_avoids_supported

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (P x : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2} coords s P →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords s x →
      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords P x
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.coprime_residualCubeFactor

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (P a : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2} coords s P →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords s a →
      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords P
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2} coords a)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.coprime_symm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a b : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b ↔
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords b a
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.cubeSplit_mul

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (x n : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords s x →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2} coords s n →
      Eq.{u_2 + 1}
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.cubeSplit.{u_1, u_2} coords s (HMul.hMul.{u_2, u_2, u_2} x n))
        (Prod.mk.{u_2, u_2} x n)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.factorization

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (a : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords s a →
    Eq.{u_2 + 1} a
      (∏ p ∈ s,
        HPow.hPow.{u_2, 0, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.primeElement.{u_1, u_2} coords p)
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.minimumFactor_supported

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (a : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords s a →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords s
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.minimumFactor.{u_1, u_2} coords a)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.minimum_mul_residualCube

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A),
  (∀ (p : ι),
      HeckeSkeleton.LowFrozenCube.AdmissibleExponent
        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p)) →
    Eq.{u_2 + 1} a
      (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.minimumFactor.{u_1, u_2} coords a)
        (HPow.hPow.{u_2, 0, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2} coords a)
          3))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.norm_eq_prod

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (a : A),
  Eq.{1} (normI a)
    (∏ p ∈ Finsupp.support.{u_1, 0} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a),
      HPow.hPow.{0, 0, 0} (normI (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.primeElement.{u_1, u_2} coords p))
        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.norm_factorization

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (a : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords s a →
    ∀ (normI : MonoidHom.{u_2, 0} A ℝ),
      Eq.{1} (normI a)
        (∏ p ∈ s,
          HPow.hPow.{0, 0, 0} (normI (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.primeElement.{u_1, u_2} coords p))
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.norm_residualRowFactor

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (k : A)
  (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    Eq.{1} (normI (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2} coords s k))
      (HDiv.hDiv.{0, 0, 0} (normI k)
        (HMul.hMul.{0, 0, 0}
          (normI (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k))
          (normI (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords s k))))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.norm_residualRowFactor_le

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (k : A)
  (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (K : ℝ),
      LE.le.{0} (normI k) K →
        LE.le.{0} (normI (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2} coords s k))
          (HDiv.hDiv.{0, 0, 0} K
            (HMul.hMul.{0, 0, 0}
              (normI (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k))
              (normI (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords s k))))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.norm_row_factorization

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (k : A)
  (normI : MonoidHom.{u_2, 0} A ℝ),
  Eq.{1} (normI k)
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0} (normI (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k))
        (normI (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords s k)))
      (normI (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2} coords s k)))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.not_coprime_iff_shared_prime

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a b : A),
  ¬HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b ↔
    ∃ p,
      Ne.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) 0 ∧
        Ne.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p) 0
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.not_coprime_of_shared_prime

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a b : A) (p : ι),
  Ne.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) 0 →
    Ne.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p) 0 →
      ¬HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulCubeFactor_squarefree

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A) (p : ι),
  LE.le.{0}
    ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulCubeFactor.{u_1, u_2} coords a))
      p)
    1
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor_powerful

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (k : A) (p : ι),
  Eq.{1}
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k))
        p)
      0 ∨
    LE.le.{0} 2
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k))
        p)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerful_factorization

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A),
  (∀ (p : ι),
      Eq.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) 0 ∨
        LE.le.{0} 2 ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p)) →
    Eq.{u_2 + 1} a
      (HMul.hMul.{u_2, u_2, u_2}
        (HPow.hPow.{u_2, 0, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulSquareFactor.{u_1, u_2} coords a)
          2)
        (HPow.hPow.{u_2, 0, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulCubeFactor.{u_1, u_2} coords a)
          3))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerful_factorization_unique

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a u v : A),
  (∀ (p : ι), LE.le.{0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords v) p) 1) →
    Eq.{u_2 + 1} a (HMul.hMul.{u_2, u_2, u_2} (HPow.hPow.{u_2, 0, u_2} u 2) (HPow.hPow.{u_2, 0, u_2} v 3)) →
      Eq.{u_2 + 1} u (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulSquareFactor.{u_1, u_2} coords a) ∧
        Eq.{u_2 + 1} v (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulCubeFactor.{u_1, u_2} coords a)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.primal_marked_sum_overlap_zero

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) {σ : Type u_3} {κ : Type u_4}
  (chi : A → MonoidHom.{u_2, 0} A ℂ),
  (∀ (a b : A),
      Eq.{1} (HPow.hPow.{0, 0, 0} ((chi a) b) 6)
        (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
    ∀ (row : A) (slots : Finset.{u_3} σ) (prime : σ → ι) (i : σ),
      Membership.mem.{u_3, u_3} slots i →
        Ne.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords row) (prime i)) 0 →
          ∀ (indices : Finset.{u_4} κ) (index : κ → A) (weight : κ → ℂ),
            Eq.{1}
              (∑ a ∈ indices,
                HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (weight a) ((chi row) (index a)))
                  (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.idealWholeIndexMark.{u_1, u_2, u_3} coords slots prime
                    (index a)))
              0
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.primeElement_injective

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))),
  Function.Injective.{u_1 + 1, u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.primeElement.{u_1, u_2} coords)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor_supported

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (a : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords s a →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords s
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2} coords a)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor_avoids

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (k : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2} coords s
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2} coords s k)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor_extended

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (base : Finset.{u_1} ι) (k pow : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k) pow →
    Eq.{u_2 + 1}
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2} coords
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.extendedFrozenSupport.{u_1, u_2} coords base pow) k)
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2} coords base k)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor_injOn

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (pow sup : A)
  (rows : Finset.{u_2} A),
  Set.InjOn.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2} coords s)
    ↑(HeckeSkeleton.LowFrozenCube.PrimeCoordinates.rowBlock.{u_1, u_2} coords s pow sup rows)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor_squarefree

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (k : A) (p : ι),
  LE.le.{0}
    ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2} coords s k))
      p)
    1
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows_avoids

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (pow sup : A)
  (rows : Finset.{u_2} A) (d : A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2} coords s pow sup rows)
      d →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2} coords s d
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows_norm_le

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (pow sup : A)
  (rows : Finset.{u_2} A) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (K : ℝ),
      (∀ (k : A), Membership.mem.{u_2, u_2} rows k → LE.le.{0} (normI k) K) →
        ∀ (d : A),
          Membership.mem.{u_2, u_2}
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2} coords s pow sup rows) d →
            LE.le.{0} (normI d) (HDiv.hDiv.{0, 0, 0} K (HMul.hMul.{0, 0, 0} (normI pow) (normI sup)))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows_squarefree

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (pow sup : A)
  (rows : Finset.{u_2} A) (d : A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2} coords s pow sup rows)
      d →
    ∀ (p : ι), LE.le.{0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords d) p) 1
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.rowBlock_extended

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (base : Finset.{u_1} ι) (pow sup : A)
  (rows : Finset.{u_2} A),
  Eq.{u_2 + 1}
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.rowBlock.{u_1, u_2} coords
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.extendedFrozenSupport.{u_1, u_2} coords base pow) pow sup rows)
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.rowBlock.{u_1, u_2} coords base pow sup rows)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.row_factorization

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (k : A),
  Eq.{u_2 + 1} k
    (HMul.hMul.{u_2, u_2, u_2}
      (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k)
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords s k))
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2} coords s k))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.row_factors_pairwise_coprime

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (k : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k)
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords s k) ∧
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k)
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2} coords s k) ∧
      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords s k)
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2} coords s k)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.sum_rowBlock_reindex

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) {R : Type u_3}
  [inst_1 : AddCommMonoid.{u_3} R] (s : Finset.{u_1} ι) (pow sup : A) (rows : Finset.{u_2} A) (F : A → R),
  Eq.{u_3 + 1}
    (∑ k ∈ HeckeSkeleton.LowFrozenCube.PrimeCoordinates.rowBlock.{u_1, u_2} coords s pow sup rows,
      F (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2} coords s k))
    (∑ d ∈ HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2} coords s pow sup rows, F d)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedFactor_supported

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (a : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords s
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedFactor.{u_1, u_2} coords s a)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor_extended

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (base : Finset.{u_1} ι) (k pow : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k) pow →
    Eq.{u_2 + 1}
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.extendedFrozenSupport.{u_1, u_2} coords base pow) k)
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords base k)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor_squarefree

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (k : A) (p : ι),
  LE.le.{0}
    ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords s k))
      p)
    1
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor_supported

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (k : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords s
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords s k)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supported_away_unique

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (a x n : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords s x →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2} coords s n →
      Eq.{u_2 + 1} a (HMul.hMul.{u_2, u_2, u_2} x n) →
        Eq.{u_2 + 1} x (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedFactor.{u_1, u_2} coords s a) ∧
          Eq.{u_2 + 1} n (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.awayFactor.{u_1, u_2} coords s a)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supported_mul_away

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (a : A),
  Eq.{u_2 + 1}
    (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedFactor.{u_1, u_2} coords s a)
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.awayFactor.{u_1, u_2} coords s a))
    a
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supported_support

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2} coords
    (Finsupp.support.{u_1, 0} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a)) a
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.symbol_zero_of_shared_prime

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (chi : A → MonoidHom.{u_2, 0} A ℂ),
  (∀ (a b : A),
      Eq.{1} (HPow.hPow.{0, 0, 0} ((chi a) b) 6)
        (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
    ∀ (a b : A) (p : ι),
      Ne.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) 0 →
        Ne.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p) 0 → Eq.{1} ((chi a) b) 0
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_awayFactor

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (a : A) (p : ι),
  Eq.{1}
    ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.awayFactor.{u_1, u_2} coords s a))
      p)
    (ite.{1} (Membership.mem.{u_1, u_1} s p) 0
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_injective

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))),
  Function.Injective.{u_2 + 1, u_1 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_mapExponents

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (f : ℕ → ℕ) (hf : Eq.{1} (f 0) 0)
  (a : A) (p : ι),
  Eq.{1}
    ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.mapExponents.{u_1, u_2} coords f hf a))
      p)
    (f ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_mul

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a b : A),
  Eq.{u_1 + 1}
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords (HMul.hMul.{u_2, u_2, u_2} a b))
    (HAdd.hAdd.{u_1, u_1, u_1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a)
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_mul_apply

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a b : A) (p : ι),
  Eq.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords (HMul.hMul.{u_2, u_2, u_2} a b)) p)
    (HAdd.hAdd.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p)
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_ne_one_of_mem_powerful_support

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (k pow : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k) pow →
    ∀ (p : ι),
      Membership.mem.{u_1, u_1}
          (Finsupp.support.{u_1, 0} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords pow)) p →
        Ne.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords k) p) 1
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_one

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))),
  Eq.{u_1 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords 1) 0
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_pow

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A) (n : ℕ),
  Eq.{u_1 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords (HPow.hPow.{u_2, 0, u_2} a n))
    (HSMul.hSMul.{0, u_1, u_1} n (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_pow_apply

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A) (n : ℕ) (p : ι),
  Eq.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords (HPow.hPow.{u_2, 0, u_2} a n)) p)
    (HMul.hMul.{0, 0, 0} n ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_powerfulCubeFactor

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A) (p : ι),
  Eq.{1}
    ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulCubeFactor.{u_1, u_2} coords a))
      p)
    (HeckeSkeleton.LowFrozenCube.powerfulCubeDigit
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_powerfulRowFactor

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (k : A) (p : ι),
  Eq.{1}
    ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k))
      p)
    (HeckeSkeleton.LowFrozenCube.powerfulRowPart.{u_1}
      (⇑(HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords k)) p)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_powerfulSquareFactor

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A) (p : ι),
  Eq.{1}
    ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulSquareFactor.{u_1, u_2} coords a))
      p)
    (HeckeSkeleton.LowFrozenCube.powerfulSquareExp
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_primeElement

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (p : ι),
  Eq.{u_1 + 1}
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.primeElement.{u_1, u_2} coords p))
    (Finsupp.single.{u_1, 0} p 1)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_prod_apply

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) {κ : Type u_3} (s : Finset.{u_3} κ)
  (f : κ → A) (p : ι),
  Eq.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords (∏ i ∈ s, f i)) p)
    (∑ i ∈ s, (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords (f i)) p)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_residualRowFactor

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (k : A) (p : ι),
  Eq.{1}
    ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2} coords s k))
      p)
    (HeckeSkeleton.LowFrozenCube.residualRowPart.{u_1} s
      (⇑(HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords k)) p)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_supportedFactor

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (a : A) (p : ι),
  Eq.{1}
    ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedFactor.{u_1, u_2} coords s a))
      p)
    (ite.{1} (Membership.mem.{u_1, u_1} s p)
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) 0)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation_supportedRowFactor

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (k : A) (p : ι),
  Eq.{1}
    ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords s k))
      p)
    (HeckeSkeleton.LowFrozenCube.supportedRowPart.{u_1} s
      (⇑(HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords k)) p)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.wholeIndex_overlap_zero

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) {σ : Type u_3}
  (chi : A → MonoidHom.{u_2, 0} A ℂ),
  (∀ (a b : A),
      Eq.{1} (HPow.hPow.{0, 0, 0} ((chi a) b) 6)
        (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
    ∀ (row : A) (slots : Finset.{u_3} σ) (prime : σ → ι) (i : σ),
      Membership.mem.{u_3, u_3} slots i →
        Ne.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords row) (prime i)) 0 →
          ∀ (a : A),
            Eq.{1}
              (HMul.hMul.{0, 0, 0} ((chi row) a)
                (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.idealWholeIndexMark.{u_1, u_2, u_3} coords slots prime a))
              0
```

## HeckeSkeleton.LowFrozenCube.awayPart.eq_1

```lean
∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] (s : Finset.{u_1} ι) (v : ι → ℕ) (p : ι),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.awayPart.{u_1} s v p) (ite.{1} (Membership.mem.{u_1, u_1} s p) 0 (v p))
```

## HeckeSkeleton.LowFrozenCube.canonicalPair_admissible._proof_1_1

```lean
∀ {e m x : ℕ},
  Eq.{1} m 1 ∨ Eq.{1} m 3 ∨ Eq.{1} m 0 ∧ Eq.{1} x 0 →
    Eq.{1} e (HAdd.hAdd.{0, 0, 0} m (HMul.hMul.{0, 0, 0} 3 x)) →
      ¬(Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 0 ∨ Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 1) → False
```

## HeckeSkeleton.LowFrozenCube.cubeProduct.eq_1

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (q : Prod.{u_1, u_1} A A),
  Eq.{u_1 + 1} (HeckeSkeleton.LowFrozenCube.cubeProduct.{u_1} q) (HMul.hMul.{u_1, u_1, u_1} q.1 q.2)
```

## HeckeSkeleton.LowFrozenCube.cubicSaving._proof_1

```lean
(HAdd.hAdd.{0, 0, 0} 2 1).AtLeastTwo
```

## HeckeSkeleton.LowFrozenCube.cubicScale._proof_1

```lean
(HAdd.hAdd.{0, 0, 0} 1 1).AtLeastTwo
```

## HeckeSkeleton.LowFrozenCube.cubicScale._proof_2

```lean
(HAdd.hAdd.{0, 0, 0} 2 1).AtLeastTwo
```

## HeckeSkeleton.LowFrozenCube.cubicScale.eq_1

```lean
∀ (Z v z : ℝ),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.cubicScale Z v z)
    (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z v) (HPow.hPow.{0, 0, 0} Z z))
      (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z v) (HPow.hPow.{0, 0, 0} Z z)) (2 / 3)))
```

## HeckeSkeleton.LowFrozenCube.disjoint_add_right._proof_1_1

```lean
∀ {ι : Type u_1} {x n : ι → ℕ} (p : ι), Eq.{1} (HAdd.hAdd.{0, 0, 0} (x p) (n p)) 0 → ¬Eq.{1} (x p) 0 → False
```

## HeckeSkeleton.LowFrozenCube.disjoint_add_right._proof_1_2

```lean
∀ {ι : Type u_1} {x n : ι → ℕ} (p : ι), Eq.{1} (HAdd.hAdd.{0, 0, 0} (x p) (n p)) 0 → ¬Eq.{1} (n p) 0 → False
```

## HeckeSkeleton.LowFrozenCube.frozenBase.eq_1

```lean
∀ {ι : Type u_1} (v : ι → ℕ) (p : ι),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.frozenBase.{u_1} v p) (HeckeSkeleton.LowFrozenCube.frozenMin (v p))
```

## HeckeSkeleton.LowFrozenCube.frozenCube.eq_1

```lean
∀ {ι : Type u_1} (v : ι → ℕ) (p : ι),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.frozenCube.{u_1} v p) (HeckeSkeleton.LowFrozenCube.frozenCubeExp (v p))
```

## HeckeSkeleton.LowFrozenCube.frozenCubeExp.eq_1

```lean
∀ (e : ℕ),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.frozenCubeExp e)
    (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} e (HeckeSkeleton.LowFrozenCube.frozenMin e)) 3)
```

## HeckeSkeleton.LowFrozenCube.frozenExponent_decomposition._proof_1_3

```lean
∀ (e : ℕ),
  Eq.{1} e 0 →
    ¬Eq.{1} e (HAdd.hAdd.{0, 0, 0} 0 (HMul.hMul.{0, 0, 0} 3 (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} e 0) 3))) → False
```

## HeckeSkeleton.LowFrozenCube.frozenExponent_decomposition._proof_1_4

```lean
∀ (e : ℕ),
  Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 1 →
    ¬Eq.{1} e (HAdd.hAdd.{0, 0, 0} 1 (HMul.hMul.{0, 0, 0} 3 (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} e 1) 3))) → False
```

## HeckeSkeleton.LowFrozenCube.frozenExponent_decomposition._proof_1_5

```lean
∀ (e : ℕ),
  Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 0 ∨ Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 1 →
    ¬Eq.{1} e 0 →
      ¬Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 1 →
        ¬Eq.{1} e (HAdd.hAdd.{0, 0, 0} 3 (HMul.hMul.{0, 0, 0} 3 (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} e 3) 3))) →
          False
```

## HeckeSkeleton.LowFrozenCube.frozenExponent_unique._proof_1_3

```lean
∀ {e m x : ℕ},
  Eq.{1} e (HAdd.hAdd.{0, 0, 0} m (HMul.hMul.{0, 0, 0} 3 x)) →
    Eq.{1} e 0 → ¬(Eq.{1} m 0 ∧ Eq.{1} x (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} e 0) 3)) → False
```

## HeckeSkeleton.LowFrozenCube.frozenExponent_unique._proof_1_4

```lean
∀ {e m x : ℕ},
  Eq.{1} m 1 ∨ Eq.{1} m 3 ∨ Eq.{1} m 0 ∧ Eq.{1} x 0 →
    Eq.{1} e (HAdd.hAdd.{0, 0, 0} m (HMul.hMul.{0, 0, 0} 3 x)) →
      ¬Eq.{1} e 0 →
        Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 1 →
          ¬(Eq.{1} m 1 ∧ Eq.{1} x (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} e 1) 3)) → False
```

## HeckeSkeleton.LowFrozenCube.frozenExponent_unique._proof_1_5

```lean
∀ {e m x : ℕ},
  Eq.{1} m 1 ∨ Eq.{1} m 3 ∨ Eq.{1} m 0 ∧ Eq.{1} x 0 →
    Eq.{1} e (HAdd.hAdd.{0, 0, 0} m (HMul.hMul.{0, 0, 0} 3 x)) →
      ¬Eq.{1} e 0 →
        ¬Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 1 →
          ¬(Eq.{1} m 3 ∧ Eq.{1} x (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} e 3) 3)) → False
```

## HeckeSkeleton.LowFrozenCube.frozenMin.eq_1

```lean
∀ (e : ℕ),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.frozenMin e)
    (ite.{1} (Eq.{1} e 0) 0 (ite.{1} (Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 1) 1 3))
```

## HeckeSkeleton.LowFrozenCube.frozenMin_eq_zero_iff._simp_1

```lean
∀ (e : ℕ), Eq.{1} (Eq.{1} (HeckeSkeleton.LowFrozenCube.frozenMin e) 0) (Eq.{1} e 0)
```

## HeckeSkeleton.LowFrozenCube.frozenMin_le._proof_1_1

```lean
∀ (e : ℕ), Eq.{1} e 0 → ¬LE.le.{0} 0 e → False
```

## HeckeSkeleton.LowFrozenCube.frozenMin_le._proof_1_2

```lean
∀ (e : ℕ), Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 1 → ¬LE.le.{0} 1 e → False
```

## HeckeSkeleton.LowFrozenCube.frozenMin_le._proof_1_3

```lean
∀ (e : ℕ),
  Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 0 ∨ Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 1 →
    ¬Eq.{1} e 0 → ¬Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 1 → ¬LE.le.{0} 3 e → False
```

## HeckeSkeleton.LowFrozenCube.fullCubeCoefficient.eq_1

```lean
∀ {A : Type u_1} (split : A → Prod.{u_1, u_1} A A) (B : A → A → A → ℂ) (c b : A),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.fullCubeCoefficient.{u_1} split B c b) (B c (split b).1 (split b).2)
```

## HeckeSkeleton.LowFrozenCube.hybridScale.eq_1

```lean
∀ (Z H v ell z : ℝ),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.hybridScale Z H v ell z)
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowFrozenCube.quadraticScale Z H v ell) (HPow.hPow.{0, 0, 0} Z ell))
      (HeckeSkeleton.LowFrozenCube.cubicScale Z v z))
```

## HeckeSkeleton.LowFrozenCube.localPhaseDigit.eq_1

```lean
∀ (j e : ℕ),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.localPhaseDigit j e)
    (ite.{1} (Eq.{1} e 0) (HMod.hMod.{0, 0, 0} (HSub.hSub.{0, 0, 0} 8 j) 6)
      (HMod.hMod.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 4 (HMul.hMul.{0, 0, 0} 2 e)) 6))
```

## HeckeSkeleton.LowFrozenCube.localPhaseDigit_add_cube._proof_1_1

```lean
∀ (e : ℕ), LT.lt.{0} 0 e → Eq.{1} e 0 → False
```

## HeckeSkeleton.LowFrozenCube.localPhaseDigit_add_cube._proof_1_2

```lean
∀ (e x : ℕ), LT.lt.{0} 0 e → Eq.{1} (HAdd.hAdd.{0, 0, 0} e (HMul.hMul.{0, 0, 0} 3 x)) 0 → False
```

## HeckeSkeleton.LowFrozenCube.localPhaseDigit_add_cube._proof_1_4

```lean
∀ (e x : ℕ),
  ¬Eq.{1}
        (HMod.hMod.{0, 0, 0}
          (HAdd.hAdd.{0, 0, 0} 4 (HMul.hMul.{0, 0, 0} 2 (HAdd.hAdd.{0, 0, 0} e (HMul.hMul.{0, 0, 0} 3 x)))) 6)
        (HMod.hMod.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 4 (HMul.hMul.{0, 0, 0} 2 e)) 6) →
    False
```

## HeckeSkeleton.LowFrozenCube.localPhaseDigit_frozen._proof_1_1

```lean
∀ (e : ℕ),
  Ne.{1} (HeckeSkeleton.LowFrozenCube.frozenMin e) 0 → ¬LT.lt.{0} 0 (HeckeSkeleton.LowFrozenCube.frozenMin e) → False
```

## HeckeSkeleton.LowFrozenCube.normalizedCubeCoefficient.eq_1

```lean
∀ (Qx C : ℝ) (Ω : ℂ),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.normalizedCubeCoefficient Qx C Ω)
    (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} ↑Qx ↑C) Ω)
```

## HeckeSkeleton.LowFrozenCube.normalizedCubeCoefficient_reassemble._simp_1_2

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 2] [NeZero.{u_2} 2], Eq.{1} (Eq.{u_2 + 1} 2 0) False
```

## HeckeSkeleton.LowFrozenCube.normalizedCubeCoefficient_reassemble._simp_1_3

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 3] [NeZero.{u_2} 3], Eq.{1} (Eq.{u_2 + 1} 3 0) False
```

## HeckeSkeleton.LowFrozenCube.normalizedCubeCoefficient_reassemble._simp_1_4

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 4] [NeZero.{u_2} 4], Eq.{1} (Eq.{u_2 + 1} 4 0) False
```

## HeckeSkeleton.LowFrozenCube.normalizedCubeCoefficient_reassemble._simp_1_5

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [NoZeroDivisors.{u_1} M₀] {a b : M₀},
  Ne.{u_1 + 1} a 0 → Ne.{u_1 + 1} b 0 → Eq.{1} (Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} a b) 0) False
```

## HeckeSkeleton.LowFrozenCube.normalizedCubeCoefficient_reassemble._simp_1_6

```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀} [IsReduced.{u_1} M₀] (n : ℕ),
  Ne.{u_1 + 1} a 0 → Eq.{1} (Eq.{u_1 + 1} (HPow.hPow.{u_1, 0, u_1} a n) 0) False
```

## HeckeSkeleton.LowFrozenCube.normalizedCubeCoefficient_reassemble._simp_1_7

```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero.{u_3} G₀] {a : G₀} (n : ℤ),
  Ne.{u_3 + 1} a 0 → Eq.{1} (Eq.{u_3 + 1} (HPow.hPow.{u_3, 0, u_3} a n) 0) False
```

## HeckeSkeleton.LowFrozenCube.normalizedCubeCoefficient_reassemble._simp_1_8

```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne.{u_1} R] [CharZero.{u_1} R] (n : ℕ),
  Eq.{1} (Eq.{u_1 + 1} (HAdd.hAdd.{u_1, u_1, u_1} (↑n) 1) 0) False
```

## HeckeSkeleton.LowFrozenCube.powerfulCubeDigit.eq_1

```lean
∀ (e : ℕ), Eq.{1} (HeckeSkeleton.LowFrozenCube.powerfulCubeDigit e) (HMod.hMod.{0, 0, 0} e 2)
```

## HeckeSkeleton.LowFrozenCube.powerfulCubeDigit_squarefree._proof_1_1

```lean
∀ (e : ℕ), ¬LE.le.{0} (HMod.hMod.{0, 0, 0} e 2) 1 → False
```

## HeckeSkeleton.LowFrozenCube.powerfulExponent_decomposition._proof_1_1

```lean
∀ (e : ℕ),
  Eq.{1} e 0 ∨ LE.le.{0} 2 e →
    ¬Eq.{1} e
          (HAdd.hAdd.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} 2
              (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} e (HMul.hMul.{0, 0, 0} 3 (HMod.hMod.{0, 0, 0} e 2))) 2))
            (HMul.hMul.{0, 0, 0} 3 (HMod.hMod.{0, 0, 0} e 2))) →
      False
```

## HeckeSkeleton.LowFrozenCube.powerfulExponent_unique._proof_1_1

```lean
∀ {e a b : ℕ},
  LE.le.{0} b 1 →
    Eq.{1} e (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 a) (HMul.hMul.{0, 0, 0} 3 b)) →
      ¬(Eq.{1} a (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} e (HMul.hMul.{0, 0, 0} 3 (HMod.hMod.{0, 0, 0} e 2))) 2) ∧
            Eq.{1} b (HMod.hMod.{0, 0, 0} e 2)) →
        False
```

## HeckeSkeleton.LowFrozenCube.powerfulRowPart.eq_1

```lean
∀ {ι : Type u_1} (v : ι → ℕ) (p : ι),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.powerfulRowPart.{u_1} v p) (ite.{1} (LE.le.{0} 2 (v p)) (v p) 0)
```

## HeckeSkeleton.LowFrozenCube.powerfulSquareExp.eq_1

```lean
∀ (e : ℕ),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.powerfulSquareExp e)
    (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} e (HMul.hMul.{0, 0, 0} 3 (HMod.hMod.{0, 0, 0} e 2))) 2)
```

## HeckeSkeleton.LowFrozenCube.powerful_pair_norm_le_sqrt._proof_1_1

```lean
¬LE.le.{0} 2 3 → False
```

## HeckeSkeleton.LowFrozenCube.quadraticScale.eq_1

```lean
∀ (Z H v ell : ℝ),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.quadraticScale Z H v ell)
    (HAdd.hAdd.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z H)
      (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z v) (HPow.hPow.{0, 0, 0} Z ell)))
```

## HeckeSkeleton.LowFrozenCube.residualRowPart.congr_simp

```lean
∀ {ι : Type u_1} {inst : DecidableEq.{u_1 + 1} ι} [inst_1 : DecidableEq.{u_1 + 1} ι] (s s_1 : Finset.{u_1} ι),
  Eq.{u_1 + 1} s s_1 →
    ∀ (v v_1 : ι → ℕ),
      Eq.{u_1 + 1} v v_1 →
        ∀ (a a_1 : ι),
          Eq.{u_1 + 1} a a_1 →
            Eq.{1} (HeckeSkeleton.LowFrozenCube.residualRowPart.{u_1} s v a)
              (HeckeSkeleton.LowFrozenCube.residualRowPart.{u_1} s_1 v_1 a_1)
```

## HeckeSkeleton.LowFrozenCube.residualRowPart.eq_1

```lean
∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] (s : Finset.{u_1} ι) (v : ι → ℕ) (p : ι),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.residualRowPart.{u_1} s v p) (ite.{1} (Eq.{1} (v p) 1 ∧ p ∉ s) 1 0)
```

## HeckeSkeleton.LowFrozenCube.residualRowPart_squarefree._proof_1_2

```lean
∀ {ι : Type u_1} (v : ι → ℕ) (p : ι), ¬LE.le.{0} 1 1 → False
```

## HeckeSkeleton.LowFrozenCube.residualRowPart_squarefree._proof_1_3

```lean
¬LE.le.{0} 0 1 → False
```

## HeckeSkeleton.LowFrozenCube.row_decomposition._proof_1_1

```lean
∀ {ι : Type u_1} (v : ι → ℕ) (p : ι), LE.le.{0} 2 (v p) → Eq.{1} (v p) 1 → False
```

## HeckeSkeleton.LowFrozenCube.row_decomposition._proof_1_5

```lean
∀ {ι : Type u_1} (v : ι → ℕ) (p : ι), ¬LE.le.{0} 2 (v p) → ¬(Eq.{1} (v p) 0 ∨ Eq.{1} (v p) 1) → False
```

## HeckeSkeleton.LowFrozenCube.row_parts_pairwise_disjoint._proof_1_3

```lean
∀ {ι : Type u_1} (s : Finset.{u_1} ι) (v : ι → ℕ) (p : ι),
  LE.le.{0} 2 (v p) → Eq.{1} (v p) 1 ∧ Membership.mem.{u_1, u_1} s p → False
```

## HeckeSkeleton.LowFrozenCube.row_parts_pairwise_disjoint._proof_1_4

```lean
∀ {ι : Type u_1} (v : ι → ℕ) (p : ι), ¬(Eq.{1} (v p) 0 ∨ Eq.{1} 0 0) → False
```

## HeckeSkeleton.LowFrozenCube.row_parts_pairwise_disjoint._proof_1_5

```lean
∀ {ι : Type u_1} (v : ι → ℕ) (p : ι), ¬(Eq.{1} 0 0 ∨ False) → False
```

## HeckeSkeleton.LowFrozenCube.row_parts_pairwise_disjoint._proof_1_6

```lean
∀ {ι : Type u_1} (v : ι → ℕ) (p : ι), ¬(Eq.{1} 0 0 ∨ Eq.{1} 0 0) → False
```

## HeckeSkeleton.LowFrozenCube.row_parts_pairwise_disjoint._proof_1_8

```lean
∀ {ι : Type u_1} (s : Finset.{u_1} ι) (v : ι → ℕ) (p : ι), LE.le.{0} 2 (v p) → Eq.{1} (v p) 1 ∧ p ∉ s → False
```

## HeckeSkeleton.LowFrozenCube.squaredCoefficientExponent._proof_1

```lean
(HAdd.hAdd.{0, 0, 0} 1 1).AtLeastTwo
```

## HeckeSkeleton.LowFrozenCube.sum_rows_eq_frozen_blocks._simp_1_2

```lean
∀ {α : Type u} {β : Type v} {x y : Prod.{u, v} α β},
  Eq.{1} (Eq.{max (u + 1) (v + 1)} x y) (Eq.{u + 1} x.1 y.1 ∧ Eq.{v + 1} x.2 y.2)
```

## HeckeSkeleton.LowFrozenCube.supportedPart.eq_1

```lean
∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] (s : Finset.{u_1} ι) (v : ι → ℕ) (p : ι),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.supportedPart.{u_1} s v p) (ite.{1} (Membership.mem.{u_1, u_1} s p) (v p) 0)
```

## HeckeSkeleton.LowFrozenCube.supportedRowPart.congr_simp

```lean
∀ {ι : Type u_1} {inst : DecidableEq.{u_1 + 1} ι} [inst_1 : DecidableEq.{u_1 + 1} ι] (s s_1 : Finset.{u_1} ι),
  Eq.{u_1 + 1} s s_1 →
    ∀ (v v_1 : ι → ℕ),
      Eq.{u_1 + 1} v v_1 →
        ∀ (a a_1 : ι),
          Eq.{u_1 + 1} a a_1 →
            Eq.{1} (HeckeSkeleton.LowFrozenCube.supportedRowPart.{u_1} s v a)
              (HeckeSkeleton.LowFrozenCube.supportedRowPart.{u_1} s_1 v_1 a_1)
```

## HeckeSkeleton.LowFrozenCube.supportedRowPart.eq_1

```lean
∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] (s : Finset.{u_1} ι) (v : ι → ℕ) (p : ι),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.supportedRowPart.{u_1} s v p)
    (ite.{1} (Eq.{1} (v p) 1 ∧ Membership.mem.{u_1, u_1} s p) 1 0)
```

## HeckeSkeleton.LowFrozenCube.supportedRowPart_squarefree._proof_1_2

```lean
∀ {ι : Type u_1} (v : ι → ℕ) (p : ι), ¬LE.le.{0} 1 1 → False
```

## HeckeSkeleton.LowFrozenCube.supportedRowPart_squarefree._proof_1_3

```lean
¬LE.le.{0} 0 1 → False
```

## HeckeSkeleton.LowFrozenCube.terminalBound._proof_1

```lean
(HAdd.hAdd.{0, 0, 0} 4 1).AtLeastTwo
```

## HeckeSkeleton.LowFrozenCube.terminalBound._proof_2

```lean
(HAdd.hAdd.{0, 0, 0} 3 1).AtLeastTwo
```

## HeckeSkeleton.LowFrozenCube.valuationProduct.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A] (prime : ι → A) (s : Finset.{u_1} ι) (v : ι → ℕ),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.valuationProduct.{u_1, u_2} prime s v)
    (∏ p ∈ s, HPow.hPow.{u_2, 0, u_2} (prime p) (v p))
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.card_le_real_scale

```lean
∀ {A : Type u_2} [CommMonoid.{u_2} A] (normI : A → ℝ) (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    ∀ (C : ℝ),
      LE.le.{0} 0 C →
        HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q C →
          ∀ (X : ℝ),
            LE.le.{0} 0 X →
              ∀ (s : Finset.{u_2} A),
                (∀ (a : A), Membership.mem.{u_2, u_2} s a → LE.le.{0} (normI a) X) →
                  LE.le.{0} (↑(Finset.card.{u_2} s)) (HMul.hMul.{0, 0, 0} C X)
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.completed_energy_le

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ)
  (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    (∀ (a : A), LE.le.{0} 1 (q a)) →
      ∀ (Ccount : ℝ),
        LT.lt.{0} 0 Ccount →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
            ∀ (symbol : A → A → ℂ),
              (∀ (a b c : A),
                  Eq.{1} (symbol a (HMul.hMul.{u_2, u_2, u_2} b c)) (HMul.hMul.{0, 0, 0} (symbol a b) (symbol a c))) →
                (∀ (a b : A),
                    Eq.{1} (HPow.hPow.{0, 0, 0} (symbol a b) 6)
                      (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
                  HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) symbol →
                    ∀ (eta : ℝ),
                      LT.lt.{0} 0 eta →
                        ∃ Cq,
                          LT.lt.{0} 0 Cq ∧
                            ∀ (K X : ℝ),
                              LE.le.{0} 1 K →
                                LE.le.{0} 1 X →
                                  ∀ (rows ys : Finset.{u_2} A) (gamma : A → ℂ) (G : ℝ),
                                    LE.le.{0} 0 G →
                                      (∀ (k : A),
                                          Membership.mem.{u_2, u_2} rows k →
                                            HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords k ∧
                                              LE.le.{0} (normI k) K) →
                                        (∀ (y : A), Membership.mem.{u_2, u_2} ys y → LE.le.{0} (normI y) X) →
                                          (∀ (y : A),
                                              Membership.mem.{u_2, u_2} ys y → LE.le.{0} (Norm.norm.{0} (gamma y)) G) →
                                            LE.le.{0}
                                              (∑ k ∈ rows,
                                                HPow.hPow.{0, 0, 0}
                                                  (Norm.norm.{0}
                                                    (∑ y ∈ ys,
                                                      HMul.hMul.{0, 0, 0} (gamma y)
                                                        (HPow.hPow.{0, 0, 0} (symbol k y) 3)))
                                                  2)
                                              (HMul.hMul.{0, 0, 0}
                                                (HMul.hMul.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0}
                                                    (HMul.hMul.{0, 0, 0}
                                                      (HMul.hMul.{0, 0, 0}
                                                        (HMul.hMul.{0, 0, 0} Cq
                                                          (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} K X) eta))
                                                        (HAdd.hAdd.{0, 0, 0} K X))
                                                      (HPow.hPow.{0, 0, 0} G 2))
                                                    Ccount)
                                                  X)
                                                (HPow.hPow.{0, 0, 0} (HeckeSkeleton.LowHybrid.harmonicEnvelope Ccount X)
                                                  2))
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.completed_quadratic_positive

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : A → ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (symbol : A → A → ℂ),
      (∀ (a b c : A),
          Eq.{1} (symbol a (HMul.hMul.{u_2, u_2, u_2} b c)) (HMul.hMul.{0, 0, 0} (symbol a b) (symbol a c))) →
        (∀ (a b : A),
            Eq.{1} (HPow.hPow.{0, 0, 0} (symbol a b) 6)
              (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
          ∀ (rows ys : Finset.{u_2} A) (gamma : A → ℂ) (Q : ℝ),
            (∀ (t : A),
                Membership.mem.{u_2, u_2} (HeckeSkeleton.LowHybrid.CompletedQuadratic.squareRoots.{u_1, u_2} coords ys)
                    t →
                  ∀ (f : A → ℂ),
                    LE.le.{0}
                      (∑ k ∈ rows,
                        HPow.hPow.{0, 0, 0}
                          (Norm.norm.{0}
                            (∑ s ∈ HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreeColumns.{u_1, u_2} coords ys t,
                              HMul.hMul.{0, 0, 0} (f s) (HPow.hPow.{0, 0, 0} (symbol k s) 3)))
                          2)
                      (HMul.hMul.{0, 0, 0} Q
                        (∑ s ∈ HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreeColumns.{u_1, u_2} coords ys t,
                          HPow.hPow.{0, 0, 0} (Norm.norm.{0} (f s)) 2))) →
              LE.le.{0}
                (∑ k ∈ rows,
                  HPow.hPow.{0, 0, 0}
                    (Norm.norm.{0} (∑ y ∈ ys, HMul.hMul.{0, 0, 0} (gamma y) (HPow.hPow.{0, 0, 0} (symbol k y) 3))) 2)
                (HMul.hMul.{0, 0, 0}
                  (∑ t ∈ HeckeSkeleton.LowHybrid.CompletedQuadratic.squareRoots.{u_1, u_2} coords ys,
                    HDiv.hDiv.{0, 0, 0} 1 (normI t))
                  (∑ t ∈ HeckeSkeleton.LowHybrid.CompletedQuadratic.squareRoots.{u_1, u_2} coords ys,
                    HMul.hMul.{0, 0, 0} (normI t)
                      (HMul.hMul.{0, 0, 0} Q
                        (∑ s ∈ HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreeColumns.{u_1, u_2} coords ys t,
                          HPow.hPow.{0, 0, 0}
                            (Norm.norm.{0} (gamma (HMul.hMul.{u_2, u_2, u_2} s (HPow.hPow.{u_2, 0, u_2} t 2)))) 2))))
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.productCoefficient_norm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (columns cubes : Finset.{u_2} A),
  (∀ (n : A),
      Membership.mem.{u_2, u_2} columns n → HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords n) →
    ∀ (beta : A → A → ℂ),
      (∀ (n : A),
          Membership.mem.{u_2, u_2} columns n →
            ∀ (b : A), Membership.mem.{u_2, u_2} cubes b → LE.le.{0} (Norm.norm.{0} (beta n b)) 1) →
        ∀ (y : A),
          LE.le.{0}
            (Norm.norm.{0} (HeckeSkeleton.LowHybrid.CompletedQuadratic.productCoefficient.{u_2} columns cubes beta y))
            ↑(Finset.card.{u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords y))
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.product_fiber_card

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (columns cubes : Finset.{u_2} A),
  (∀ (n : A),
      Membership.mem.{u_2, u_2} columns n → HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords n) →
    ∀ (y : A),
      LE.le.{0}
        ↑(Finset.card.{u_2}
            ({u ∈ SProd.sprod.{u_2, u_2, u_2} columns cubes | Eq.{u_2 + 1} (HMul.hMul.{u_2, u_2, u_2} u.1 u.2) y}))
        ↑(Finset.card.{u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords y))
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.product_row

```lean
∀ {A : Type u_2} [inst : CommMonoid.{u_2} A] (symbol : A → A → ℂ) (columns cubes : Finset.{u_2} A)
  (beta : A → A → ℂ) (k : A),
  Eq.{1}
    (∑ n ∈ columns,
      ∑ b ∈ cubes, HMul.hMul.{0, 0, 0} (beta n b) (HPow.hPow.{0, 0, 0} (symbol k (HMul.hMul.{u_2, u_2, u_2} n b)) 3))
    (∑ y ∈ HeckeSkeleton.LowHybrid.CompletedQuadratic.products.{u_2} columns cubes,
      HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.CompletedQuadratic.productCoefficient.{u_2} columns cubes beta y)
        (HPow.hPow.{0, 0, 0} (symbol k y) 3))
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.square_decomposition

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (y : A),
  Eq.{u_2 + 1}
    (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreePart.{u_1, u_2} coords y)
      (HPow.hPow.{u_2, 0, u_2} (HeckeSkeleton.LowHybrid.CompletedQuadratic.squarePart.{u_1, u_2} coords y) 2))
    y
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.square_symbol

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (symbol : A → A → ℂ),
  (∀ (a b c : A), Eq.{1} (symbol a (HMul.hMul.{u_2, u_2, u_2} b c)) (HMul.hMul.{0, 0, 0} (symbol a b) (symbol a c))) →
    (∀ (a b : A),
        Eq.{1} (HPow.hPow.{0, 0, 0} (symbol a b) 6)
          (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
      ∀ (k s t : A),
        Eq.{1} (HPow.hPow.{0, 0, 0} (symbol k (HMul.hMul.{u_2, u_2, u_2} s (HPow.hPow.{u_2, 0, u_2} t 2))) 3)
          (HMul.hMul.{0, 0, 0}
            (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords k t) 1 0)
            (HPow.hPow.{0, 0, 0} (symbol k s) 3))
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreeColumn_injective

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (ys : Finset.{u_2} A) (t : A),
  Set.InjOn.{u_2, u_2} (HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreePart.{u_1, u_2} coords)
    ↑({y ∈ ys | Eq.{u_2 + 1} (HeckeSkeleton.LowHybrid.CompletedQuadratic.squarePart.{u_1, u_2} coords y) t})
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreeColumns_mem

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) {ys : Finset.{u_2} A} {t s : A},
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreeColumns.{u_1, u_2} coords ys t) s →
    Membership.mem.{u_2, u_2} ys (HMul.hMul.{u_2, u_2, u_2} s (HPow.hPow.{u_2, 0, u_2} t 2)) ∧
      HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords s
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreePart_squarefree

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (y : A),
  HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords
    (HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreePart.{u_1, u_2} coords y)
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.sum_square_parts

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) {R : Type u_3}
  [inst_1 : AddCommMonoid.{u_3} R] (ys : Finset.{u_2} A) (F : A → R),
  Eq.{u_3 + 1} (∑ y ∈ ys, F y)
    (∑ t ∈ HeckeSkeleton.LowHybrid.CompletedQuadratic.squareRoots.{u_1, u_2} coords ys,
      ∑ s ∈ HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreeColumns.{u_1, u_2} coords ys t,
        F (HMul.hMul.{u_2, u_2, u_2} s (HPow.hPow.{u_2, 0, u_2} t 2)))
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.sum_square_symbols

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (symbol : A → A → ℂ),
  (∀ (a b c : A), Eq.{1} (symbol a (HMul.hMul.{u_2, u_2, u_2} b c)) (HMul.hMul.{0, 0, 0} (symbol a b) (symbol a c))) →
    (∀ (a b : A),
        Eq.{1} (HPow.hPow.{0, 0, 0} (symbol a b) 6)
          (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
      ∀ (ys : Finset.{u_2} A) (gamma : A → ℂ) (k : A),
        Eq.{1} (∑ y ∈ ys, HMul.hMul.{0, 0, 0} (gamma y) (HPow.hPow.{0, 0, 0} (symbol k y) 3))
          (∑ t ∈ HeckeSkeleton.LowHybrid.CompletedQuadratic.squareRoots.{u_1, u_2} coords ys,
            HMul.hMul.{0, 0, 0}
              (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords k t) 1 0)
              (∑ s ∈ HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreeColumns.{u_1, u_2} coords ys t,
                HMul.hMul.{0, 0, 0} (gamma (HMul.hMul.{u_2, u_2, u_2} s (HPow.hPow.{u_2, 0, u_2} t 2)))
                  (HPow.hPow.{0, 0, 0} (symbol k s) 3)))
```

## HeckeSkeleton.LowHybrid.CubicSieveInput._proof_1

```lean
(HAdd.hAdd.{0, 0, 0} 1 1).AtLeastTwo
```

## HeckeSkeleton.LowHybrid.CubicSieveInput._proof_2

```lean
(HAdd.hAdd.{0, 0, 0} 2 1).AtLeastTwo
```

## HeckeSkeleton.LowHybrid.Factorization.commonExp_le_one

```lean
∀ (n b : ℕ), LE.le.{0} n 1 → LE.le.{0} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b) 1
```

## HeckeSkeleton.LowHybrid.Factorization.commonPart_leftPart_coprime

```lean
∀ {ι : Type u_1} (n b : ι → ℕ),
  HeckeSkeleton.LowHybrid.Factorization.SquarefreeVector.{u_1} n →
    HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1}
      (HeckeSkeleton.LowHybrid.Factorization.commonPart.{u_1} n b)
      (HeckeSkeleton.LowHybrid.Factorization.leftPart.{u_1} n b)
```

## HeckeSkeleton.LowHybrid.Factorization.commonPart_rightPart_coprime

```lean
∀ {ι : Type u_1} (n b : ι → ℕ),
  HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} (HeckeSkeleton.LowHybrid.Factorization.commonPart.{u_1} n b)
    (HeckeSkeleton.LowHybrid.Factorization.rightPart.{u_1} n b)
```

## HeckeSkeleton.LowHybrid.Factorization.commonPart_squarefree

```lean
∀ {ι : Type u_1} (n b : ι → ℕ),
  HeckeSkeleton.LowHybrid.Factorization.SquarefreeVector.{u_1} n →
    HeckeSkeleton.LowHybrid.Factorization.SquarefreeVector.{u_1}
      (HeckeSkeleton.LowHybrid.Factorization.commonPart.{u_1} n b)
```

## HeckeSkeleton.LowHybrid.Factorization.common_left_disjoint

```lean
∀ (n b : ℕ),
  LE.le.{0} n 1 →
    Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b) 0 ∨
      Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.leftExp n b) 0
```

## HeckeSkeleton.LowHybrid.Factorization.common_right_disjoint

```lean
∀ (n b : ℕ),
  Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b) 0 ∨
    Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.rightExp n b) 0
```

## HeckeSkeleton.LowHybrid.Factorization.completed_cubic_mask

```lean
∀ {ι : Type u_1} (P r c m h t : ι → ℕ) (psi : (ι → ℕ) → ℂ),
  (∀ (a b : ι → ℕ), Eq.{1} (psi fun p => HAdd.hAdd.{0, 0, 0} (a p) (b p)) (HMul.hMul.{0, 0, 0} (psi a) (psi b))) →
    (∀ (a : ι → ℕ), ¬HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} P a → Eq.{1} (psi a) 0) →
      Eq.{1}
        (ite.{1}
          (HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} P fun p =>
            HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (r p) (c p)) (h p))
              (HMul.hMul.{0, 0, 0} 2 (t p)))
          (psi fun p => HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (r p) (c p)) (m p)) 0)
        (ite.{1} (HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} P fun p => HAdd.hAdd.{0, 0, 0} (h p) (t p))
          (HMul.hMul.{0, 0, 0} (psi r) (psi fun p => HAdd.hAdd.{0, 0, 0} (c p) (m p))) 0)
```

## HeckeSkeleton.LowHybrid.Factorization.completed_quadratic_symbol

```lean
∀ {ι : Type u_1} (row n b : ι → ℕ) (chi : (ι → ℕ) → ℂ),
  (∀ (a b : ι → ℕ), Eq.{1} (chi fun p => HAdd.hAdd.{0, 0, 0} (a p) (b p)) (HMul.hMul.{0, 0, 0} (chi a) (chi b))) →
    (∀ (a : ι → ℕ),
        Eq.{1} (HPow.hPow.{0, 0, 0} (chi a) 6)
          (ite.{1} (HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} row a) 1 0)) →
      Eq.{1} (HPow.hPow.{0, 0, 0} (chi fun p => HAdd.hAdd.{0, 0, 0} (n p) (b p)) 3)
        (ite.{1}
          (HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} row
            (HeckeSkeleton.LowHybrid.Factorization.maskPart.{u_1} n b))
          (HPow.hPow.{0, 0, 0} (chi (HeckeSkeleton.LowHybrid.Factorization.residualProduct.{u_1} n b)) 3) 0)
```

## HeckeSkeleton.LowHybrid.Factorization.completed_row_mask

```lean
∀ {ι : Type u_1} (row n b : ι → ℕ),
  HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} row
      (HeckeSkeleton.LowHybrid.Factorization.maskPart.{u_1} n b) ↔
    HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} row
        (HeckeSkeleton.LowHybrid.Factorization.commonPart.{u_1} n b) ∧
      HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} row
        (HeckeSkeleton.LowHybrid.Factorization.squarePart.{u_1} b)
```

## HeckeSkeleton.LowHybrid.Factorization.completed_square_decomposition

```lean
∀ {ι : Type u_1} (n b : ι → ℕ),
  Eq.{u_1 + 1} (fun p => HAdd.hAdd.{0, 0, 0} (n p) (b p)) fun p =>
    HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.residualProduct.{u_1} n b p)
      (HMul.hMul.{0, 0, 0} 2 (HeckeSkeleton.LowHybrid.Factorization.maskPart.{u_1} n b p))
```

## HeckeSkeleton.LowHybrid.Factorization.completed_square_exponent

```lean
∀ (n b : ℕ),
  Eq.{1} (HAdd.hAdd.{0, 0, 0} n b)
    (HAdd.hAdd.{0, 0, 0}
      (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.leftExp n b)
        (HeckeSkeleton.LowHybrid.Factorization.rightExp n b))
      (HMul.hMul.{0, 0, 0} 2
        (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b)
          (HeckeSkeleton.LowHybrid.Factorization.squareExp b))))
```

## HeckeSkeleton.LowHybrid.Factorization.coprimeVector_add_right

```lean
∀ {ι : Type u_1} (P a b : ι → ℕ),
  (HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} P fun p => HAdd.hAdd.{0, 0, 0} (a p) (b p)) ↔
    HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} P a ∧
      HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} P b
```

## HeckeSkeleton.LowHybrid.Factorization.cubicColumn_decomposition

```lean
∀ {ι : Type u_1} (n b r c' : ι → ℕ),
  (∀ (p : ι),
      Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.commonPart.{u_1} n b p) (HAdd.hAdd.{0, 0, 0} (r p) (c' p))) →
    Eq.{u_1 + 1} n fun p =>
      HAdd.hAdd.{0, 0, 0} (r p)
        (HAdd.hAdd.{0, 0, 0} (c' p) (HeckeSkeleton.LowHybrid.Factorization.leftPart.{u_1} n b p))
```

## HeckeSkeleton.LowHybrid.Factorization.cubicColumn_factors_coprime

```lean
∀ {ι : Type u_1} (n b r c' : ι → ℕ),
  HeckeSkeleton.LowHybrid.Factorization.SquarefreeVector.{u_1} n →
    (∀ (p : ι),
        Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.commonPart.{u_1} n b p) (HAdd.hAdd.{0, 0, 0} (r p) (c' p))) →
      HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} c'
        (HeckeSkeleton.LowHybrid.Factorization.leftPart.{u_1} n b)
```

## HeckeSkeleton.LowHybrid.Factorization.cubicColumn_squarefree

```lean
∀ {ι : Type u_1} (n b r c' : ι → ℕ),
  HeckeSkeleton.LowHybrid.Factorization.SquarefreeVector.{u_1} n →
    (∀ (p : ι),
        Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.commonPart.{u_1} n b p) (HAdd.hAdd.{0, 0, 0} (r p) (c' p))) →
      HeckeSkeleton.LowHybrid.Factorization.SquarefreeVector.{u_1} fun p =>
        HAdd.hAdd.{0, 0, 0} (c' p) (HeckeSkeleton.LowHybrid.Factorization.leftPart.{u_1} n b p)
```

## HeckeSkeleton.LowHybrid.Factorization.cubic_mask_equivalence

```lean
∀ {ι : Type u_1} (P r c m h t : ι → ℕ),
  (HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} P fun p =>
      HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (r p) (c p)) (m p)) →
    ((HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} P fun p =>
        HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (r p) (c p)) (h p))
          (HMul.hMul.{0, 0, 0} 2 (t p))) ↔
      HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} P fun p => HAdd.hAdd.{0, 0, 0} (h p) (t p))
```

## HeckeSkeleton.LowHybrid.Factorization.leftExp_le_one

```lean
∀ (n b : ℕ), LE.le.{0} n 1 → LE.le.{0} (HeckeSkeleton.LowHybrid.Factorization.leftExp n b) 1
```

## HeckeSkeleton.LowHybrid.Factorization.leftPart_decomposition

```lean
∀ {ι : Type u_1} (n b : ι → ℕ),
  Eq.{u_1 + 1} n fun p =>
    HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.commonPart.{u_1} n b p)
      (HeckeSkeleton.LowHybrid.Factorization.leftPart.{u_1} n b p)
```

## HeckeSkeleton.LowHybrid.Factorization.leftPart_rightPart_coprime

```lean
∀ {ι : Type u_1} (n b : ι → ℕ),
  HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} (HeckeSkeleton.LowHybrid.Factorization.leftPart.{u_1} n b)
    (HeckeSkeleton.LowHybrid.Factorization.rightPart.{u_1} n b)
```

## HeckeSkeleton.LowHybrid.Factorization.leftPart_squarefree

```lean
∀ {ι : Type u_1} (n b : ι → ℕ),
  HeckeSkeleton.LowHybrid.Factorization.SquarefreeVector.{u_1} n →
    HeckeSkeleton.LowHybrid.Factorization.SquarefreeVector.{u_1}
      (HeckeSkeleton.LowHybrid.Factorization.leftPart.{u_1} n b)
```

## HeckeSkeleton.LowHybrid.Factorization.left_right_disjoint

```lean
∀ (n b : ℕ),
  Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.leftExp n b) 0 ∨
    Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.rightExp n b) 0
```

## HeckeSkeleton.LowHybrid.Factorization.local_factorization_unique

```lean
∀ (n b g t c m h : ℕ),
  LE.le.{0} g 1 →
    Eq.{1} b (HAdd.hAdd.{0, 0, 0} g (HMul.hMul.{0, 0, 0} 2 t)) →
      Eq.{1} n (HAdd.hAdd.{0, 0, 0} c m) →
        Eq.{1} g (HAdd.hAdd.{0, 0, 0} c h) →
          Eq.{1} m 0 ∨ Eq.{1} h 0 →
            Eq.{1} g (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b) ∧
              Eq.{1} t (HeckeSkeleton.LowHybrid.Factorization.squareExp b) ∧
                Eq.{1} c (HeckeSkeleton.LowHybrid.Factorization.commonExp n b) ∧
                  Eq.{1} m (HeckeSkeleton.LowHybrid.Factorization.leftExp n b) ∧
                    Eq.{1} h (HeckeSkeleton.LowHybrid.Factorization.rightExp n b)
```

## HeckeSkeleton.LowHybrid.Factorization.residualProduct_squarefree

```lean
∀ {ι : Type u_1} (n b : ι → ℕ),
  HeckeSkeleton.LowHybrid.Factorization.SquarefreeVector.{u_1} n →
    HeckeSkeleton.LowHybrid.Factorization.SquarefreeVector.{u_1}
      (HeckeSkeleton.LowHybrid.Factorization.residualProduct.{u_1} n b)
```

## HeckeSkeleton.LowHybrid.Factorization.residual_exponent_le_one

```lean
∀ (n b : ℕ),
  LE.le.{0} n 1 →
    LE.le.{0}
      (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.leftExp n b)
        (HeckeSkeleton.LowHybrid.Factorization.rightExp n b))
      1
```

## HeckeSkeleton.LowHybrid.Factorization.rightExp_le_one

```lean
∀ (n b : ℕ), LE.le.{0} (HeckeSkeleton.LowHybrid.Factorization.rightExp n b) 1
```

## HeckeSkeleton.LowHybrid.Factorization.rightPart_decomposition

```lean
∀ {ι : Type u_1} (n b : ι → ℕ),
  Eq.{u_1 + 1} (HeckeSkeleton.LowHybrid.Factorization.squarefreePart.{u_1} b) fun p =>
    HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.commonPart.{u_1} n b p)
      (HeckeSkeleton.LowHybrid.Factorization.rightPart.{u_1} n b p)
```

## HeckeSkeleton.LowHybrid.Factorization.rightPart_squarefree

```lean
∀ {ι : Type u_1} (n b : ι → ℕ),
  HeckeSkeleton.LowHybrid.Factorization.SquarefreeVector.{u_1}
    (HeckeSkeleton.LowHybrid.Factorization.rightPart.{u_1} n b)
```

## HeckeSkeleton.LowHybrid.Factorization.split_left

```lean
∀ (n b : ℕ),
  Eq.{1} n
    (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b)
      (HeckeSkeleton.LowHybrid.Factorization.leftExp n b))
```

## HeckeSkeleton.LowHybrid.Factorization.split_right

```lean
∀ (n b : ℕ),
  Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b)
    (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b)
      (HeckeSkeleton.LowHybrid.Factorization.rightExp n b))
```

## HeckeSkeleton.LowHybrid.Factorization.squarePart_decomposition

```lean
∀ {ι : Type u_1} (b : ι → ℕ),
  Eq.{u_1 + 1} b fun p =>
    HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.squarefreePart.{u_1} b p)
      (HMul.hMul.{0, 0, 0} 2 (HeckeSkeleton.LowHybrid.Factorization.squarePart.{u_1} b p))
```

## HeckeSkeleton.LowHybrid.Factorization.square_extraction

```lean
∀ (b : ℕ),
  Eq.{1} b
    (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b)
      (HMul.hMul.{0, 0, 0} 2 (HeckeSkeleton.LowHybrid.Factorization.squareExp b)))
```

## HeckeSkeleton.LowHybrid.Factorization.squarefreeExp_le_one

```lean
∀ (b : ℕ), LE.le.{0} (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b) 1
```

## HeckeSkeleton.LowHybrid.Factorization.squarefreePart_squarefree

```lean
∀ {ι : Type u_1} (b : ι → ℕ),
  HeckeSkeleton.LowHybrid.Factorization.SquarefreeVector.{u_1}
    (HeckeSkeleton.LowHybrid.Factorization.squarefreePart.{u_1} b)
```

## HeckeSkeleton.LowHybrid.Factorization.vector_factorization_unique

```lean
∀ {ι : Type u_1} (n b g t c m h : ι → ℕ),
  HeckeSkeleton.LowHybrid.Factorization.SquarefreeVector.{u_1} g →
    (∀ (p : ι), Eq.{1} (b p) (HAdd.hAdd.{0, 0, 0} (g p) (HMul.hMul.{0, 0, 0} 2 (t p)))) →
      (∀ (p : ι), Eq.{1} (n p) (HAdd.hAdd.{0, 0, 0} (c p) (m p))) →
        (∀ (p : ι), Eq.{1} (g p) (HAdd.hAdd.{0, 0, 0} (c p) (h p))) →
          HeckeSkeleton.LowHybrid.Factorization.CoprimeVector.{u_1} m h →
            Eq.{u_1 + 1} g (HeckeSkeleton.LowHybrid.Factorization.squarefreePart.{u_1} b) ∧
              Eq.{u_1 + 1} t (HeckeSkeleton.LowHybrid.Factorization.squarePart.{u_1} b) ∧
                Eq.{u_1 + 1} c (HeckeSkeleton.LowHybrid.Factorization.commonPart.{u_1} n b) ∧
                  Eq.{u_1 + 1} m (HeckeSkeleton.LowHybrid.Factorization.leftPart.{u_1} n b) ∧
                    Eq.{u_1 + 1} h (HeckeSkeleton.LowHybrid.Factorization.rightPart.{u_1} n b)
```

## HeckeSkeleton.LowHybrid.NormalForm.sum_zero_extend_box

```lean
∀ {I : Type u_1} [CommMonoid.{u_1} I]
  (support : Finset.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I)) (ts cs ms hs : Finset.{u_1} I),
  support ⊆ HeckeSkeleton.LowHybrid.NormalForm.completedBox.{u_1} ts cs ms hs →
    ∀ (F : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I → ℂ),
      Eq.{1} (∑ v ∈ support, F v)
        (∑ t ∈ ts,
          ∑ c ∈ cs,
            ∑ m ∈ ms,
              ∑ h ∈ hs,
                ite.{1}
                  (Membership.mem.{u_1, u_1} support
                    (Prod.mk.{u_1, u_1} t (Prod.mk.{u_1, u_1} c (Prod.mk.{u_1, u_1} m h))))
                  (F (Prod.mk.{u_1, u_1} t (Prod.mk.{u_1, u_1} c (Prod.mk.{u_1, u_1} m h)))) 0)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.actualDivisorEnvelope_nonneg

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : A → ℝ)
  (hfinite : ∀ (X : ℝ), Set.Finite.{u_2} (Set.ofPred.{u_2} fun a => LE.le.{0} (normI a) X)) (X : ℝ),
  LE.le.{0} 0 (HeckeSkeleton.LowHybrid.PrimeArithmetic.actualDivisorEnvelope.{u_1, u_2} coords normI hfinite X)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.actualDivisorEnvelope_subpower

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LE.le.{0} 1 (normI a)) →
    ∀ (hfinite : ∀ (X : ℝ), Set.Finite.{u_2} (Set.ofPred.{u_2} fun a => LE.le.{0} (normI a) X)),
      HeckeSkeleton.LowHybrid.SubpowerBound
        (HeckeSkeleton.LowHybrid.PrimeArithmetic.actualDivisorEnvelope.{u_1, u_2} coords (⇑normI) hfinite)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.arithmetic_norm_le_of_dvd

```lean
∀ {A : Type u_2} [inst : CommMonoid.{u_2} A] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} A),
  (∀ (x : A), LE.le.{0} 1 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S x)) →
    ∀ {a b : A},
      Dvd.dvd.{u_2} a b →
        LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S a)
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S b)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.arithmetic_quotient_dvd

```lean
∀ {A : Type u_2} [inst : CommMonoid.{u_2} A] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} A) (d k : A),
  Dvd.dvd.{u_2} d k → Dvd.dvd.{u_2} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_2} S d k) k
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.canonical_block_bounds

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ)))
  (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} A),
  (∀ (x : A), LE.le.{0} 1 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S x)) →
    ∀ {columns cubes : Finset.{u_2} A} (N B : ℝ),
      (∀ (n : A),
          Membership.mem.{u_2, u_2} columns n →
            HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords n ∧
              LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S n) N) →
        (∀ (b : A),
            Membership.mem.{u_2, u_2} cubes b →
              LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S b) B) →
          ∀ {r : A} {v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_2} A},
            Membership.mem.{u_2, u_2}
                (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_2} S
                  (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_2}
                    (HeckeSkeleton.LowHybrid.PrimeArithmetic.completion.{u_1, u_2} coords columns cubes))
                  r)
                v →
              LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S v.1) B ∧
                LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S v.2.1) N ∧
                  LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S v.2.2.1) N ∧
                    LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S v.2.2.2) B ∧
                      HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords
                          (HMul.hMul.{u_2, u_2, u_2} v.2.2.1 v.2.2.2) ∧
                        LE.le.{0}
                            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S
                              (HMul.hMul.{u_2, u_2, u_2} v.2.2.1 v.2.2.2))
                            (HMul.hMul.{0, 0, 0} N B) ∧
                          HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords
                              (HMul.hMul.{u_2, u_2, u_2} v.2.1 v.2.2.1) ∧
                            LE.le.{0}
                              (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S
                                (HMul.hMul.{u_2, u_2, u_2} v.2.1 v.2.2.1))
                              N
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.canonical_block_residual_squarefree

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ)))
  (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} A) {columns cubes : Finset.{u_2} A},
  (∀ (n : A),
      Membership.mem.{u_2, u_2} columns n → HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords n) →
    ∀ {r : A} {v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_2} A},
      Membership.mem.{u_2, u_2}
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_2} S
            (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_2}
              (HeckeSkeleton.LowHybrid.PrimeArithmetic.completion.{u_1, u_2} coords columns cubes))
            r)
          v →
        HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords (HMul.hMul.{u_2, u_2, u_2} v.2.2.1 v.2.2.2)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.canonical_finite_inputs

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ)))
  (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} A),
  (∀ (x : A), LE.le.{0} 1 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S x)) →
    Eq.{u_2 + 1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_2} S)
        (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords) →
      ∀ (cutoff : ℝ → Finset.{u_2} A),
        (∀ (X : ℝ) (a : A),
            Membership.mem.{u_2, u_2} (cutoff X) a ↔
              LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S a) X) →
          ∀ (K N B L : ℝ) (rows marks columns cubes : Finset.{u_2} A),
            (∀ (k : A),
                Membership.mem.{u_2, u_2} rows k →
                  HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords k ∧
                    LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S k) K) →
              (∀ (p : A),
                  Membership.mem.{u_2, u_2} marks p →
                    HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords p ∧
                      LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S p) L) →
                (∀ (n : A),
                    Membership.mem.{u_2, u_2} columns n →
                      HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords n ∧
                        LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S n) N) →
                  (∀ (b : A),
                      Membership.mem.{u_2, u_2} cubes b →
                        LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S b) B) →
                    HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_2} S
                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) rows marks columns cubes
                      (cutoff K) (cutoff K)
                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.completion.{u_1, u_2} coords columns cubes)
                      (fun x x_1 => cutoff B) (fun x x_1 => cutoff N) (fun x x_1 => cutoff N) (fun x x_1 => cutoff B)
                      (fun x x_1 =>
                        HeckeSkeleton.LowHybrid.PrimeArithmetic.quadraticPairs.{u_1, u_2} coords S cutoff N B)
                      (fun x x_1 => HeckeSkeleton.LowHybrid.PrimeArithmetic.cubicPairs.{u_1, u_2} coords S cutoff N)
                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.squarefreeCutoff.{u_1, u_2} coords cutoff
                        (HMul.hMul.{0, 0, 0} N B))
                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.squarefreeCutoff.{u_1, u_2} coords cutoff N) K
                      (HMul.hMul.{0, 0, 0} N B) N L
                      (HPow.hPow.{0, 0, 0}
                        (HeckeSkeleton.LowHybrid.divisorCountEnvelope.{u_2} cutoff
                          (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords) K)
                        2)
                      (HeckeSkeleton.LowHybrid.divisorCountEnvelope.{u_2} cutoff
                        (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords) (HMul.hMul.{0, 0, 0} N B))
                      (HeckeSkeleton.LowHybrid.divisorCountEnvelope.{u_2} cutoff
                        (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords) N)
                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.cutoffHarmonic.{u_2} S cutoff B)
                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.cutoffHarmonic.{u_2} S cutoff N)
                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.cutoffHarmonic.{u_2} S cutoff B)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.canonical_support_residual_squarefree

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) {columns cubes : Finset.{u_2} A},
  (∀ (n : A),
      Membership.mem.{u_2, u_2} columns n → HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords n) →
    ∀ {v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_2} A},
      Membership.mem.{u_2, u_2}
          (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_2}
            (HeckeSkeleton.LowHybrid.PrimeArithmetic.completion.{u_1, u_2} coords columns cubes))
          v →
        HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords (HMul.hMul.{u_2, u_2, u_2} v.2.2.1 v.2.2.2)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.card_divisors

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A),
  Eq.{1} (Finset.card.{u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords a))
    (HPow.hPow.{0, 0, 0} 2 (Finset.card.{u_1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.support.{u_1, u_2} coords a)))
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.card_divisors_real

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A),
  Eq.{1} (↑(Finset.card.{u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords a)))
    (HPow.hPow.{0, 0, 0} 2 (Finset.card.{u_1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.support.{u_1, u_2} coords a)))
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.completedSplit_reconstruct

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (x : Prod.{u_2, u_2} A A),
  Eq.{u_2 + 1}
    (HeckeSkeleton.LowHybrid.NormalForm.recombine.{u_2}
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.completedSplit.{u_1, u_2} coords x))
    x
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.completed_residual_squarefree

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (n b : A),
  HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords n →
    HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords
      (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.leftPart.{u_1, u_2} coords n b)
        (HeckeSkeleton.LowHybrid.PrimeArithmetic.rightPart.{u_1, u_2} coords n b))
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.coprime_iff_disjoint_support

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a b : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b ↔
    Disjoint.{u_1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.support.{u_1, u_2} coords a)
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.support.{u_1, u_2} coords b)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.divisor_count_le_actual_envelope

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : A → ℝ)
  (hfinite : ∀ (X : ℝ), Set.Finite.{u_2} (Set.ofPred.{u_2} fun a => LE.le.{0} (normI a) X)) (X : ℝ) (a : A),
  LE.le.{0} (normI a) X →
    LE.le.{0} (↑(Finset.card.{u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords a)))
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.actualDivisorEnvelope.{u_1, u_2} coords normI hfinite X)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.divisor_count_subpower

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LE.le.{0} 1 (normI a)) →
    (∀ (X : ℝ), Set.Finite.{u_2} (Set.ofPred.{u_2} fun a => LE.le.{0} (normI a) X)) →
      ∀ (eta : ℝ),
        LT.lt.{0} 0 eta →
          ∃ C,
            LT.lt.{0} 0 C ∧
              ∀ (a : A),
                LE.le.{0} (↑(Finset.card.{u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords a)))
                  (HMul.hMul.{0, 0, 0} C (HPow.hPow.{0, 0, 0} (normI a) eta))
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.divisor_count_subpower_of_cutoffs

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LE.le.{0} 1 (normI a)) →
    ∀ (cutoff : ℝ → Finset.{u_2} A),
      (∀ (X : ℝ) (a : A), LE.le.{0} (normI a) X → Membership.mem.{u_2, u_2} (cutoff X) a) →
        ∀ (eta : ℝ),
          LT.lt.{0} 0 eta →
            ∃ C,
              LT.lt.{0} 0 C ∧
                ∀ (a : A),
                  LE.le.{0}
                    (↑(Finset.card.{u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords a)))
                    (HMul.hMul.{0, 0, 0} C (HPow.hPow.{0, 0, 0} (normI a) eta))
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.divisor_dvd

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a d : A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords a) d → Dvd.dvd.{u_2} d a
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.divisor_envelope_subpower

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LE.le.{0} 1 (normI a)) →
    (∀ (X : ℝ), Set.Finite.{u_2} (Set.ofPred.{u_2} fun a => LE.le.{0} (normI a) X)) →
      ∀ (cutoff : ℝ → Finset.{u_2} A),
        (∀ (X : ℝ), LE.le.{0} 1 X → ∀ (a : A), Membership.mem.{u_2, u_2} (cutoff X) a → LE.le.{0} (normI a) X) →
          HeckeSkeleton.LowHybrid.SubpowerBound
            (HeckeSkeleton.LowHybrid.divisorCountEnvelope.{u_2} cutoff
              (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords))
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.divisor_pair_count_le

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ)))
  (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} A),
  (∀ (x : A), LE.le.{0} 1 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S x)) →
    Eq.{u_2 + 1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_2} S)
        (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords) →
      ∀ (cutoff : ℝ → Finset.{u_2} A),
        (∀ (X : ℝ) (a : A),
            Membership.mem.{u_2, u_2} (cutoff X) a ↔
              LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S a) X) →
          ∀ (K : ℝ) (k : A),
            LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S k) K →
              LE.le.{0} (↑(Finset.card.{u_2} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisorPairs.{u_2} S k)))
                (HPow.hPow.{0, 0, 0}
                  (HeckeSkeleton.LowHybrid.divisorCountEnvelope.{u_2} cutoff
                    (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords) K)
                  2)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.divisor_pair_norms

```lean
∀ {A : Type u_2} [inst : CommMonoid.{u_2} A] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} A),
  (∀ (x : A), LE.le.{0} 1 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S x)) →
    ∀ {d r k : A},
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisorPairs.{u_2} S k)
          (Prod.mk.{u_2, u_2} d r) →
        LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S d)
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S k) ∧
          LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S r)
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} S k)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.dvd_iff_coordinates_le

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a b : A),
  Dvd.dvd.{u_2} a b ↔
    ∀ (p : ι),
      LE.le.{0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p)
        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.finite_norms_of_cutoffs

```lean
∀ {A : Type u_2} [CommMonoid.{u_2} A] (normI : A → ℝ) (cutoff : ℝ → Finset.{u_2} A),
  (∀ (X : ℝ) (a : A), LE.le.{0} (normI a) X → Membership.mem.{u_2, u_2} (cutoff X) a) →
    ∀ (X : ℝ), Set.Finite.{u_2} (Set.ofPred.{u_2} fun a => LE.le.{0} (normI a) X)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.finite_prime_norms

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : A → ℝ),
  (∀ (X : ℝ), Set.Finite.{u_2} (Set.ofPred.{u_2} fun a => LE.le.{0} (normI a) X)) →
    ∀ (X : ℝ),
      Set.Finite.{u_1}
        (Set.ofPred.{u_1} fun p =>
          LE.le.{0} (normI (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.primeElement.{u_1, u_2} coords p)) X)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.finite_singleton_prime_norms

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : A → ℝ),
  (∀ (X : ℝ), Set.Finite.{u_2} (Set.ofPred.{u_2} fun a => LE.le.{0} (normI a) X)) →
    ∀ (X : ℝ),
      Set.Finite.{u_1}
        (Set.ofPred.{u_1} fun p =>
          LE.le.{0}
            (normI
              (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2} coords
                (Singleton.singleton.{u_1, u_1} p)))
            X)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport_dvd_iff

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (a : A),
  Dvd.dvd.{u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2} coords s) a ↔
    s ⊆ HeckeSkeleton.LowHybrid.PrimeArithmetic.support.{u_1, u_2} coords a
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport_injective

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))),
  Function.Injective.{u_1 + 1, u_2 + 1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2} coords)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport_support_of_squarefree

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) {a : A},
  HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords a →
    Eq.{u_2 + 1}
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2} coords
        (HeckeSkeleton.LowHybrid.PrimeArithmetic.support.{u_1, u_2} coords a))
      a
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.mem_divisors_of_squarefree_dvd

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) {a d : A},
  HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords d →
    Dvd.dvd.{u_2} d a →
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords a) d
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.mem_normCutoff

```lean
∀ {A : Type u_2} [CommMonoid.{u_2} A] (normI : A → ℝ)
  (hfinite : ∀ (X : ℝ), Set.Finite.{u_2} (Set.ofPred.{u_2} fun a => LE.le.{0} (normI a) X)) (X : ℝ) (a : A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.normCutoff.{u_2} normI hfinite X) a ↔
    LE.le.{0} (normI a) X
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.mobius_expansion

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (p k : A),
  Eq.{1} (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords p k) 1 0)
    (∑ d ∈ HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords k,
      ite.{1} (Dvd.dvd.{u_2} d p) (HeckeSkeleton.LowHybrid.PrimeArithmetic.mobius.{u_1, u_2} coords d) 0)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.mobius_norm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A),
  Eq.{1} (Norm.norm.{0} (HeckeSkeleton.LowHybrid.PrimeArithmetic.mobius.{u_1, u_2} coords a)) 1
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.norm_fromSupport_le

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LE.le.{0} 1 (normI a)) →
    ∀ (a : A),
      LE.le.{0}
        (normI
          (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2} coords
            (HeckeSkeleton.LowHybrid.PrimeArithmetic.support.{u_1, u_2} coords a)))
        (normI a)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.norm_le_of_dvd

```lean
∀ {A : Type u_2} [inst : CommMonoid.{u_2} A] (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LE.le.{0} 1 (normI a)) → ∀ {a b : A}, Dvd.dvd.{u_2} a b → LE.le.{0} (normI a) (normI b)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.prime_product_le_norm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LE.le.{0} 1 (normI a)) →
    ∀ (a : A),
      LE.le.{0}
        (∏ p ∈ HeckeSkeleton.LowHybrid.PrimeArithmetic.support.{u_1, u_2} coords a,
          normI (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.primeElement.{u_1, u_2} coords p))
        (normI a)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.product_fiber_card_le_squarefree_divisors

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ)))
  (pairs : Finset.{u_2} (Prod.{u_2, u_2} A A)) (j : A),
  HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords j →
    LE.le.{0} ↑(Finset.card.{u_2} ({u ∈ pairs | Eq.{u_2 + 1} (HMul.hMul.{u_2, u_2, u_2} u.1 u.2) j}))
      ↑(Finset.card.{u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords j))
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.quotient_spec

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (d k : A),
  Dvd.dvd.{u_2} d k →
    Eq.{u_2 + 1} (HMul.hMul.{u_2, u_2, u_2} d (HeckeSkeleton.LowHybrid.PrimeArithmetic.quotient.{u_1, u_2} coords d k))
      k
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.singleton_fromSupport_injective

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))),
  Function.Injective.{u_1 + 1, u_2 + 1} fun p =>
    HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2} coords (Singleton.singleton.{u_1, u_1} p)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.squarefree_mem_divisors

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a d : A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords a) d →
    HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords d
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.squarefree_of_dvd

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) {a b : A},
  Dvd.dvd.{u_2} a b →
    HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords b →
      HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords a
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.support_fromSupport

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι),
  Eq.{u_1 + 1}
    (HeckeSkeleton.LowHybrid.PrimeArithmetic.support.{u_1, u_2} coords
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2} coords s))
    s
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.support_subset_of_dvd

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) {a b : A},
  Dvd.dvd.{u_2} a b →
    HeckeSkeleton.LowHybrid.PrimeArithmetic.support.{u_1, u_2} coords a ⊆
      HeckeSkeleton.LowHybrid.PrimeArithmetic.support.{u_1, u_2} coords b
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.swapped_product_fiber_card_le_squarefree_divisors

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ)))
  (pairs : Finset.{u_2} (Prod.{u_2, u_2} A A)) (j : A),
  HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords j →
    LE.le.{0} ↑(Finset.card.{u_2} ({u ∈ pairs | Eq.{u_2 + 1} (HMul.hMul.{u_2, u_2, u_2} u.2 u.1) j}))
      ↑(Finset.card.{u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.divisors.{u_1, u_2} coords j))
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.valuation_fromSupport

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (p : ι),
  Eq.{1}
    ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
        (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2} coords s))
      p)
    (ite.{1} (Membership.mem.{u_1, u_1} s p) 1 0)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.valuation_mapTwo

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (f : ℕ → ℕ → ℕ) (hf : Eq.{1} (f 0 0) 0)
  (a b : A) (p : ι),
  Eq.{1}
    ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
        (HeckeSkeleton.LowHybrid.PrimeArithmetic.mapTwo.{u_1, u_2} coords f hf a b))
      p)
    (f ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p)
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p))
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.valuation_quotient

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (d k : A) (p : ι),
  Eq.{1}
    ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords
        (HeckeSkeleton.LowHybrid.PrimeArithmetic.quotient.{u_1, u_2} coords d k))
      p)
    (HSub.hSub.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords k) p)
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords d) p))
```

## HeckeSkeleton.LowHybrid.WeightedBlock.cHarmonic_nonneg

```lean
∀ {I : Type u} (b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I) (rows : Finset.{u} I) (Q S Rbudget A : ℝ),
  HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.{u, v} b rows Q S Rbudget A →
    LE.le.{0} 0 (HeckeSkeleton.LowHybrid.WeightedBlock.cHarmonic.{u, v} b)
```

## HeckeSkeleton.LowHybrid.WeightedBlock.energy_le

```lean
∀ {I : Type u} (b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I) (rows : Finset.{u} I) (Q S Rbudget A : ℝ),
  LE.le.{0} 0 Q →
    LE.le.{0} 0 S →
      LE.le.{0} 0 Rbudget →
        LE.le.{0} 0 A →
          HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.{u, v} b rows Q S Rbudget A →
            LE.le.{0}
              (∑ i ∈ rows, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (HeckeSkeleton.LowHybrid.WeightedBlock.row.{u, v} b i)) 2)
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} Q S) Rbudget) A)
                    (HPow.hPow.{0, 0, 0} (HeckeSkeleton.LowHybrid.WeightedBlock.tHarmonic.{u, v} b) 2))
                  (HeckeSkeleton.LowHybrid.WeightedBlock.cHarmonic.{u, v} b))
                (HeckeSkeleton.LowHybrid.WeightedBlock.hHarmonic.{u, v} b))
```

## HeckeSkeleton.LowHybrid.WeightedBlock.energy_le_uniform_harmonics

```lean
∀ {I : Type u} (b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I) (rows : Finset.{u} I)
  (Q S Rbudget A Ht Hc Hh : ℝ),
  LE.le.{0} 0 Q →
    LE.le.{0} 0 S →
      LE.le.{0} 0 Rbudget →
        LE.le.{0} 0 A →
          LE.le.{0} 0 Ht →
            LE.le.{0} 0 Hc →
              LE.le.{0} 0 Hh →
                HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.{u, v} b rows Q S Rbudget A →
                  LE.le.{0} (HeckeSkeleton.LowHybrid.WeightedBlock.tHarmonic.{u, v} b) Ht →
                    LE.le.{0} (HeckeSkeleton.LowHybrid.WeightedBlock.cHarmonic.{u, v} b) Hc →
                      LE.le.{0} (HeckeSkeleton.LowHybrid.WeightedBlock.hHarmonic.{u, v} b) Hh →
                        LE.le.{0}
                          (∑ i ∈ rows,
                            HPow.hPow.{0, 0, 0} (Norm.norm.{0} (HeckeSkeleton.LowHybrid.WeightedBlock.row.{u, v} b i))
                              2)
                          (HMul.hMul.{0, 0, 0}
                            (HMul.hMul.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} Q S) Rbudget) A)
                                (HPow.hPow.{0, 0, 0} Ht 2))
                              Hc)
                            Hh)
```

## HeckeSkeleton.LowHybrid.WeightedBlock.hHarmonic_nonneg

```lean
∀ {I : Type u} (b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I) (rows : Finset.{u} I) (Q S Rbudget A : ℝ),
  HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.{u, v} b rows Q S Rbudget A →
    LE.le.{0} 0 (HeckeSkeleton.LowHybrid.WeightedBlock.hHarmonic.{u, v} b)
```

## HeckeSkeleton.LowHybrid.WeightedBlock.tHarmonic_nonneg

```lean
∀ {I : Type u} (b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I) (rows : Finset.{u} I) (Q S Rbudget A : ℝ),
  HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.{u, v} b rows Q S Rbudget A →
    LE.le.{0} 0 (HeckeSkeleton.LowHybrid.WeightedBlock.tHarmonic.{u, v} b)
```

## HeckeSkeleton.LowHybrid.annular_normalized_mass_le._simp_1_1

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 2] [NeZero.{u_2} 2], Eq.{1} (Eq.{u_2 + 1} 2 0) False
```

## HeckeSkeleton.LowHybrid.annular_normalized_mass_le._simp_1_2

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 3] [NeZero.{u_2} 3], Eq.{1} (Eq.{u_2 + 1} 3 0) False
```

## HeckeSkeleton.LowHybrid.annular_normalized_mass_le._simp_1_3

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 4] [NeZero.{u_2} 4], Eq.{1} (Eq.{u_2 + 1} 4 0) False
```

## HeckeSkeleton.LowHybrid.annular_normalized_mass_le._simp_1_4

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [NoZeroDivisors.{u_1} M₀] {a b : M₀},
  Ne.{u_1 + 1} a 0 → Ne.{u_1 + 1} b 0 → Eq.{1} (Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} a b) 0) False
```

## HeckeSkeleton.LowHybrid.annular_normalized_mass_le._simp_1_5

```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀} [IsReduced.{u_1} M₀] (n : ℕ),
  Ne.{u_1 + 1} a 0 → Eq.{1} (Eq.{u_1 + 1} (HPow.hPow.{u_1, 0, u_1} a n) 0) False
```

## HeckeSkeleton.LowHybrid.annular_normalized_mass_le._simp_1_6

```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero.{u_3} G₀] {a : G₀} (n : ℤ),
  Ne.{u_3 + 1} a 0 → Eq.{1} (Eq.{u_3 + 1} (HPow.hPow.{u_3, 0, u_3} a n) 0) False
```

## HeckeSkeleton.LowHybrid.annular_normalized_mass_le._simp_1_7

```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne.{u_1} R] [CharZero.{u_1} R] (n : ℕ),
  Eq.{1} (Eq.{u_1 + 1} (HAdd.hAdd.{u_1, u_1, u_1} (↑n) 1) 0) False
```

## HeckeSkeleton.LowHybrid.betaSquaredMass.eq_1

```lean
∀ {I : Type u_1} (beta : I → I → ℂ) (columns cubes : Finset.{u_1} I),
  Eq.{1} (HeckeSkeleton.LowHybrid.betaSquaredMass.{u_1} beta columns cubes)
    ↑(Finset.sup.{0, u_1} (SProd.sprod.{u_1, u_1, u_1} columns cubes) fun u =>
        HPow.hPow.{0, 0, 0} (NNNorm.nnnorm.{0} (beta u.1 u.2)) 2)
```

## HeckeSkeleton.LowHybrid.completedBlock._proof_1

```lean
(HAdd.hAdd.{0, 0, 0} 1 1).AtLeastTwo
```

## HeckeSkeleton.LowHybrid.completedBlock._proof_2

```lean
(HAdd.hAdd.{0, 0, 0} 2 1).AtLeastTwo
```

## HeckeSkeleton.LowHybrid.divisorCountEnvelope.eq_1

```lean
∀ {I : Type u_1} (cutoff : ℝ → Finset.{u_1} I) (divisors : I → Finset.{u_1} I) (X : ℝ),
  Eq.{1} (HeckeSkeleton.LowHybrid.divisorCountEnvelope.{u_1} cutoff divisors X)
    ↑(Finset.sup.{0, u_1} (cutoff X) fun i => Finset.card.{u_1} (divisors i))
```

## HeckeSkeleton.LowHybrid.divisorEnvelopeOfCounting._proof_1

```lean
∀ {A : Type u_1} [inst : CommMonoid.{u_1} A] (normI : MonoidHom.{u_1, 0} A ℝ) (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    ∀ (Ccount : ℝ),
      HeckeSkeleton.LowHybrid.LinearNormCounting.{u_1} q Ccount →
        ∀ (X : ℝ), Set.Finite.{u_1} (Set.ofPred.{u_1} fun i => LE.le.{0} (normI i) X)
```

## HeckeSkeleton.LowHybrid.factorized_column_mass_le._simp_1_1

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 2] [NeZero.{u_2} 2], Eq.{1} (Eq.{u_2 + 1} 2 0) False
```

## HeckeSkeleton.LowHybrid.factorized_column_mass_le._simp_1_2

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 3] [NeZero.{u_2} 3], Eq.{1} (Eq.{u_2 + 1} 3 0) False
```

## HeckeSkeleton.LowHybrid.factorized_column_mass_le._simp_1_3

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 4] [NeZero.{u_2} 4], Eq.{1} (Eq.{u_2 + 1} 4 0) False
```

## HeckeSkeleton.LowHybrid.factorized_column_mass_le._simp_1_4

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [NoZeroDivisors.{u_1} M₀] {a b : M₀},
  Ne.{u_1 + 1} a 0 → Ne.{u_1 + 1} b 0 → Eq.{1} (Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} a b) 0) False
```

## HeckeSkeleton.LowHybrid.factorized_column_mass_le._simp_1_5

```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀} [IsReduced.{u_1} M₀] (n : ℕ),
  Ne.{u_1 + 1} a 0 → Eq.{1} (Eq.{u_1 + 1} (HPow.hPow.{u_1, 0, u_1} a n) 0) False
```

## HeckeSkeleton.LowHybrid.factorized_column_mass_le._simp_1_6

```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero.{u_3} G₀] {a : G₀} (n : ℤ),
  Ne.{u_3 + 1} a 0 → Eq.{1} (Eq.{u_3 + 1} (HPow.hPow.{u_3, 0, u_3} a n) 0) False
```

## HeckeSkeleton.LowHybrid.factorized_column_mass_le._simp_1_7

```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne.{u_1} R] [CharZero.{u_1} R] (n : ℕ),
  Eq.{1} (Eq.{u_1 + 1} (HAdd.hAdd.{u_1, u_1, u_1} (↑n) 1) 0) False
```

## HeckeSkeleton.LowHybrid.fixed_block_scalar_ledger._simp_1_1

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 2] [NeZero.{u_2} 2], Eq.{1} (Eq.{u_2 + 1} 2 0) False
```

## HeckeSkeleton.LowHybrid.fixed_block_scalar_ledger._simp_1_2

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 3] [NeZero.{u_2} 3], Eq.{1} (Eq.{u_2 + 1} 3 0) False
```

## HeckeSkeleton.LowHybrid.fixed_block_scalar_ledger._simp_1_3

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 4] [NeZero.{u_2} 4], Eq.{1} (Eq.{u_2 + 1} 4 0) False
```

## HeckeSkeleton.LowHybrid.fixed_block_scalar_ledger._simp_1_4

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [NoZeroDivisors.{u_1} M₀] {a b : M₀},
  Ne.{u_1 + 1} a 0 → Ne.{u_1 + 1} b 0 → Eq.{1} (Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} a b) 0) False
```

## HeckeSkeleton.LowHybrid.fixed_block_scalar_ledger._simp_1_5

```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀} [IsReduced.{u_1} M₀] (n : ℕ),
  Ne.{u_1 + 1} a 0 → Eq.{1} (Eq.{u_1 + 1} (HPow.hPow.{u_1, 0, u_1} a n) 0) False
```

## HeckeSkeleton.LowHybrid.fixed_block_scalar_ledger._simp_1_6

```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero.{u_3} G₀] {a : G₀} (n : ℤ),
  Ne.{u_3 + 1} a 0 → Eq.{1} (Eq.{u_3 + 1} (HPow.hPow.{u_3, 0, u_3} a n) 0) False
```

## HeckeSkeleton.LowHybrid.fixed_block_scalar_ledger._simp_1_7

```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne.{u_1} R] [CharZero.{u_1} R] (n : ℕ),
  Eq.{1} (Eq.{u_1 + 1} (HAdd.hAdd.{u_1, u_1, u_1} (↑n) 1) 0) False
```

## HeckeSkeleton.LowHybrid.harmonicEnvelope.eq_1

```lean
∀ (C X : ℝ),
  Eq.{1} (HeckeSkeleton.LowHybrid.harmonicEnvelope C X) (HMul.hMul.{0, 0, 0} C (HAdd.hAdd.{0, 0, 0} 1 (Real.log X)))
```

## HeckeSkeleton.LowHybrid.harmonicPartial.eq_1

```lean
∀ (N : ℕ),
  Eq.{1} (HeckeSkeleton.LowHybrid.harmonicPartial N)
    (∑ n ∈ Finset.range N, HDiv.hDiv.{0, 0, 0} 1 (HAdd.hAdd.{0, 0, 0} (↑n) 1))
```

## HeckeSkeleton.LowHybrid.hybridEnergy.eq_1

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ) (a : I → ℂ)
  (beta : I → I → ℂ) (rows marks columns cubes : Finset.{u_1} I),
  Eq.{1} (HeckeSkeleton.LowHybrid.hybridEnergy.{u_1} symbol cop normI a beta rows marks columns cubes)
    (∑ k ∈ rows,
      HPow.hPow.{0, 0, 0}
        (Norm.norm.{0} (HeckeSkeleton.LowHybrid.hybridRow.{u_1} symbol cop normI a beta marks columns cubes k)) 2)
```

## HeckeSkeleton.LowHybrid.hybridEnergy_beta_bound_of_unit._simp_1_1

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 2] [NeZero.{u_2} 2], Eq.{1} (Eq.{u_2 + 1} 2 0) False
```

## HeckeSkeleton.LowHybrid.hybridEnergy_beta_bound_of_unit._simp_1_2

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 3] [NeZero.{u_2} 3], Eq.{1} (Eq.{u_2 + 1} 3 0) False
```

## HeckeSkeleton.LowHybrid.hybridEnergy_beta_bound_of_unit._simp_1_3

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 4] [NeZero.{u_2} 4], Eq.{1} (Eq.{u_2 + 1} 4 0) False
```

## HeckeSkeleton.LowHybrid.hybridEnergy_beta_bound_of_unit._simp_1_4

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [NoZeroDivisors.{u_1} M₀] {a b : M₀},
  Ne.{u_1 + 1} a 0 → Ne.{u_1 + 1} b 0 → Eq.{1} (Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} a b) 0) False
```

## HeckeSkeleton.LowHybrid.hybridEnergy_beta_bound_of_unit._simp_1_5

```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀} [IsReduced.{u_1} M₀] (n : ℕ),
  Ne.{u_1 + 1} a 0 → Eq.{1} (Eq.{u_1 + 1} (HPow.hPow.{u_1, 0, u_1} a n) 0) False
```

## HeckeSkeleton.LowHybrid.hybridEnergy_beta_bound_of_unit._simp_1_6

```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero.{u_3} G₀] {a : G₀} (n : ℤ),
  Ne.{u_3 + 1} a 0 → Eq.{1} (Eq.{u_3 + 1} (HPow.hPow.{u_3, 0, u_3} a n) 0) False
```

## HeckeSkeleton.LowHybrid.hybridEnergy_beta_bound_of_unit._simp_1_7

```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne.{u_1} R] [CharZero.{u_1} R] (n : ℕ),
  Eq.{1} (Eq.{u_1 + 1} (HAdd.hAdd.{u_1, u_1, u_1} (↑n) 1) 0) False
```

## HeckeSkeleton.LowHybrid.hybridRow.eq_1

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ) (a : I → ℂ)
  (beta : I → I → ℂ) (marks columns cubes : Finset.{u_1} I) (k : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.hybridRow.{u_1} symbol cop normI a beta marks columns cubes k)
    (∑ P ∈ marks,
      HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (a P) ↑√(normI P)) (ite.{1} (cop P k) 1 0))
        (∑ n ∈ columns,
          ∑ b ∈ cubes,
            HMul.hMul.{0, 0, 0} (beta n b)
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (symbol k (HMul.hMul.{u_1, u_1, u_1} n b)) 3)
                  (HPow.hPow.{0, 0, 0} (symbol P n) (-2)))
                (ite.{1} (cop P b) 1 0))))
```

## HeckeSkeleton.LowHybrid.linear_norm_counting_norm_one_le._proof_1_1

```lean
∀ {I : Type u_1} (q : I → ℕ) (i : I), ¬LE.le.{0} 1 (q i) → ¬Eq.{1} (q i) 0 → False
```

## HeckeSkeleton.LowHybrid.reciprocal_grid_sum._simp_1_1

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 2] [NeZero.{u_2} 2], Eq.{1} (Eq.{u_2 + 1} 2 0) False
```

## HeckeSkeleton.LowHybrid.reciprocal_grid_sum._simp_1_2

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 3] [NeZero.{u_2} 3], Eq.{1} (Eq.{u_2 + 1} 3 0) False
```

## HeckeSkeleton.LowHybrid.reciprocal_grid_sum._simp_1_3

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 4] [NeZero.{u_2} 4], Eq.{1} (Eq.{u_2 + 1} 4 0) False
```

## HeckeSkeleton.LowHybrid.reciprocal_grid_sum._simp_1_4

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [NoZeroDivisors.{u_1} M₀] {a b : M₀},
  Ne.{u_1 + 1} a 0 → Ne.{u_1 + 1} b 0 → Eq.{1} (Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} a b) 0) False
```

## HeckeSkeleton.LowHybrid.reciprocal_grid_sum._simp_1_5

```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀} [IsReduced.{u_1} M₀] (n : ℕ),
  Ne.{u_1 + 1} a 0 → Eq.{1} (Eq.{u_1 + 1} (HPow.hPow.{u_1, 0, u_1} a n) 0) False
```

## HeckeSkeleton.LowHybrid.reciprocal_grid_sum._simp_1_6

```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero.{u_3} G₀] {a : G₀} (n : ℤ),
  Ne.{u_3 + 1} a 0 → Eq.{1} (Eq.{u_3 + 1} (HPow.hPow.{u_3, 0, u_3} a n) 0) False
```

## HeckeSkeleton.LowHybrid.reciprocal_grid_sum._simp_1_7

```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne.{u_1} R] [CharZero.{u_1} R] (n : ℕ),
  Eq.{1} (Eq.{u_1 + 1} (HAdd.hAdd.{u_1, u_1, u_1} (↑n) 1) 0) False
```

## HeckeSkeleton.LowHybrid.reciprocal_sum_le_harmonic_of_prefix_count._proof_1_10

```lean
∀ {I : Type u_1} (q : I → ℕ) (n : ℕ) (i : I),
  LE.le.{0} 1 (q i) → Eq.{1} (HSub.hSub.{0, 0, 0} (q i) 1) n → ¬Eq.{1} (q i) (HAdd.hAdd.{0, 0, 0} n 1) → False
```

## HeckeSkeleton.LowHybrid.reciprocal_sum_le_harmonic_of_prefix_count._proof_1_2

```lean
∀ {I : Type u_1} (q : I → ℕ) (N : ℕ) (i : I),
  LE.le.{0} 1 (q i) → LE.le.{0} (q i) N → ¬LT.lt.{0} (HSub.hSub.{0, 0, 0} (q i) 1) N → False
```

## HeckeSkeleton.LowHybrid.reciprocal_sum_le_harmonic_of_prefix_count._proof_1_6

```lean
∀ {I : Type u_1} (q : I → ℕ) (n : ℕ) (i : I),
  LT.lt.{0} (HSub.hSub.{0, 0, 0} (q i) 1) n → LE.le.{0} 1 (q i) → ¬LE.le.{0} (q i) n → False
```

## HeckeSkeleton.LowHybrid.reciprocal_sum_le_harmonic_of_prefix_count._proof_1_9

```lean
∀ {I : Type u_1} (q : I → ℕ) (n : ℕ) (i : I),
  LE.le.{0} (q i) n → LE.le.{0} 1 (q i) → ¬LT.lt.{0} (HSub.hSub.{0, 0, 0} (q i) 1) n → False
```

## HeckeSkeleton.LowHybrid.reciprocal_sum_le_harmonic_of_prefix_count._simp_1_1

```lean
∀ {n m : ℕ}, Eq.{1} (Membership.mem.{0, 0} (Finset.range n) m) (LT.lt.{0} m n)
```

## HeckeSkeleton.LowHybrid.reciprocal_sum_le_harmonic_of_prefix_count._simp_1_3

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred.{u_1 + 1} p] {s : Finset.{u_1} α} {a : α},
  Eq.{1} (Membership.mem.{u_1, u_1} (Finset.filter.{u_1} p s) a) (Membership.mem.{u_1, u_1} s a ∧ p a)
```

## HeckeSkeleton.LowHybrid.row_local_positive_transpose._simp_1_1

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred.{u_1 + 1} p] {s : Finset.{u_1} α} {a : α},
  Eq.{1} (Membership.mem.{u_1, u_1} (Finset.filter.{u_1} p s) a) (Membership.mem.{u_1, u_1} s a ∧ p a)
```

## HeckeSkeleton.LowHybrid.row_powerset_filter_eq_common_powerset._simp_1_1

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred.{u_1 + 1} p] {s : Finset.{u_1} α} {a : α},
  Eq.{1} (Membership.mem.{u_1, u_1} (Finset.filter.{u_1} p s) a) (Membership.mem.{u_1, u_1} s a ∧ p a)
```

## HeckeSkeleton.LowHybrid.row_powerset_filter_eq_common_powerset._simp_1_2

```lean
∀ {α : Type u_1} {s t : Finset.{u_1} α}, Eq.{1} (Membership.mem.{u_1, u_1} (Finset.powerset.{u_1} t) s) (s ⊆ t)
```

## HeckeSkeleton.LowHybrid.row_powerset_filter_eq_common_powerset._simp_1_3

```lean
∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] {s t u : Finset.{u_1} α},
  Eq.{1} (s ⊆ Inter.inter.{u_1} t u) (s ⊆ t ∧ s ⊆ u)
```

## HeckeSkeleton.LowHybrid.sum_mul_le_of_prefix_bound._proof_1_1

```lean
∀ (N n : ℕ), LT.lt.{0} n (HSub.hSub.{0, 0, 0} N 1) → ¬LE.le.{0} (HAdd.hAdd.{0, 0, 0} n 1) N → False
```

## HeckeSkeleton.LowHybrid.support_coprime_mask_eq_mobius_sum._simp_1_1

```lean
∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] {s t : Finset.{u_1} α},
  Eq.{1} (Disjoint.{u_1} s t) (Eq.{u_1 + 1} (Inter.inter.{u_1} s t) EmptyCollection.emptyCollection.{u_1})
```

## HeckeSkeleton.LowHybrid.two_row_local_cauchy._simp_1_1

```lean
∀ {ι : Type u_1} {R : Type u_4} [inst : NonUnitalNonAssocSemiring.{u_4} R] (s : Finset.{u_1} ι) (f : ι → R)
  (a : R), Eq.{u_4 + 1} (∑ i ∈ s, HMul.hMul.{u_4, u_4, u_4} a (f i)) (HMul.hMul.{u_4, u_4, u_4} a (∑ i ∈ s, f i))
```

## HeckeSkeleton.LowHybrid.weighted_sum_sq._simp_1_1

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 2] [NeZero.{u_2} 2], Eq.{1} (Eq.{u_2 + 1} 2 0) False
```

## HeckeSkeleton.LowHybrid.weighted_sum_sq._simp_1_2

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 3] [NeZero.{u_2} 3], Eq.{1} (Eq.{u_2 + 1} 3 0) False
```

## HeckeSkeleton.LowHybrid.weighted_sum_sq._simp_1_3

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 4] [NeZero.{u_2} 4], Eq.{1} (Eq.{u_2 + 1} 4 0) False
```

## HeckeSkeleton.LowHybrid.weighted_sum_sq._simp_1_4

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [NoZeroDivisors.{u_1} M₀] {a b : M₀},
  Ne.{u_1 + 1} a 0 → Ne.{u_1 + 1} b 0 → Eq.{1} (Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} a b) 0) False
```

## HeckeSkeleton.LowHybrid.weighted_sum_sq._simp_1_5

```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀} [IsReduced.{u_1} M₀] (n : ℕ),
  Ne.{u_1 + 1} a 0 → Eq.{1} (Eq.{u_1 + 1} (HPow.hPow.{u_1, 0, u_1} a n) 0) False
```

## HeckeSkeleton.LowHybrid.weighted_sum_sq._simp_1_6

```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero.{u_3} G₀] {a : G₀} (n : ℤ),
  Ne.{u_3 + 1} a 0 → Eq.{1} (Eq.{u_3 + 1} (HPow.hPow.{u_3, 0, u_3} a n) 0) False
```

## HeckeSkeleton.LowHybrid.weighted_sum_sq._simp_1_7

```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne.{u_1} R] [CharZero.{u_1} R] (n : ℕ),
  Eq.{1} (Eq.{u_1 + 1} (HAdd.hAdd.{u_1, u_1, u_1} (↑n) 1) 0) False
```

## HeckeSkeleton.LowHybrid.zeroExtendedCubic.congr_simp

```lean
∀ {M : Type u_1} {C : Type u_2} {J : Type u_3} {P : Type u_4} {inst : DecidableEq.{u_1 + 1} M}
  [inst_1 : DecidableEq.{u_1 + 1} M] {inst_2 : DecidableEq.{u_2 + 1} C} [inst_3 : DecidableEq.{u_2 + 1} C]
  (good good_1 : Finset.{max u_2 u_1} (Prod.{u_1, u_2} M C)),
  Eq.{(max u_2 u_1) + 1} good good_1 →
    ∀ (phi phi_1 : Prod.{u_1, u_2} M C → J),
      Eq.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1)} phi phi_1 →
        ∀ (chi chi_1 : P → J → ℂ),
          Eq.{max (u_3 + 1) (u_4 + 1)} chi chi_1 →
            ∀ (a a_1 : M),
              Eq.{u_1 + 1} a a_1 →
                ∀ (a_2 a_3 : C),
                  Eq.{u_2 + 1} a_2 a_3 →
                    ∀ (a_4 a_5 : P),
                      Eq.{u_4 + 1} a_4 a_5 →
                        Eq.{1} (HeckeSkeleton.LowHybrid.zeroExtendedCubic.{u_1, u_2, u_3, u_4} good phi chi a a_2 a_4)
                          (HeckeSkeleton.LowHybrid.zeroExtendedCubic.{u_1, u_2, u_3, u_4} good_1 phi_1 chi_1 a_1 a_3
                            a_5)
```

## HeckeSkeleton.LowHybrid.zeroExtendedCubic.eq_1

```lean
∀ {M : Type u_1} {C : Type u_2} {J : Type u_3} {P : Type u_4} [inst : DecidableEq.{u_1 + 1} M]
  [inst_1 : DecidableEq.{u_2 + 1} C] (good : Finset.{max u_2 u_1} (Prod.{u_1, u_2} M C)) (phi : Prod.{u_1, u_2} M C → J)
  (chi : P → J → ℂ) (m : M) (c : C) (p : P),
  Eq.{1} (HeckeSkeleton.LowHybrid.zeroExtendedCubic.{u_1, u_2, u_3, u_4} good phi chi m c p)
    (ite.{1} (Membership.mem.{max u_2 u_1, max u_1 u_2} good (Prod.mk.{u_1, u_2} m c))
      (chi p (phi (Prod.mk.{u_1, u_2} m c))) 0)
```

## HeckeSkeleton.LowHybrid.zeroExtendedQuadratic.congr_simp

```lean
∀ {K : Type u_1} {M : Type u_2} {H : Type u_3} {J : Type u_4} {inst : DecidableEq.{u_2 + 1} M}
  [inst_1 : DecidableEq.{u_2 + 1} M] {inst_2 : DecidableEq.{u_3 + 1} H} [inst_3 : DecidableEq.{u_3 + 1} H]
  (good good_1 : Finset.{max u_3 u_2} (Prod.{u_2, u_3} M H)),
  Eq.{(max u_3 u_2) + 1} good good_1 →
    ∀ (phi phi_1 : Prod.{u_2, u_3} M H → J),
      Eq.{max (max (u_2 + 1) (u_3 + 1)) (u_4 + 1)} phi phi_1 →
        ∀ (q q_1 : K → J → ℂ),
          Eq.{max (u_1 + 1) (u_4 + 1)} q q_1 →
            ∀ (a a_1 : K),
              Eq.{u_1 + 1} a a_1 →
                ∀ (a_2 a_3 : M),
                  Eq.{u_2 + 1} a_2 a_3 →
                    ∀ (a_4 a_5 : H),
                      Eq.{u_3 + 1} a_4 a_5 →
                        Eq.{1} (HeckeSkeleton.LowHybrid.zeroExtendedQuadratic.{u_1, u_2, u_3, u_4} good phi q a a_2 a_4)
                          (HeckeSkeleton.LowHybrid.zeroExtendedQuadratic.{u_1, u_2, u_3, u_4} good_1 phi_1 q_1 a_1 a_3
                            a_5)
```

## HeckeSkeleton.LowHybrid.zeroExtendedQuadratic.eq_1

```lean
∀ {K : Type u_1} {M : Type u_2} {H : Type u_3} {J : Type u_4} [inst : DecidableEq.{u_2 + 1} M]
  [inst_1 : DecidableEq.{u_3 + 1} H] (good : Finset.{max u_3 u_2} (Prod.{u_2, u_3} M H)) (phi : Prod.{u_2, u_3} M H → J)
  (q : K → J → ℂ) (k : K) (m : M) (h : H),
  Eq.{1} (HeckeSkeleton.LowHybrid.zeroExtendedQuadratic.{u_1, u_2, u_3, u_4} good phi q k m h)
    (ite.{1} (Membership.mem.{max u_3 u_2, max u_2 u_3} good (Prod.mk.{u_2, u_3} m h))
      (q k (phi (Prod.mk.{u_2, u_3} m h))) 0)
```

## HeckeSkeleton.LowHybrid.NormalForm.rotate_three_sums

内部名称：`_private.HeckeSkeleton.LowHybrid.NormalForm.0.HeckeSkeleton.LowHybrid.NormalForm.rotate_three_sums`。

```lean
∀ {A : Type u_2} {B : Type u_3} {C : Type u_4} (as : Finset.{u_2} A) (bs : Finset.{u_3} B) (cs : Finset.{u_4} C)
  (F : A → B → C → ℂ), Eq.{1} (∑ a ∈ as, ∑ b ∈ bs, ∑ c ∈ cs, F a b c) (∑ b ∈ bs, ∑ c ∈ cs, ∑ a ∈ as, F a b c)
```

## HeckeSkeleton.LowHybrid.sum_zero_extension._simp_1_1

内部名称：`_private.HeckeSkeleton.LowHybrid.WeightedSieveBounds.0.HeckeSkeleton.LowHybrid.sum_zero_extension._simp_1_1`。

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred.{u_1 + 1} p] {s : Finset.{u_1} α} {a : α},
  Eq.{1} (Membership.mem.{u_1, u_1} (Finset.filter.{u_1} p s) a) (Membership.mem.{u_1, u_1} s a ∧ p a)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.columns_away

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A}
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D normI Z H v ell z b) (c : A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.columns_coeff

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A}
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D normI Z H v ell z b) (c : A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
    LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.lam.{u_1, u_2} b c)) 1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.columns_lower

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A}
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D normI Z H v ell z b) (c : A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
    LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z v) 2) (normI c)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.columns_sf_norm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A}
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D normI Z H v ell z b) (c : A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
    HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) c ∧
      LE.le.{0} (normI c) (HPow.hPow.{0, 0, 0} Z v)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.cube_lower

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A}
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D normI Z H v ell z b)
  (u : Prod.{u_2, u_2} A A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
    LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z ell) 2)
      (normI
        (HMul.hMul.{u_2, u_2, u_2}
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) u.1)
          u.2))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.cube_upper

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A}
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D normI Z H v ell z b)
  (u : Prod.{u_2, u_2} A A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
    LE.le.{0}
      (normI
        (HMul.hMul.{u_2, u_2, u_2}
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) u.1)
          u.2))
      (HPow.hPow.{0, 0, 0} Z ell)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.input_away

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A}
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D normI Z H v ell z b)
  (u : Prod.{u_2, u_2} A A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) u.2
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.input_phase

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A}
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D normI Z H v ell z b) (c : A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.phase.{u_1, u_2} b c u.1 u.2))
          1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.input_supported

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A}
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D normI Z H v ell z b)
  (u : Prod.{u_2, u_2} A A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) u.1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.marks_away

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A}
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D normI Z H v ell z b) (P : A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.marks_coeff

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A}
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D normI Z H v ell z b) (P : A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
    LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.a₀.{u_1, u_2} b P)) 1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.marks_sf_norm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A}
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D normI Z H v ell z b) (P : A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
    HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P ∧
      LE.le.{0} (normI P) (HPow.hPow.{0, 0, 0} Z z)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.residual_norm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A}
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D normI Z H v ell z b) (d : A),
  Membership.mem.{u_2, u_2}
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.pow.{u_1, u_2} b)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.sup.{u_1, u_2} b)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1, u_2} b))
      d →
    LE.le.{0} (normI d) (HPow.hPow.{0, 0, 0} Z H)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.rho_norm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A}
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D normI Z H v ell z b) (d : A),
  (∀ (p : ι),
      LE.le.{0}
        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) d)
          p)
        1) →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d →
      Eq.{1} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.ρ₀.{u_1, u_2} b d)) 1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.rows_norm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A}
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D normI Z H v ell z b) (k : A),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1, u_2} b) k →
    LE.le.{0} (normI k) (HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.rowBall.{u_1, u_2} self)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.activeInput_reconstruct

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  (∀ (q : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} inputs q →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.1) →
    ∀ (q : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.activeInputBlock.{u_1, u_2} D normI first prefactor atZero
            inputs)
          q →
        Eq.{u_2 + 1} q.1
          (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D)
            (HPow.hPow.{u_2, 0, u_2}
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) q.1)
              3))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.aggregate_source_energy_ledger

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    (∀ (a : A), LE.le.{0} 1 (q a)) →
      ∀ (Ccount : ℝ),
        LT.lt.{0} 0 Ccount →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
            (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b) →
              (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                  (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                  fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b) →
                ∀ (eps eta : ℝ),
                  LT.lt.{0} 0 eps →
                    LT.lt.{0} 0 eta →
                      ∃ C,
                        LT.lt.{0} 0 C ∧
                          ∀ (Z O H v ell S B z T Rrad : ℝ),
                            LE.le.{0} 1 Z →
                              LE.le.{0} 0 O →
                                LE.le.{0} 0 H →
                                  LE.le.{0} 0 v →
                                    LE.le.{0} 0 ell →
                                      LE.le.{0} 0 z →
                                        ∀ (rows : Finset.{u_2} A),
                                          (∀ (k : A),
                                              Membership.mem.{u_2, u_2} rows k →
                                                LE.le.{0}
                                                  (normI
                                                    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1,
                                                        u_2}
                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                          u_2}
                                                        D)
                                                      k))
                                                  (HPow.hPow.{0, 0, 0} Z O)) →
                                            LE.le.{0}
                                                (normI
                                                  (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2}
                                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2}
                                                      D)
                                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2}
                                                      D)))
                                                (HPow.hPow.{0, 0, 0} Z Rrad) →
                                              ∀
                                                (family :
                                                  Prod.{u_2, u_2} A A →
                                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι
                                                      A)
                                                (a :
                                                  (pair : Prod.{u_2, u_2} A A) →
                                                    Membership.mem.{u_2, u_2}
                                                        (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2}
                                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                              u_2}
                                                            D)
                                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1,
                                                              u_2}
                                                            D)
                                                          rows)
                                                        pair →
                                                      HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1,
                                                          u_2}
                                                        D (⇑normI) Z H v ell z (family pair)),
                                                (∀ (pair : Prod.{u_2, u_2} A A),
                                                    Membership.mem.{u_2, u_2}
                                                        (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2}
                                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                              u_2}
                                                            D)
                                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1,
                                                              u_2}
                                                            D)
                                                          rows)
                                                        pair →
                                                      HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.{u_1,
                                                          u_2}
                                                        D (⇑normI) (family pair)) →
                                                  LE.le.{0} (HPow.hPow.{0, 0, 0} Z (HAdd.hAdd.{0, 0, 0} S B))
                                                      (normI
                                                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.{u_1,
                                                            u_2}
                                                          D)) →
                                                    LE.le.{0}
                                                      (HMul.hMul.{0, 0, 0}
                                                        (∑
                                                          pair ∈
                                                            HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2}
                                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                                  u_2}
                                                                D)
                                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1,
                                                                  u_2}
                                                                D)
                                                              rows,
                                                          HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.energy.{u_1,
                                                              u_2}
                                                            (family pair) D ⇑normI)
                                                        (HPow.hPow.{0, 0, 0} Z
                                                          (HeckeSkeleton.LowFrozenCube.squaredKernelExponent T v ell)))
                                                      (HMul.hMul.{0, 0, 0} C
                                                        (HPow.hPow.{0, 0, 0} Z
                                                          (HAdd.hAdd.{0, 0, 0}
                                                            (HAdd.hAdd.{0, 0, 0}
                                                              (HeckeSkeleton.LowFrozenCube.reflectedExponent O H v ell S
                                                                B z T)
                                                              (HMul.hMul.{0, 0, 0} eps
                                                                (HAdd.hAdd.{0, 0, 0}
                                                                  (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} H v) ell)
                                                                  z)))
                                                            (HMul.hMul.{0, 0, 0} eta (HAdd.hAdd.{0, 0, 0} O Rrad)))))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.avoids_ordinary_of_avoids_support

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (a : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) a →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) a
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.beta_bound_of_lower_annulus

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (lam : A → ℂ) (Ω : A → A → A → ℂ) (B C : ℝ),
      LT.lt.{0} 0 B →
        LE.le.{0} 0 C →
          ∀ (columns : Finset.{u_2} A) (pairs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
            (∀ (c : A),
                Membership.mem.{u_2, u_2} columns c →
                  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c) →
              (∀ (q : Prod.{u_2, u_2} A A),
                  Membership.mem.{u_2, u_2} pairs q →
                    HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D q.1 ∧
                      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.2) →
                (∀ (c : A), Membership.mem.{u_2, u_2} columns c → LE.le.{0} (Norm.norm.{0} (lam c)) 1) →
                  (∀ (c : A),
                      Membership.mem.{u_2, u_2} columns c →
                        ∀ (q : Prod.{u_2, u_2} A A),
                          Membership.mem.{u_2, u_2} pairs q →
                            LE.le.{0} (Norm.norm.{0} (Ω c q.1 q.2)) (HDiv.hDiv.{0, 0, 0} C (normI q.1))) →
                    (∀ (q : Prod.{u_2, u_2} A A),
                        Membership.mem.{u_2, u_2} pairs q →
                          LE.le.{0} B (normI (HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2} q))) →
                      ∀ (c : A),
                        Membership.mem.{u_2, u_2} columns c →
                          ∀ (b : A),
                            Membership.mem.{u_2, u_2}
                                (Finset.image.{u_2, u_2} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2} pairs) b →
                              LE.le.{0}
                                (Norm.norm.{0}
                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.beta.{u_1, u_2} D (⇑normI) lam Ω c
                                    b))
                                (HDiv.hDiv.{0, 0, 0} C B)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.beta_eq_scalar_unitBeta

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (lam : A → ℂ)
  (Ω : A → A → A → ℂ) (B C : ℝ),
  LT.lt.{0} 0 B →
    LE.le.{0} 0 C →
      ∀ (c b : A),
        LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.beta.{u_1, u_2} D normI lam Ω c b))
            (HDiv.hDiv.{0, 0, 0} C B) →
          Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.beta.{u_1, u_2} D normI lam Ω c b)
            (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} ↑C ↑B)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.{u_1, u_2} D normI lam Ω B C c b))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.beta_norm_le

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (lam : A → ℂ) (Ω : A → A → A → ℂ) (C : ℝ),
      LE.le.{0} 0 C →
        ∀ (columns : Finset.{u_2} A) (pairs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
          (∀ (c : A),
              Membership.mem.{u_2, u_2} columns c →
                HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c) →
            (∀ (q : Prod.{u_2, u_2} A A),
                Membership.mem.{u_2, u_2} pairs q →
                  HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D q.1 ∧
                    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.2) →
              (∀ (c : A), Membership.mem.{u_2, u_2} columns c → LE.le.{0} (Norm.norm.{0} (lam c)) 1) →
                (∀ (c : A),
                    Membership.mem.{u_2, u_2} columns c →
                      ∀ (q : Prod.{u_2, u_2} A A),
                        Membership.mem.{u_2, u_2} pairs q →
                          LE.le.{0} (Norm.norm.{0} (Ω c q.1 q.2)) (HDiv.hDiv.{0, 0, 0} C (normI q.1))) →
                  ∀ (c : A),
                    Membership.mem.{u_2, u_2} columns c →
                      ∀ (b : A),
                        Membership.mem.{u_2, u_2}
                            (Finset.image.{u_2, u_2} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2} pairs) b →
                          LE.le.{0}
                            (Norm.norm.{0}
                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.beta.{u_1, u_2} D (⇑normI) lam Ω c b))
                            (HDiv.hDiv.{0, 0, 0} C (normI b))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.blockSourceEnergy_reindex

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
  (Ω : A → A → A → ℂ) (pow sup : A) (rows marks columns : Finset.{u_2} A) (pairs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  Eq.{1}
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.blockSourceEnergy.{u_1, u_2} D normI a₀ ρ₀ lam Ω pow sup rows
      marks columns pairs)
    (∑
      d ∈
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) pow sup rows,
      HPow.hPow.{0, 0, 0}
        (Norm.norm.{0}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceRow.{u_1, u_2} D normI a₀ ρ₀ lam Ω marks columns pairs
            d))
        2)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.canonical_admissible

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (x : A),
  HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
    ∀ (p : ι),
      HeckeSkeleton.LowFrozenCube.AdmissibleExponent
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.exponents.{u_1, u_2} D x p)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.canonical_coprime

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (P x : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P →
    HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P x
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.canonical_coprime_ordinary

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (a x : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) a →
    HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) a x
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.canonical_minimum

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (x : A),
  HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
    Eq.{u_1 + 1}
      (HeckeSkeleton.LowFrozenCube.frozenBase.{u_1}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.exponents.{u_1, u_2} D x))
      fun p =>
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
        p
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.canonical_of_minimumFactor_eq

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (a : A),
  Eq.{u_2 + 1}
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.minimumFactor.{u_1, u_2}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) a)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D) →
    HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) a)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.canonical_residual

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (x : A),
  HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
    Eq.{u_1 + 1}
      (HeckeSkeleton.LowFrozenCube.frozenCube.{u_1}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.exponents.{u_1, u_2} D x))
      fun p =>
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) x)
        p
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.canonical_split

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (x n : A),
  HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) n →
      Eq.{u_2 + 1}
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.cubeSplit.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) (HMul.hMul.{u_2, u_2, u_2} x n))
        (Prod.mk.{u_2, u_2} x n)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.canonical_supported

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (x : A),
  HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) x
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.canonical_supported_on

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (s : Finset.{u_1} ι),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) s
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D) →
    ∀ (x : A),
      HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) s x
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.canonical_supported_ordinary

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (x : A),
  HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) x
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.column_frozen

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (lam : A → ℂ) (c x : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c →
    HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
      Eq.{1}
        (HeckeSkeleton.LowFrozenCube.columnCoefficient.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinarySymbol.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.exponents.{u_1, u_2} D x) lam
          (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D)
            (HPow.hPow.{u_2, 0, u_2} x 3))
          c)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.column.{u_1, u_2} D lam c)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.column_norm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (lam : A → ℂ) (c : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c →
    Eq.{1} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.column.{u_1, u_2} D lam c))
      (Norm.norm.{0} (lam c))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.familySourceEnergy_eq_blocks

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ)
  (family : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A)
  (rows : Finset.{u_2} A),
  (∀ (pair : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2}
          (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) rows)
          pair →
        Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1, u_2} (family pair)) rows ∧
          Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.pow.{u_1, u_2} (family pair)) pair.1 ∧
            Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.sup.{u_1, u_2} (family pair))
              pair.2) →
    Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.familySourceEnergy.{u_1, u_2} D normI family rows)
      (∑
        pair ∈
          HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) rows,
        HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.energy.{u_1, u_2} (family pair) D normI)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.family_source_energy_ledger

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    (∀ (a : A), LE.le.{0} 1 (q a)) →
      ∀ (Ccount : ℝ),
        LT.lt.{0} 0 Ccount →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
            (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b) →
              (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                  (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                  fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b) →
                ∀ (eps eta : ℝ),
                  LT.lt.{0} 0 eps →
                    LT.lt.{0} 0 eta →
                      ∃ C,
                        LT.lt.{0} 0 C ∧
                          ∀ (Z O H v ell S B z T Rrad : ℝ),
                            LE.le.{0} 1 Z →
                              LE.le.{0} 0 O →
                                LE.le.{0} 0 H →
                                  LE.le.{0} 0 v →
                                    LE.le.{0} 0 ell →
                                      LE.le.{0} 0 z →
                                        ∀ (rows : Finset.{u_2} A),
                                          (∀ (k : A),
                                              Membership.mem.{u_2, u_2} rows k →
                                                LE.le.{0}
                                                  (normI
                                                    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1,
                                                        u_2}
                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                          u_2}
                                                        D)
                                                      k))
                                                  (HPow.hPow.{0, 0, 0} Z O)) →
                                            LE.le.{0}
                                                (normI
                                                  (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2}
                                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2}
                                                      D)
                                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2}
                                                      D)))
                                                (HPow.hPow.{0, 0, 0} Z Rrad) →
                                              ∀
                                                (family :
                                                  Prod.{u_2, u_2} A A →
                                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι
                                                      A),
                                                (∀ (pair : Prod.{u_2, u_2} A A),
                                                    Membership.mem.{u_2, u_2}
                                                        (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2}
                                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                              u_2}
                                                            D)
                                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1,
                                                              u_2}
                                                            D)
                                                          rows)
                                                        pair →
                                                      Eq.{u_2 + 1}
                                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1,
                                                              u_2}
                                                            (family pair))
                                                          rows ∧
                                                        Eq.{u_2 + 1}
                                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.pow.{u_1,
                                                                u_2}
                                                              (family pair))
                                                            pair.1 ∧
                                                          Eq.{u_2 + 1}
                                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.sup.{u_1,
                                                                u_2}
                                                              (family pair))
                                                            pair.2) →
                                                  ∀
                                                    (a :
                                                      (pair : Prod.{u_2, u_2} A A) →
                                                        Membership.mem.{u_2, u_2}
                                                            (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2}
                                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                                  u_2}
                                                                D)
                                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1,
                                                                  u_2}
                                                                D)
                                                              rows)
                                                            pair →
                                                          HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1,
                                                              u_2}
                                                            D (⇑normI) Z H v ell z (family pair)),
                                                    (∀ (pair : Prod.{u_2, u_2} A A),
                                                        Membership.mem.{u_2, u_2}
                                                            (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2}
                                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                                  u_2}
                                                                D)
                                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1,
                                                                  u_2}
                                                                D)
                                                              rows)
                                                            pair →
                                                          HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.{u_1,
                                                              u_2}
                                                            D (⇑normI) (family pair)) →
                                                      LE.le.{0} (HPow.hPow.{0, 0, 0} Z (HAdd.hAdd.{0, 0, 0} S B))
                                                          (normI
                                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.{u_1,
                                                                u_2}
                                                              D)) →
                                                        LE.le.{0}
                                                          (HMul.hMul.{0, 0, 0}
                                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.familySourceEnergy.{u_1,
                                                                u_2}
                                                              D (⇑normI) family rows)
                                                            (HPow.hPow.{0, 0, 0} Z
                                                              (HeckeSkeleton.LowFrozenCube.squaredKernelExponent T v
                                                                ell)))
                                                          (HMul.hMul.{0, 0, 0} C
                                                            (HPow.hPow.{0, 0, 0} Z
                                                              (HAdd.hAdd.{0, 0, 0}
                                                                (HAdd.hAdd.{0, 0, 0}
                                                                  (HeckeSkeleton.LowFrozenCube.reflectedExponent O H v
                                                                    ell S B z T)
                                                                  (HMul.hMul.{0, 0, 0} eps
                                                                    (HAdd.hAdd.{0, 0, 0}
                                                                      (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} H v)
                                                                        ell)
                                                                      z)))
                                                                (HMul.hMul.{0, 0, 0} eta
                                                                  (HAdd.hAdd.{0, 0, 0} O Rrad)))))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.freezePair_injOn

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  (∀ (q : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} inputs q →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.1) →
    Set.InjOn.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.freezePair.{u_1, u_2} D)
      ↑(HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.activeInputBlock.{u_1, u_2} D normI first prefactor atZero
          inputs)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenInputPairs_canonical

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  (∀ (q : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} inputs q →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.2) →
    ∀ (q : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenInputPairs.{u_1, u_2} D normI first prefactor atZero
            inputs)
          q →
        HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D q.1 ∧
          HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.2
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenInputPairs_norm_lower

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)) (B : ℝ),
  (∀ (q : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} inputs q →
        LE.le.{0} B
          (normI
            (HMul.hMul.{u_2, u_2, u_2}
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) q.1)
              q.2))) →
    ∀ (q : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenInputPairs.{u_1, u_2} D normI first prefactor atZero
            inputs)
          q →
        LE.le.{0} B (normI (HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2} q))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenPhase_norm_le

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ) (columns : Finset.{u_2} A) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  (∀ (q : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} inputs q →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.1) →
    (∀ (c : A),
        Membership.mem.{u_2, u_2} columns c →
          ∀ (q : Prod.{u_2, u_2} A A),
            Membership.mem.{u_2, u_2} inputs q → LE.le.{0} (Norm.norm.{0} (phase c q.1 q.2)) 1) →
      ∀ (c : A),
        Membership.mem.{u_2, u_2} columns c →
          ∀ (q : Prod.{u_2, u_2} A A),
            Membership.mem.{u_2, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenInputPairs.{u_1, u_2} D normI first prefactor
                  atZero inputs)
                q →
              LE.le.{0}
                (Norm.norm.{0}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenPhase.{u_1, u_2} D phase c q.1 q.2))
                1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.hybridRow_scale_beta

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (β γ : A → A → ℂ) (aP : A → ℂ)
  (marks columns cubes : Finset.{u_2} A) (scalar : ℂ),
  (∀ (c : A),
      Membership.mem.{u_2, u_2} columns c →
        ∀ (b : A), Membership.mem.{u_2, u_2} cubes b → Eq.{1} (β c b) (HMul.hMul.{0, 0, 0} scalar (γ c b))) →
    ∀ (d : A),
      Eq.{1}
        (HeckeSkeleton.LowHybrid.hybridRow.{u_2}
          (fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b)
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
          normI aP β marks columns cubes d)
        (HMul.hMul.{0, 0, 0} scalar
          (HeckeSkeleton.LowHybrid.hybridRow.{u_2}
            (fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
            normI aP γ marks columns cubes d))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.kernel_numerator_frozen

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ) (X : ℝ)
  (c x n : A),
  Eq.{1}
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0}
        (HMul.hMul.{0, 0, 0} X
          (normI
            (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D)
              (HPow.hPow.{u_2, 0, u_2} x 3))))
        (normI c))
      (HPow.hPow.{0, 0, 0} (normI n) 3))
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0}
        (HMul.hMul.{0, 0, 0} X (normI (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D)))
        (normI c))
      (HPow.hPow.{0, 0, 0} (normI (HMul.hMul.{u_2, u_2, u_2} x n)) 3))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.local_table_frozen_exit

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ),
      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D) →
        ∀ (a₀ ρ₀ lam : A → ℂ) (B : ℝ),
          LT.lt.{0} 0 B →
            ∀ (rows marks columns : Finset.{u_2} A) (pairs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
              (∀ (d : A),
                  Membership.mem.{u_2, u_2} rows d →
                    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d) →
                (∀ (d : A), Membership.mem.{u_2, u_2} rows d → Eq.{1} (Norm.norm.{0} (ρ₀ d)) 1) →
                  (∀ (P : A),
                      Membership.mem.{u_2, u_2} marks P →
                        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P) →
                    (∀ (P : A), Membership.mem.{u_2, u_2} marks P → LE.le.{0} (Norm.norm.{0} (a₀ P)) 1) →
                      (∀ (c : A),
                          Membership.mem.{u_2, u_2} columns c →
                            HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c) →
                        (∀ (c : A), Membership.mem.{u_2, u_2} columns c → LE.le.{0} (Norm.norm.{0} (lam c)) 1) →
                          (∀ (q : Prod.{u_2, u_2} A A),
                              Membership.mem.{u_2, u_2} pairs q →
                                HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D q.1 ∧
                                  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.2) →
                            (∀ (c : A),
                                Membership.mem.{u_2, u_2} columns c →
                                  ∀ (q : Prod.{u_2, u_2} A A),
                                    Membership.mem.{u_2, u_2} pairs q → LE.le.{0} (Norm.norm.{0} (phase c q.1 q.2)) 1) →
                              (∀ (q : Prod.{u_2, u_2} A A),
                                  Membership.mem.{u_2, u_2} pairs q →
                                    LE.le.{0} B (normI (HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2} q))) →
                                have Ω :=
                                  HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableOmega.{u_1, u_2} D (⇑normI)
                                    first prefactor atZero phase;
                                have C :=
                                  HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableMajorant.{u_1, u_2} D (⇑normI)
                                    first prefactor atZero;
                                (∀ (P : A),
                                    Membership.mem.{u_2, u_2} marks P →
                                      LE.le.{0}
                                        (Norm.norm.{0}
                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀ P))
                                        1) ∧
                                  (∀ (c : A),
                                      Membership.mem.{u_2, u_2} columns c →
                                        ∀ (b : A),
                                          Membership.mem.{u_2, u_2}
                                              (Finset.image.{u_2, u_2} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2}
                                                pairs)
                                              b →
                                            LE.le.{0}
                                              (Norm.norm.{0}
                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.{u_1, u_2} D
                                                  (⇑normI) lam Ω B C c b))
                                              1) ∧
                                    Eq.{1}
                                      (∑ d ∈ rows,
                                        HPow.hPow.{0, 0, 0}
                                          (Norm.norm.{0}
                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceRow.{u_1, u_2} D
                                              (⇑normI) a₀ ρ₀ lam Ω marks columns pairs d))
                                          2)
                                      (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} C B) 2)
                                        (HeckeSkeleton.LowHybrid.hybridEnergy.{u_2}
                                          (fun a b =>
                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b)
                                          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                                          (⇑normI)
                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀)
                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.{u_1, u_2} D
                                            (⇑normI) lam Ω B C)
                                          rows marks columns
                                          (Finset.image.{u_2, u_2} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2}
                                            pairs)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.local_table_row_block_exit

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ),
      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D) →
        ∀ (a₀ ρ₀ lam : A → ℂ) (K B : ℝ),
          LT.lt.{0} 0 B →
            ∀ (pow sup : A) (rows marks columns : Finset.{u_2} A) (pairs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
              (∀ (k : A), Membership.mem.{u_2, u_2} rows k → LE.le.{0} (normI k) K) →
                (∀ (d : A),
                    (∀ (p : ι),
                        LE.le.{0}
                          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) d)
                            p)
                          1) →
                      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d →
                        Eq.{1} (Norm.norm.{0} (ρ₀ d)) 1) →
                  (∀ (P : A),
                      Membership.mem.{u_2, u_2} marks P →
                        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P) →
                    (∀ (P : A), Membership.mem.{u_2, u_2} marks P → LE.le.{0} (Norm.norm.{0} (a₀ P)) 1) →
                      (∀ (c : A),
                          Membership.mem.{u_2, u_2} columns c →
                            HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c) →
                        (∀ (c : A), Membership.mem.{u_2, u_2} columns c → LE.le.{0} (Norm.norm.{0} (lam c)) 1) →
                          (∀ (q : Prod.{u_2, u_2} A A),
                              Membership.mem.{u_2, u_2} pairs q →
                                HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D q.1 ∧
                                  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.2) →
                            (∀ (c : A),
                                Membership.mem.{u_2, u_2} columns c →
                                  ∀ (q : Prod.{u_2, u_2} A A),
                                    Membership.mem.{u_2, u_2} pairs q → LE.le.{0} (Norm.norm.{0} (phase c q.1 q.2)) 1) →
                              (∀ (q : Prod.{u_2, u_2} A A),
                                  Membership.mem.{u_2, u_2} pairs q →
                                    LE.le.{0} B (normI (HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2} q))) →
                                have residual :=
                                  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2}
                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) pow sup
                                    rows;
                                have Ω :=
                                  HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableOmega.{u_1, u_2} D (⇑normI)
                                    first prefactor atZero phase;
                                have C :=
                                  HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableMajorant.{u_1, u_2} D (⇑normI)
                                    first prefactor atZero;
                                LE.le.{0} 1
                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualParameter.{u_1, u_2} D
                                      (⇑normI) K pow sup) ∧
                                  (∀ (d : A),
                                      Membership.mem.{u_2, u_2} residual d →
                                        (∀ (p : ι),
                                            LE.le.{0}
                                              ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                                  d)
                                                p)
                                              1) ∧
                                          HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D)
                                              d ∧
                                            LE.le.{0} (normI d)
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualParameter.{u_1,
                                                  u_2}
                                                D (⇑normI) K pow sup)) ∧
                                    (∀ (P : A),
                                        Membership.mem.{u_2, u_2} marks P →
                                          LE.le.{0}
                                            (Norm.norm.{0}
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀ P))
                                            1) ∧
                                      (∀ (c : A),
                                          Membership.mem.{u_2, u_2} columns c →
                                            ∀ (b : A),
                                              Membership.mem.{u_2, u_2}
                                                  (Finset.image.{u_2, u_2} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2}
                                                    pairs)
                                                  b →
                                                LE.le.{0}
                                                  (Norm.norm.{0}
                                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.{u_1,
                                                        u_2}
                                                      D (⇑normI) lam Ω B C c b))
                                                  1) ∧
                                        Eq.{1}
                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.blockSourceEnergy.{u_1, u_2}
                                            D (⇑normI) a₀ ρ₀ lam Ω pow sup rows marks columns pairs)
                                          (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} C B) 2)
                                            (HeckeSkeleton.LowHybrid.hybridEnergy.{u_2}
                                              (fun a b =>
                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a)
                                                  b)
                                              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                                              (⇑normI)
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀)
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.{u_1, u_2} D
                                                (⇑normI) lam Ω B C)
                                              residual marks columns
                                              (Finset.image.{u_2, u_2} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2}
                                                pairs)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark_frozen

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (a₀ : A → ℂ) (P x : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P →
    HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
      Eq.{1}
        (HeckeSkeleton.LowFrozenCube.markCoefficient.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinarySymbol.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.exponents.{u_1, u_2} D x) a₀
          (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D)
            (HPow.hPow.{u_2, 0, u_2} x 3))
          P)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀ P)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark_norm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (a₀ : A → ℂ) (P : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P →
    Eq.{1} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀ P))
      (Norm.norm.{0} (a₀ P))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mem_activeInputBlock

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)) (q : Prod.{u_2, u_2} A A),
  Membership.mem.{u_2, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.activeInputBlock.{u_1, u_2} D normI first prefactor atZero
        inputs)
      q ↔
    Membership.mem.{u_2, u_2} inputs q ∧
      Eq.{u_2 + 1}
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.minimumFactor.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) q.1)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D) ∧
        Ne.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawTable.{u_1, u_2} D normI first prefactor atZero q.1)
          0
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum_cases_of_activeInput

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)) (q : Prod.{u_2, u_2} A A),
  Membership.mem.{u_2, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.activeInputBlock.{u_1, u_2} D normI first prefactor atZero
        inputs)
      q →
    ∀ (p : ι),
      Eq.{1}
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
            p)
          0 ∨
        Eq.{1}
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
              p)
            1 ∨
          Eq.{1}
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
              p)
            3
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum_ordinary

```lean
∀ {ι : Type u_3} {A : Type u_4} [inst : CommMonoid.{u_4} A]
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_3, u_4} ι A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_3, u_4}
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_3, u_4} self)
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_3, u_4} self)
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_3, u_4} self)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum_supported

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D)
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum_supported_of_activeInput

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  (∀ (q : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} inputs q →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.1) →
    ∀ (q : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.activeInputBlock.{u_1, u_2} D normI first prefactor atZero
            inputs)
          q →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mixedPhase_column_overlap_zero

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (d P c n : A) (p : ι),
  Ne.{1}
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P)
        p)
      0 →
    Ne.{1}
        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) c)
          p)
        0 →
      Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mixedPhase.{u_1, u_2} D d P c n) 0
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mixedPhase_cube_overlap_zero

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (d P c n : A),
  ¬HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P n →
    Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mixedPhase.{u_1, u_2} D d P c n) 0
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mixedPhase_eq

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (d P c n : A),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mixedPhase.{u_1, u_2} D d P c n)
    (HMul.hMul.{0, 0, 0}
      (ite.{1}
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P d)
        1 0)
      (HMul.hMul.{0, 0, 0}
        (HMul.hMul.{0, 0, 0}
          (HPow.hPow.{0, 0, 0}
            ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D d) (HMul.hMul.{u_2, u_2, u_2} c n))
            3)
          (HPow.hPow.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D P) c) 4))
        (ite.{1}
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P n)
          1 0)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mixedPhase_row_overlap_zero

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (d P c n : A) (p : ι),
  Ne.{1}
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P)
        p)
      0 →
    Ne.{1}
        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) d)
          p)
        0 →
      Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mixedPhase.{u_1, u_2} D d P c n) 0
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.negativeInteraction_norm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (v : ι → ℕ) (a : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) a →
    Eq.{1}
      (Norm.norm.{0}
        (HeckeSkeleton.LowFrozenCube.negativeOrdinaryInteraction.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinarySymbol.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D) v a))
      1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.norm_chargeIdeal

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ),
  Eq.{1} (normI (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.{u_1, u_2} D))
    (∏ p ∈ HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D,
      HPow.hPow.{0, 0, 0} (normI (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.prime.{u_1, u_2} D p))
        (HeckeSkeleton.LowFrozenCube.LocalTable.minimumCharge
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D p)
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
            p)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.normalized_frozen_exit

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (a₀ ρ₀ lam : A → ℂ) (Ω : A → A → A → ℂ) (B C : ℝ),
      LT.lt.{0} 0 B →
        LE.le.{0} 0 C →
          ∀ (rows marks columns : Finset.{u_2} A) (pairs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
            (∀ (d : A),
                Membership.mem.{u_2, u_2} rows d →
                  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d) →
              (∀ (d : A), Membership.mem.{u_2, u_2} rows d → Eq.{1} (Norm.norm.{0} (ρ₀ d)) 1) →
                (∀ (P : A),
                    Membership.mem.{u_2, u_2} marks P →
                      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P) →
                  (∀ (P : A), Membership.mem.{u_2, u_2} marks P → LE.le.{0} (Norm.norm.{0} (a₀ P)) 1) →
                    (∀ (c : A),
                        Membership.mem.{u_2, u_2} columns c →
                          HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c) →
                      (∀ (c : A), Membership.mem.{u_2, u_2} columns c → LE.le.{0} (Norm.norm.{0} (lam c)) 1) →
                        (∀ (q : Prod.{u_2, u_2} A A),
                            Membership.mem.{u_2, u_2} pairs q →
                              HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D q.1 ∧
                                HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.2) →
                          (∀ (c : A),
                              Membership.mem.{u_2, u_2} columns c →
                                ∀ (q : Prod.{u_2, u_2} A A),
                                  Membership.mem.{u_2, u_2} pairs q →
                                    LE.le.{0} (Norm.norm.{0} (Ω c q.1 q.2)) (HDiv.hDiv.{0, 0, 0} C (normI q.1))) →
                            (∀ (q : Prod.{u_2, u_2} A A),
                                Membership.mem.{u_2, u_2} pairs q →
                                  LE.le.{0} B (normI (HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2} q))) →
                              (∀ (P : A),
                                  Membership.mem.{u_2, u_2} marks P →
                                    LE.le.{0}
                                      (Norm.norm.{0}
                                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀ P))
                                      1) ∧
                                (∀ (c : A),
                                    Membership.mem.{u_2, u_2} columns c →
                                      ∀ (b : A),
                                        Membership.mem.{u_2, u_2}
                                            (Finset.image.{u_2, u_2} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2}
                                              pairs)
                                            b →
                                          LE.le.{0}
                                            (Norm.norm.{0}
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.{u_1, u_2} D
                                                (⇑normI) lam Ω B C c b))
                                            1) ∧
                                  Eq.{1}
                                    (∑ d ∈ rows,
                                      HPow.hPow.{0, 0, 0}
                                        (Norm.norm.{0}
                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceRow.{u_1, u_2} D
                                            (⇑normI) a₀ ρ₀ lam Ω marks columns pairs d))
                                        2)
                                    (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} C B) 2)
                                      (HeckeSkeleton.LowHybrid.hybridEnergy.{u_2}
                                        (fun a b =>
                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b)
                                        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                                        (⇑normI) (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀)
                                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.{u_1, u_2} D (⇑normI)
                                          lam Ω B C)
                                        rows marks columns
                                        (Finset.image.{u_2, u_2} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2} pairs)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinarySymbol_norm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (a : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) a →
    ∀ (p : ι),
      Membership.mem.{u_1, u_1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) p →
        Eq.{1} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinarySymbol.{u_1, u_2} D p a)) 1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary_subset

```lean
∀ {ι : Type u_3} {A : Type u_4} [inst : CommMonoid.{u_4} A]
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_3, u_4} ι A),
  HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_3, u_4} self ⊆
    HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_3, u_4} self
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.positiveInteraction_norm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (v : ι → ℕ) (a : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) a →
    Eq.{1}
      (Norm.norm.{0}
        (HeckeSkeleton.LowFrozenCube.positiveOrdinaryInteraction.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinarySymbol.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D) v a))
      1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.prime_eq_primeElement

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (p : ι),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.prime.{u_1, u_2} D p)
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.primeElement.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) p)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawBlockSourceEnergy_reindex

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ) (pow sup : A) (rows marks columns : Finset.{u_2} A)
  (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  Eq.{1}
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawBlockSourceEnergy.{u_1, u_2} D normI first prefactor atZero
      phase a₀ ρ₀ lam pow sup rows marks columns inputs)
    (∑
      d ∈
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) pow sup rows,
      HPow.hPow.{0, 0, 0}
        (Norm.norm.{0}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceRow.{u_1, u_2} D normI first prefactor atZero phase
            a₀ ρ₀ lam marks columns inputs d))
        2)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawBlockSourceEnergy_scale_column

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ) (a₀ ρ₀ lam gamma : A → ℂ) (scalar : ℂ) (pow sup : A)
  (rows marks columns : Finset.{u_2} A) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  (∀ (c : A), Membership.mem.{u_2, u_2} columns c → Eq.{1} (lam c) (HMul.hMul.{0, 0, 0} scalar (gamma c))) →
    Eq.{1}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawBlockSourceEnergy.{u_1, u_2} D normI first prefactor atZero
        phase a₀ ρ₀ lam pow sup rows marks columns inputs)
      (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} scalar) 2)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawBlockSourceEnergy.{u_1, u_2} D normI first prefactor atZero
          phase a₀ ρ₀ gamma pow sup rows marks columns inputs))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceRow_eq_sourceRow

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ) (marks columns : Finset.{u_2} A)
  (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  (∀ (q : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} inputs q →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.1) →
    ∀ (d : A),
      Eq.{1}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceRow.{u_1, u_2} D normI first prefactor atZero phase
          a₀ ρ₀ lam marks columns inputs d)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceRow.{u_1, u_2} D normI a₀ ρ₀ lam
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableOmega.{u_1, u_2} D normI first prefactor atZero
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenPhase.{u_1, u_2} D phase))
          marks columns
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenInputPairs.{u_1, u_2} D normI first prefactor atZero
            inputs)
          d)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceRow_scale_column

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ) (a₀ ρ₀ lam gamma : A → ℂ) (scalar : ℂ) (marks columns : Finset.{u_2} A)
  (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  (∀ (c : A), Membership.mem.{u_2, u_2} columns c → Eq.{1} (lam c) (HMul.hMul.{0, 0, 0} scalar (gamma c))) →
    ∀ (d : A),
      Eq.{1}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceRow.{u_1, u_2} D normI first prefactor atZero phase
          a₀ ρ₀ lam marks columns inputs d)
        (HMul.hMul.{0, 0, 0} scalar
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceRow.{u_1, u_2} D normI first prefactor atZero phase
            a₀ ρ₀ gamma marks columns inputs d))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceTerm_eq_sourceTerm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ) (d P c a x n : A),
  Eq.{u_2 + 1} a
      (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D)
        (HPow.hPow.{u_2, 0, u_2} x 3)) →
    Eq.{1}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceTerm.{u_1, u_2} D normI first prefactor atZero phase a₀
        ρ₀ lam d P c a n)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceTerm.{u_1, u_2} D normI a₀ ρ₀ lam
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableOmega.{u_1, u_2} D normI first prefactor atZero
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenPhase.{u_1, u_2} D phase))
        d P c x n)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceTerm_zero

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ) (d P c a n : A),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawTable.{u_1, u_2} D normI first prefactor atZero a) 0 →
    Eq.{1}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceTerm.{u_1, u_2} D normI first prefactor atZero phase a₀
        ρ₀ lam d P c a n)
      0
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawTable_nonzero_admissible

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (a : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) a →
    Ne.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawTable.{u_1, u_2} D normI first prefactor atZero a) 0 →
      ∀ (p : ι),
        HeckeSkeleton.LowFrozenCube.AdmissibleExponent
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) a)
            p)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.raw_frozen_hybrid_bound

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    (∀ (a : A), LE.le.{0} 1 (q a)) →
      ∀ (Ccount : ℝ),
        LT.lt.{0} 0 Ccount →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
            (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b) →
              (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                  (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                  fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b) →
                ∀ (eps : ℝ),
                  LT.lt.{0} 0 eps →
                    ∃ C0,
                      LT.lt.{0} 0 C0 ∧
                        ∀ (K N B L Bmin : ℝ),
                          LE.le.{0} 1 N →
                            LE.le.{0} 1 B →
                              LE.le.{0} 1 L →
                                LT.lt.{0} 0 Bmin →
                                  ∀ (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
                                    (a₀ ρ₀ lam : A → ℂ) (pow sup : A) (rows marks columns : Finset.{u_2} A)
                                    (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
                                    (∀ (k : A), Membership.mem.{u_2, u_2} rows k → LE.le.{0} (normI k) K) →
                                      (∀ (d : A),
                                          (∀ (p : ι),
                                              LE.le.{0}
                                                ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2}
                                                      D)
                                                    d)
                                                  p)
                                                1) →
                                            HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D)
                                                d →
                                              Eq.{1} (Norm.norm.{0} (ρ₀ d)) 1) →
                                        (∀ (P : A),
                                            Membership.mem.{u_2, u_2} marks P →
                                              HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D)
                                                P) →
                                          (∀ (P : A),
                                              Membership.mem.{u_2, u_2} marks P →
                                                HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2}
                                                      D)
                                                    P ∧
                                                  LE.le.{0} (normI P) L) →
                                            (∀ (P : A),
                                                Membership.mem.{u_2, u_2} marks P →
                                                  LE.le.{0} (Norm.norm.{0} (a₀ P)) 1) →
                                              (∀ (c : A),
                                                  Membership.mem.{u_2, u_2} columns c →
                                                    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                          u_2}
                                                        D)
                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1,
                                                          u_2}
                                                        D)
                                                      c) →
                                                (∀ (c : A),
                                                    Membership.mem.{u_2, u_2} columns c →
                                                      HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                              u_2}
                                                            D)
                                                          c ∧
                                                        LE.le.{0} (normI c) N) →
                                                  (∀ (c : A),
                                                      Membership.mem.{u_2, u_2} columns c →
                                                        LE.le.{0} (Norm.norm.{0} (lam c)) 1) →
                                                    (∀ (u : Prod.{u_2, u_2} A A),
                                                        Membership.mem.{u_2, u_2} inputs u →
                                                          HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1,
                                                              u_2}
                                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                                u_2}
                                                              D)
                                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1,
                                                                u_2}
                                                              D)
                                                            u.1) →
                                                      (∀ (u : Prod.{u_2, u_2} A A),
                                                          Membership.mem.{u_2, u_2} inputs u →
                                                            HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1,
                                                                u_2}
                                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                                  u_2}
                                                                D)
                                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1,
                                                                  u_2}
                                                                D)
                                                              u.2) →
                                                        (∀ (c : A),
                                                            Membership.mem.{u_2, u_2} columns c →
                                                              ∀ (u : Prod.{u_2, u_2} A A),
                                                                Membership.mem.{u_2, u_2} inputs u →
                                                                  LE.le.{0} (Norm.norm.{0} (phase c u.1 u.2)) 1) →
                                                          (∀ (u : Prod.{u_2, u_2} A A),
                                                              Membership.mem.{u_2, u_2} inputs u →
                                                                LE.le.{0} Bmin
                                                                  (normI
                                                                    (HMul.hMul.{u_2, u_2, u_2}
                                                                      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1,
                                                                          u_2}
                                                                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                                            u_2}
                                                                          D)
                                                                        u.1)
                                                                      u.2))) →
                                                            (∀ (u : Prod.{u_2, u_2} A A),
                                                                Membership.mem.{u_2, u_2} inputs u →
                                                                  LE.le.{0}
                                                                    (normI
                                                                      (HMul.hMul.{u_2, u_2, u_2}
                                                                        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1,
                                                                            u_2}
                                                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                                              u_2}
                                                                            D)
                                                                          u.1)
                                                                        u.2))
                                                                    B) →
                                                              LE.le.{0}
                                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawBlockSourceEnergy.{u_1,
                                                                    u_2}
                                                                  D (⇑normI) first prefactor atZero phase a₀ ρ₀ lam pow
                                                                  sup rows marks columns inputs)
                                                                (HMul.hMul.{0, 0, 0}
                                                                  (HPow.hPow.{0, 0, 0}
                                                                    (HDiv.hDiv.{0, 0, 0}
                                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableMajorant.{u_1,
                                                                          u_2}
                                                                        D (⇑normI) first prefactor atZero)
                                                                      Bmin)
                                                                    2)
                                                                  (HMul.hMul.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0}
                                                                      (HMul.hMul.{0, 0, 0}
                                                                        (HMul.hMul.{0, 0, 0} C0
                                                                          (HPow.hPow.{0, 0, 0}
                                                                            (HMul.hMul.{0, 0, 0}
                                                                              (HMul.hMul.{0, 0, 0}
                                                                                (HMul.hMul.{0, 0, 0}
                                                                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualParameter.{u_1,
                                                                                      u_2}
                                                                                    D (⇑normI) K pow sup)
                                                                                  N)
                                                                                B)
                                                                              L)
                                                                            eps))
                                                                        (HAdd.hAdd.{0, 0, 0}
                                                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualParameter.{u_1,
                                                                              u_2}
                                                                            D (⇑normI) K pow sup)
                                                                          (HMul.hMul.{0, 0, 0} N B)))
                                                                      B)
                                                                    (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} N L)
                                                                      (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} N L)
                                                                        (2 / 3)))))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.raw_frozen_row_block_exit

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ) (K B : ℝ),
      LT.lt.{0} 0 B →
        ∀ (pow sup : A) (rows marks columns : Finset.{u_2} A) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
          (∀ (k : A), Membership.mem.{u_2, u_2} rows k → LE.le.{0} (normI k) K) →
            (∀ (d : A),
                (∀ (p : ι),
                    LE.le.{0}
                      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) d)
                        p)
                      1) →
                  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d →
                    Eq.{1} (Norm.norm.{0} (ρ₀ d)) 1) →
              (∀ (P : A),
                  Membership.mem.{u_2, u_2} marks P →
                    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P) →
                (∀ (P : A), Membership.mem.{u_2, u_2} marks P → LE.le.{0} (Norm.norm.{0} (a₀ P)) 1) →
                  (∀ (c : A),
                      Membership.mem.{u_2, u_2} columns c →
                        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c) →
                    (∀ (c : A), Membership.mem.{u_2, u_2} columns c → LE.le.{0} (Norm.norm.{0} (lam c)) 1) →
                      (∀ (q : Prod.{u_2, u_2} A A),
                          Membership.mem.{u_2, u_2} inputs q →
                            HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.1) →
                        (∀ (q : Prod.{u_2, u_2} A A),
                            Membership.mem.{u_2, u_2} inputs q →
                              HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.2) →
                          (∀ (c : A),
                              Membership.mem.{u_2, u_2} columns c →
                                ∀ (q : Prod.{u_2, u_2} A A),
                                  Membership.mem.{u_2, u_2} inputs q → LE.le.{0} (Norm.norm.{0} (phase c q.1 q.2)) 1) →
                            (∀ (q : Prod.{u_2, u_2} A A),
                                Membership.mem.{u_2, u_2} inputs q →
                                  LE.le.{0} B
                                    (normI
                                      (HMul.hMul.{u_2, u_2, u_2}
                                        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) q.1)
                                        q.2))) →
                              have residual :=
                                HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2}
                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) pow sup rows;
                              have pairs :=
                                HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenInputPairs.{u_1, u_2} D (⇑normI)
                                  first prefactor atZero inputs;
                              have Ω :=
                                HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableOmega.{u_1, u_2} D (⇑normI) first
                                  prefactor atZero
                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenPhase.{u_1, u_2} D phase);
                              have C :=
                                HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableMajorant.{u_1, u_2} D (⇑normI)
                                  first prefactor atZero;
                              LE.le.{0} 1
                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualParameter.{u_1, u_2} D
                                    (⇑normI) K pow sup) ∧
                                (∀ (d : A),
                                    Membership.mem.{u_2, u_2} residual d →
                                      (∀ (p : ι),
                                          LE.le.{0}
                                            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                                d)
                                              p)
                                            1) ∧
                                        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d ∧
                                          LE.le.{0} (normI d)
                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualParameter.{u_1,
                                                u_2}
                                              D (⇑normI) K pow sup)) ∧
                                  (∀ (P : A),
                                      Membership.mem.{u_2, u_2} marks P →
                                        LE.le.{0}
                                          (Norm.norm.{0}
                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀ P))
                                          1) ∧
                                    (∀ (c : A),
                                        Membership.mem.{u_2, u_2} columns c →
                                          ∀ (b : A),
                                            Membership.mem.{u_2, u_2}
                                                (Finset.image.{u_2, u_2} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2}
                                                  pairs)
                                                b →
                                              LE.le.{0}
                                                (Norm.norm.{0}
                                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.{u_1, u_2}
                                                    D (⇑normI) lam Ω B C c b))
                                                1) ∧
                                      Eq.{1}
                                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawBlockSourceEnergy.{u_1,
                                            u_2}
                                          D (⇑normI) first prefactor atZero phase a₀ ρ₀ lam pow sup rows marks columns
                                          inputs)
                                        (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} C B) 2)
                                          (HeckeSkeleton.LowHybrid.hybridEnergy.{u_2}
                                            (fun a b =>
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a)
                                                b)
                                            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                                            (⇑normI)
                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀)
                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.{u_1, u_2} D
                                              (⇑normI) lam Ω B C)
                                            residual marks columns
                                            (Finset.image.{u_2, u_2} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2}
                                              pairs)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.raw_local_table_frozen_exit

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ),
      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D) →
        ∀ (a₀ ρ₀ lam : A → ℂ) (B : ℝ),
          LT.lt.{0} 0 B →
            ∀ (rows marks columns : Finset.{u_2} A) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
              (∀ (d : A),
                  Membership.mem.{u_2, u_2} rows d →
                    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d) →
                (∀ (d : A), Membership.mem.{u_2, u_2} rows d → Eq.{1} (Norm.norm.{0} (ρ₀ d)) 1) →
                  (∀ (P : A),
                      Membership.mem.{u_2, u_2} marks P →
                        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P) →
                    (∀ (P : A), Membership.mem.{u_2, u_2} marks P → LE.le.{0} (Norm.norm.{0} (a₀ P)) 1) →
                      (∀ (c : A),
                          Membership.mem.{u_2, u_2} columns c →
                            HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c) →
                        (∀ (c : A), Membership.mem.{u_2, u_2} columns c → LE.le.{0} (Norm.norm.{0} (lam c)) 1) →
                          (∀ (q : Prod.{u_2, u_2} A A),
                              Membership.mem.{u_2, u_2} inputs q →
                                HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.1) →
                            (∀ (q : Prod.{u_2, u_2} A A),
                                Membership.mem.{u_2, u_2} inputs q →
                                  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.2) →
                              (∀ (c : A),
                                  Membership.mem.{u_2, u_2} columns c →
                                    ∀ (q : Prod.{u_2, u_2} A A),
                                      Membership.mem.{u_2, u_2} inputs q →
                                        LE.le.{0} (Norm.norm.{0} (phase c q.1 q.2)) 1) →
                                (∀ (q : Prod.{u_2, u_2} A A),
                                    Membership.mem.{u_2, u_2} inputs q →
                                      LE.le.{0} B
                                        (normI
                                          (HMul.hMul.{u_2, u_2, u_2}
                                            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                              q.1)
                                            q.2))) →
                                  have pairs :=
                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenInputPairs.{u_1, u_2} D
                                      (⇑normI) first prefactor atZero inputs;
                                  have Ω :=
                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableOmega.{u_1, u_2} D (⇑normI)
                                      first prefactor atZero
                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenPhase.{u_1, u_2} D phase);
                                  have C :=
                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableMajorant.{u_1, u_2} D (⇑normI)
                                      first prefactor atZero;
                                  (∀ (P : A),
                                      Membership.mem.{u_2, u_2} marks P →
                                        LE.le.{0}
                                          (Norm.norm.{0}
                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀ P))
                                          1) ∧
                                    (∀ (c : A),
                                        Membership.mem.{u_2, u_2} columns c →
                                          ∀ (b : A),
                                            Membership.mem.{u_2, u_2}
                                                (Finset.image.{u_2, u_2} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2}
                                                  pairs)
                                                b →
                                              LE.le.{0}
                                                (Norm.norm.{0}
                                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.{u_1, u_2}
                                                    D (⇑normI) lam Ω B C c b))
                                                1) ∧
                                      Eq.{1}
                                        (∑ d ∈ rows,
                                          HPow.hPow.{0, 0, 0}
                                            (Norm.norm.{0}
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceRow.{u_1, u_2}
                                                D (⇑normI) first prefactor atZero phase a₀ ρ₀ lam marks columns inputs
                                                d))
                                            2)
                                        (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} C B) 2)
                                          (HeckeSkeleton.LowHybrid.hybridEnergy.{u_2}
                                            (fun a b =>
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a)
                                                b)
                                            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                                            (⇑normI)
                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀)
                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.{u_1, u_2} D
                                              (⇑normI) lam Ω B C)
                                            rows marks columns
                                            (Finset.image.{u_2, u_2} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2}
                                              pairs)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.reciprocal

```lean
∀ {ι : Type u_3} {A : Type u_4} [inst : CommMonoid.{u_4} A]
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_3, u_4} ι A) (a b : A),
  Eq.{1} ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_3, u_4} self a) b)
    ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_3, u_4} self b) a)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualCoefficient_norm_le

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (lam : A → ℂ) (Ω : A → A → A → ℂ) (C : ℝ),
      LE.le.{0} 0 C →
        ∀ (c x n : A),
          HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c →
            LE.le.{0} (Norm.norm.{0} (lam c)) 1 →
              LE.le.{0} (Norm.norm.{0} (Ω c x n)) (HDiv.hDiv.{0, 0, 0} C (normI x)) →
                LE.le.{0}
                  (Norm.norm.{0}
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualCoefficient.{u_1, u_2} D (⇑normI) lam Ω c
                      x n))
                  (HDiv.hDiv.{0, 0, 0} C (normI (HMul.hMul.{u_2, u_2, u_2} x n)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualParameter_one_le

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (K : ℝ) (pow sup : A),
  LE.le.{0} 1 (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualParameter.{u_1, u_2} D normI K pow sup)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualRows_admissible

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (K : ℝ) (pow sup : A) (rows : Finset.{u_2} A),
      (∀ (k : A), Membership.mem.{u_2, u_2} rows k → LE.le.{0} (normI k) K) →
        ∀ (d : A),
          Membership.mem.{u_2, u_2}
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) pow sup rows)
              d →
            (∀ (p : ι),
                LE.le.{0}
                  ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) d)
                    p)
                  1) ∧
              HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d ∧
                LE.le.{0} (normI d)
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualParameter.{u_1, u_2} D (⇑normI) K pow sup)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rowFactor_frozen

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (ρ₀ : A → ℂ) (d x : A),
  HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
    Eq.{1}
      (HeckeSkeleton.LowFrozenCube.rowCoefficient.{u_1, u_2}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinarySymbol.{u_1, u_2} D)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.exponents.{u_1, u_2} D x) ρ₀
        (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D)
          (HPow.hPow.{u_2, 0, u_2} x 3))
        d)
      (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rowFactor.{u_1, u_2} D ρ₀ d)
        (HPow.hPow.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D d) x) 3))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rowFactor_norm

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (ρ₀ : A → ℂ) (d : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d →
    Eq.{1} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rowFactor.{u_1, u_2} D ρ₀ d))
      (Norm.norm.{0} (ρ₀ d))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sixth

```lean
∀ {ι : Type u_3} {A : Type u_4} [inst : CommMonoid.{u_4} A]
  (self : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_3, u_4} ι A) (a b : A),
  Eq.{1} (HPow.hPow.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_3, u_4} self a) b) 6)
    (ite.{1}
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_3, u_4}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_3, u_4} self) a b)
      1 0)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceRow_eq_frozen

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
  (Ω : A → A → A → ℂ) (marks columns : Finset.{u_2} A) (pairs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  (∀ (P : A),
      Membership.mem.{u_2, u_2} marks P →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P) →
    (∀ (c : A),
        Membership.mem.{u_2, u_2} columns c →
          HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c) →
      (∀ (q : Prod.{u_2, u_2} A A),
          Membership.mem.{u_2, u_2} pairs q →
            HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D q.1) →
        ∀ (d : A),
          Eq.{1}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceRow.{u_1, u_2} D normI a₀ ρ₀ lam Ω marks columns
              pairs d)
            (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rowFactor.{u_1, u_2} D ρ₀ d)
              (HeckeSkeleton.LowFrozenCube.frozenSeparatedRow.{u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                (fun P =>
                  HDiv.hDiv.{0, 0, 0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀ P)
                    ↑√(normI P))
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualCoefficient.{u_1, u_2} D normI lam Ω) marks
                columns pairs d))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceRow_eq_hybridRow

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
  (Ω : A → A → A → ℂ) (marks columns : Finset.{u_2} A) (pairs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  (∀ (P : A),
      Membership.mem.{u_2, u_2} marks P →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P) →
    (∀ (c : A),
        Membership.mem.{u_2, u_2} columns c →
          HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c) →
      (∀ (q : Prod.{u_2, u_2} A A),
          Membership.mem.{u_2, u_2} pairs q →
            HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D q.1 ∧
              HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.2) →
        ∀ (d : A),
          Eq.{1}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceRow.{u_1, u_2} D normI a₀ ρ₀ lam Ω marks columns
              pairs d)
            (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rowFactor.{u_1, u_2} D ρ₀ d)
              (HeckeSkeleton.LowHybrid.hybridRow.{u_2}
                (fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b)
                (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                normI (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.beta.{u_1, u_2} D normI lam Ω) marks columns
                (Finset.image.{u_2, u_2} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2} pairs) d))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceTerm_column_overlap_zero

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
  (Ω : A → A → A → ℂ) (d P c x n : A) (p : ι),
  Ne.{1}
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P)
        p)
      0 →
    Ne.{1}
        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) c)
          p)
        0 →
      Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceTerm.{u_1, u_2} D normI a₀ ρ₀ lam Ω d P c x n) 0
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceTerm_fullCube_overlap_zero

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
  (Ω : A → A → A → ℂ) (d P c x n : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P →
    HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
      ¬HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P (HMul.hMul.{u_2, u_2, u_2} x n) →
        Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceTerm.{u_1, u_2} D normI a₀ ρ₀ lam Ω d P c x n) 0
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceTerm_row_overlap_zero

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
  (Ω : A → A → A → ℂ) (d P c x n : A) (p : ι),
  Ne.{1}
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P)
        p)
      0 →
    Ne.{1}
        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) d)
          p)
        0 →
      Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceTerm.{u_1, u_2} D normI a₀ ρ₀ lam Ω d P c x n) 0
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.source_energy_eq_hybridEnergy

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
  (Ω : A → A → A → ℂ) (rows marks columns : Finset.{u_2} A) (pairs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  (∀ (d : A),
      Membership.mem.{u_2, u_2} rows d →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d) →
    (∀ (d : A), Membership.mem.{u_2, u_2} rows d → Eq.{1} (Norm.norm.{0} (ρ₀ d)) 1) →
      (∀ (P : A),
          Membership.mem.{u_2, u_2} marks P →
            HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P) →
        (∀ (c : A),
            Membership.mem.{u_2, u_2} columns c →
              HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c) →
          (∀ (q : Prod.{u_2, u_2} A A),
              Membership.mem.{u_2, u_2} pairs q →
                HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D q.1 ∧
                  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.2) →
            Eq.{1}
              (∑ d ∈ rows,
                HPow.hPow.{0, 0, 0}
                  (Norm.norm.{0}
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceRow.{u_1, u_2} D normI a₀ ρ₀ lam Ω marks
                      columns pairs d))
                  2)
              (HeckeSkeleton.LowHybrid.hybridEnergy.{u_2}
                (fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b)
                (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                normI (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.beta.{u_1, u_2} D normI lam Ω) rows marks columns
                (Finset.image.{u_2, u_2} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2} pairs))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.source_energy_ledger

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    (∀ (a : A), LE.le.{0} 1 (q a)) →
      ∀ (Ccount : ℝ),
        LT.lt.{0} 0 Ccount →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
            (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b) →
              (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                  (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                  fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b) →
                ∀ (eps : ℝ),
                  LT.lt.{0} 0 eps →
                    ∃ C,
                      LT.lt.{0} 0 C ∧
                        ∀ (Z O H v ell S B z T : ℝ),
                          LE.le.{0} 1 Z →
                            LE.le.{0} 0 H →
                              LE.le.{0} 0 v →
                                LE.le.{0} 0 ell →
                                  LE.le.{0} 0 z →
                                    ∀ (b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A)
                                      (a :
                                        HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1, u_2} D (⇑normI)
                                          Z H v ell z b),
                                      HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.{u_1, u_2} D
                                          (⇑normI) b →
                                        LE.le.{0} (HPow.hPow.{0, 0, 0} Z (HAdd.hAdd.{0, 0, 0} S B))
                                            (normI
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.{u_1, u_2}
                                                D)) →
                                          LE.le.{0}
                                            (HMul.hMul.{0, 0, 0}
                                              (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z (HDiv.hDiv.{0, 0, 0} O 2))
                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.energy.{u_1,
                                                    u_2}
                                                  b D ⇑normI))
                                              (HPow.hPow.{0, 0, 0} Z
                                                (HeckeSkeleton.LowFrozenCube.squaredKernelExponent T v ell)))
                                            (HMul.hMul.{0, 0, 0} C
                                              (HPow.hPow.{0, 0, 0} Z
                                                (HAdd.hAdd.{0, 0, 0}
                                                  (HeckeSkeleton.LowFrozenCube.reflectedExponent O H v ell S B z T)
                                                  (HMul.hMul.{0, 0, 0} eps
                                                    (HAdd.hAdd.{0, 0, 0}
                                                      (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} H v) ell) z)))))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.source_energy_power_saving

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    (∀ (a : A), LE.le.{0} 1 (q a)) →
      ∀ (Ccount : ℝ),
        LT.lt.{0} 0 Ccount →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
            (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b) →
              (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                  (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                  fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b) →
                ∀ (eps : ℝ),
                  LT.lt.{0} 0 eps →
                    ∃ C,
                      LT.lt.{0} 0 C ∧
                        ∀ (Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau : ℝ),
                          LE.le.{0} 1 Z →
                            LE.le.{0} 0 H →
                              LE.le.{0} 0 O →
                                LE.le.{0} 0 S →
                                  LE.le.{0} 0 B →
                                    LE.le.{0} 0 ell →
                                      LE.le.{0} 0 v →
                                        LE.le.{0} 0 z →
                                          LE.le.{0} 0 Q →
                                            LE.le.{0} 0 M →
                                              LE.le.{0} 0 c →
                                                Eq.{1} F (HAdd.hAdd.{0, 0, 0} N V) →
                                                  Eq.{1} Nstar (HSub.hSub.{0, 0, 0} N (HMul.hMul.{0, 0, 0} 3 bh)) →
                                                    LE.le.{0} V delta →
                                                      LE.le.{0} bh delta →
                                                        LE.le.{0} z z0 →
                                                          LE.le.{0} H (HSub.hSub.{0, 0, 0} M O) →
                                                            LE.le.{0} c
                                                                (HSub.hSub.{0, 0, 0}
                                                                  (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} F M) Q)
                                                                  z0) →
                                                              LE.le.{0} c
                                                                  (HSub.hSub.{0, 0, 0}
                                                                    (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} 4 F)
                                                                      (HMul.hMul.{0, 0, 0} 3 M))
                                                                    (HMul.hMul.{0, 0, 0} 6 z0)) →
                                                                LE.le.{0}
                                                                    (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} T S) B)
                                                                    (HAdd.hAdd.{0, 0, 0}
                                                                      (HSub.hSub.{0, 0, 0}
                                                                        (HAdd.hAdd.{0, 0, 0}
                                                                          (HAdd.hAdd.{0, 0, 0}
                                                                            (HSub.hSub.{0, 0, 0}
                                                                              (HMul.hMul.{0, 0, 0} 2 M) O)
                                                                            Q)
                                                                          V)
                                                                        Nstar)
                                                                      (HMul.hMul.{0, 0, 0} 2 z)) →
                                                                  LE.le.{0}
                                                                      (HAdd.hAdd.{0, 0, 0} v
                                                                        (HMul.hMul.{0, 0, 0} 3 ell))
                                                                      (HAdd.hAdd.{0, 0, 0} T tau) →
                                                                    LE.le.{0} delta (HDiv.hDiv.{0, 0, 0} c 100) →
                                                                      LE.le.{0} tau (HDiv.hDiv.{0, 0, 0} c 8) →
                                                                        LE.le.{0}
                                                                            (HMul.hMul.{0, 0, 0} eps
                                                                              (HAdd.hAdd.{0, 0, 0}
                                                                                (HAdd.hAdd.{0, 0, 0}
                                                                                  (HAdd.hAdd.{0, 0, 0} H v) ell)
                                                                                z))
                                                                            (HDiv.hDiv.{0, 0, 0} c 4) →
                                                                          ∀
                                                                            (b :
                                                                              HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1,
                                                                                  u_2}
                                                                                ι A)
                                                                            (a :
                                                                              HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1,
                                                                                  u_2}
                                                                                D (⇑normI) Z H v ell z b),
                                                                            HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.{u_1,
                                                                                  u_2}
                                                                                D (⇑normI) b →
                                                                              LE.le.{0}
                                                                                  (HPow.hPow.{0, 0, 0} Z
                                                                                    (HAdd.hAdd.{0, 0, 0} S B))
                                                                                  (normI
                                                                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.{u_1,
                                                                                        u_2}
                                                                                      D)) →
                                                                                LE.le.{0}
                                                                                  (HMul.hMul.{0, 0, 0}
                                                                                    (HMul.hMul.{0, 0, 0}
                                                                                      (HPow.hPow.{0, 0, 0} Z
                                                                                        (HDiv.hDiv.{0, 0, 0} O 2))
                                                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.energy.{u_1,
                                                                                          u_2}
                                                                                        b D ⇑normI))
                                                                                    (HPow.hPow.{0, 0, 0} Z
                                                                                      (HeckeSkeleton.LowFrozenCube.squaredKernelExponent
                                                                                        T v ell)))
                                                                                  (HMul.hMul.{0, 0, 0} C
                                                                                    (HPow.hPow.{0, 0, 0} Z
                                                                                      (HSub.hSub.{0, 0, 0} F
                                                                                        (HDiv.hDiv.{0, 0, 0} c 4))))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.source_energy_terminal

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    (∀ (a : A), LE.le.{0} 1 (q a)) →
      ∀ (Ccount : ℝ),
        LT.lt.{0} 0 Ccount →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
            (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b) →
              (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                  (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                  fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b) →
                ∀ (eps : ℝ),
                  LT.lt.{0} 0 eps →
                    ∃ C,
                      LT.lt.{0} 0 C ∧
                        ∀ (Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau : ℝ),
                          LE.le.{0} 1 Z →
                            LE.le.{0} 0 H →
                              LE.le.{0} 0 O →
                                LE.le.{0} 0 S →
                                  LE.le.{0} 0 B →
                                    LE.le.{0} 0 ell →
                                      LE.le.{0} 0 v →
                                        LE.le.{0} 0 z →
                                          LE.le.{0} 0 Q →
                                            Eq.{1} F (HAdd.hAdd.{0, 0, 0} N V) →
                                              Eq.{1} Nstar (HSub.hSub.{0, 0, 0} N (HMul.hMul.{0, 0, 0} 3 bh)) →
                                                LE.le.{0} V delta →
                                                  LE.le.{0} bh delta →
                                                    LE.le.{0} z z0 →
                                                      LE.le.{0} H (HSub.hSub.{0, 0, 0} M O) →
                                                        LE.le.{0} c
                                                            (HSub.hSub.{0, 0, 0}
                                                              (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} F M) Q) z0) →
                                                          LE.le.{0} c
                                                              (HSub.hSub.{0, 0, 0}
                                                                (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} 4 F)
                                                                  (HMul.hMul.{0, 0, 0} 3 M))
                                                                (HMul.hMul.{0, 0, 0} 6 z0)) →
                                                            LE.le.{0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} T S) B)
                                                                (HAdd.hAdd.{0, 0, 0}
                                                                  (HSub.hSub.{0, 0, 0}
                                                                    (HAdd.hAdd.{0, 0, 0}
                                                                      (HAdd.hAdd.{0, 0, 0}
                                                                        (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 M)
                                                                          O)
                                                                        Q)
                                                                      V)
                                                                    Nstar)
                                                                  (HMul.hMul.{0, 0, 0} 2 z)) →
                                                              LE.le.{0}
                                                                  (HAdd.hAdd.{0, 0, 0} v (HMul.hMul.{0, 0, 0} 3 ell))
                                                                  (HAdd.hAdd.{0, 0, 0} T tau) →
                                                                ∀
                                                                  (b :
                                                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1,
                                                                        u_2}
                                                                      ι A)
                                                                  (a :
                                                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.{u_1,
                                                                        u_2}
                                                                      D (⇑normI) Z H v ell z b),
                                                                  HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.{u_1,
                                                                        u_2}
                                                                      D (⇑normI) b →
                                                                    LE.le.{0}
                                                                        (HPow.hPow.{0, 0, 0} Z
                                                                          (HAdd.hAdd.{0, 0, 0} S B))
                                                                        (normI
                                                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.{u_1,
                                                                              u_2}
                                                                            D)) →
                                                                      LE.le.{0}
                                                                        (HMul.hMul.{0, 0, 0}
                                                                          (HMul.hMul.{0, 0, 0}
                                                                            (HPow.hPow.{0, 0, 0} Z
                                                                              (HDiv.hDiv.{0, 0, 0} O 2))
                                                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.energy.{u_1,
                                                                                u_2}
                                                                              b D ⇑normI))
                                                                          (HPow.hPow.{0, 0, 0} Z
                                                                            (HeckeSkeleton.LowFrozenCube.squaredKernelExponent
                                                                              T v ell)))
                                                                        (HMul.hMul.{0, 0, 0} C
                                                                          (HPow.hPow.{0, 0, 0} Z
                                                                            (HAdd.hAdd.{0, 0, 0}
                                                                              (HeckeSkeleton.LowFrozenCube.terminalBound
                                                                                F M c delta tau)
                                                                              (HMul.hMul.{0, 0, 0} eps
                                                                                (HAdd.hAdd.{0, 0, 0}
                                                                                  (HAdd.hAdd.{0, 0, 0}
                                                                                    (HAdd.hAdd.{0, 0, 0} H v) ell)
                                                                                  z)))))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.source_ledger_bound_from_weighted

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (eps C0 : ℝ),
      LT.lt.{0} 0 C0 →
        HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.WeightedRawHybridBound.{u_1, u_2} D normI eps C0 →
          HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceLedgerBound.{u_1, u_2} D normI eps
            (HMul.hMul.{0, 0, 0} 48 C0)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol_mul_first

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (a b c : A),
  Eq.{1} ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D (HMul.hMul.{u_2, u_2, u_2} a b)) c)
    (HMul.hMul.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) c)
      ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D b) c))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol_norm_of_coprime

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (a b : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) a b →
    Eq.{1} (Norm.norm.{0} ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b)) 1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableMajorant_nonneg

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ),
  LE.le.{0} 0 (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableMajorant.{u_1, u_2} D normI first prefactor atZero)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableMajorant_sq_le_charge

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ),
      (∀ (p : ι),
          Membership.mem.{u_1, u_1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) p →
            Eq.{1}
                ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
                  p)
                0 ∨
              Eq.{1}
                  ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
                    p)
                  1 ∨
                Eq.{1}
                  ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
                    p)
                  3) →
        (∀ (p : ι),
            Membership.mem.{u_1, u_1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) p →
              LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (first p)) 2)
                (HDiv.hDiv.{0, 0, 0} 1
                  (normI (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.prime.{u_1, u_2} D p)))) →
          (∀ (p : ι),
              Membership.mem.{u_1, u_1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) p →
                LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (prefactor p)) 2)
                  (normI (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.prime.{u_1, u_2} D p))) →
            (∀ (p : ι),
                Membership.mem.{u_1, u_1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) p →
                  LE.le.{0}
                    (HPow.hPow.{0, 0, 0}
                      (Norm.norm.{0} (atZero p (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D p)))
                      2)
                    (ite.{1}
                      (Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D p) 0 ∨
                        Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D p) 4)
                      (HDiv.hDiv.{0, 0, 0} 1
                        (normI (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.prime.{u_1, u_2} D p)))
                      1)) →
              LE.le.{0}
                (HPow.hPow.{0, 0, 0}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableMajorant.{u_1, u_2} D (⇑normI) first prefactor
                    atZero)
                  2)
                (Inv.inv.{0} (normI (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.{u_1, u_2} D)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableOmega_norm_le

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ),
      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D) →
        ∀ (c x n : A),
          HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
            LE.le.{0} (Norm.norm.{0} (phase c x n)) 1 →
              LE.le.{0}
                (Norm.norm.{0}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableOmega.{u_1, u_2} D (⇑normI) first prefactor
                    atZero phase c x n))
                (HDiv.hDiv.{0, 0, 0}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableMajorant.{u_1, u_2} D (⇑normI) first prefactor
                    atZero)
                  (normI x))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.table_cubeNorm_eq

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D) →
    ∀ (x : A),
      HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
        Eq.{1}
          (HeckeSkeleton.LowFrozenCube.LocalTable.cubeNorm.{u_1}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
            (fun p => normI (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.prime.{u_1, u_2} D p))
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.exponents.{u_1, u_2} D x))
          (normI x)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.table_minimumMajorant_eq

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (x : A),
  HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.CanonicalCube.{u_1, u_2} D x →
    Eq.{1}
      (HeckeSkeleton.LowFrozenCube.LocalTable.minimumMajorant.{u_1}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
        (fun p => normI (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.prime.{u_1, u_2} D p)) first prefactor atZero
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.exponents.{u_1, u_2} D x))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableMajorant.{u_1, u_2} D normI first prefactor atZero)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.uniform_weighted_raw_hybrid_bound

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (symbol : A → MonoidHom.{u_2, 0} A ℂ),
  (∀ (a b c : A),
      Eq.{1} ((symbol (HMul.hMul.{u_2, u_2, u_2} a b)) c) (HMul.hMul.{0, 0, 0} ((symbol a) c) ((symbol b) c))) →
    (∀ (a b : A),
        Eq.{1} (HPow.hPow.{0, 0, 0} ((symbol a) b) 6)
          (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a b) 1 0)) →
      ∀ (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
        (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
          (∀ (a : A), LE.le.{0} 1 (q a)) →
            ∀ (Ccount : ℝ),
              LT.lt.{0} 0 Ccount →
                HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
                  (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b => (symbol a) b) →
                    (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                        (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2} coords) fun a b =>
                        (symbol a) b) →
                      ∀ (eps : ℝ),
                        LT.lt.{0} 0 eps →
                          ∃ C0,
                            LT.lt.{0} 0 C0 ∧
                              ∀ (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A),
                                Eq.{max (u_1 + 1) (u_2 + 1)}
                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) coords →
                                  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D)
                                      symbol →
                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.WeightedRawHybridBound.{u_1, u_2} D
                                      normI eps C0
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta_norm_le

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (lam : A → ℂ)
  (Ω : A → A → A → ℂ) (B C : ℝ),
  LT.lt.{0} 0 B →
    LE.le.{0} 0 C →
      ∀ (c b : A),
        LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.beta.{u_1, u_2} D normI lam Ω c b))
            (HDiv.hDiv.{0, 0, 0} C B) →
          LE.le.{0}
            (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.{u_1, u_2} D normI lam Ω B C c b))
            1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.valuation_prime

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (p : ι),
  Eq.{u_1 + 1}
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.prime.{u_1, u_2} D p))
    (Finsupp.single.{u_1, 0} p 1)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.weighted_raw_frozen_row_block_exit

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ),
  (∀ (a : A), LT.lt.{0} 0 (normI a)) →
    ∀ (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ) (K N B : ℝ),
      LT.lt.{0} 0 N →
        LT.lt.{0} 0 B →
          ∀ (pow sup : A) (rows marks columns : Finset.{u_2} A) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
            (∀ (k : A), Membership.mem.{u_2, u_2} rows k → LE.le.{0} (normI k) K) →
              (∀ (d : A),
                  (∀ (p : ι),
                      LE.le.{0}
                        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) d)
                          p)
                        1) →
                    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d →
                      Eq.{1} (Norm.norm.{0} (ρ₀ d)) 1) →
                (∀ (P : A),
                    Membership.mem.{u_2, u_2} marks P →
                      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P) →
                  (∀ (P : A), Membership.mem.{u_2, u_2} marks P → LE.le.{0} (Norm.norm.{0} (a₀ P)) 1) →
                    (∀ (c : A),
                        Membership.mem.{u_2, u_2} columns c →
                          HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c) →
                      (∀ (c : A), Membership.mem.{u_2, u_2} columns c → LE.le.{0} (Norm.norm.{0} (lam c)) 1) →
                        (∀ (c : A), Membership.mem.{u_2, u_2} columns c → LE.le.{0} N (normI c)) →
                          (∀ (q : Prod.{u_2, u_2} A A),
                              Membership.mem.{u_2, u_2} inputs q →
                                HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.1) →
                            (∀ (q : Prod.{u_2, u_2} A A),
                                Membership.mem.{u_2, u_2} inputs q →
                                  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.2) →
                              (∀ (c : A),
                                  Membership.mem.{u_2, u_2} columns c →
                                    ∀ (q : Prod.{u_2, u_2} A A),
                                      Membership.mem.{u_2, u_2} inputs q →
                                        LE.le.{0} (Norm.norm.{0} (phase c q.1 q.2)) 1) →
                                (∀ (q : Prod.{u_2, u_2} A A),
                                    Membership.mem.{u_2, u_2} inputs q →
                                      LE.le.{0} B
                                        (normI
                                          (HMul.hMul.{u_2, u_2, u_2}
                                            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                              q.1)
                                            q.2))) →
                                  have residual :=
                                    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2}
                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) pow sup
                                      rows;
                                  have pairs :=
                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenInputPairs.{u_1, u_2} D
                                      (⇑normI) first prefactor atZero inputs;
                                  have Ω :=
                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableOmega.{u_1, u_2} D (⇑normI)
                                      first prefactor atZero
                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenPhase.{u_1, u_2} D phase);
                                  have C :=
                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableMajorant.{u_1, u_2} D (⇑normI)
                                      first prefactor atZero;
                                  have gamma :=
                                    HeckeSkeleton.LowFrozenCube.FrozenReduction.unitAnnularColumn.{u_2} (⇑normI) N lam;
                                  LE.le.{0} 1
                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualParameter.{u_1, u_2} D
                                        (⇑normI) K pow sup) ∧
                                    (∀ (d : A),
                                        Membership.mem.{u_2, u_2} residual d →
                                          (∀ (p : ι),
                                              LE.le.{0}
                                                ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2}
                                                      D)
                                                    d)
                                                  p)
                                                1) ∧
                                            HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D)
                                                d ∧
                                              LE.le.{0} (normI d)
                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualParameter.{u_1,
                                                    u_2}
                                                  D (⇑normI) K pow sup)) ∧
                                      (∀ (P : A),
                                          Membership.mem.{u_2, u_2} marks P →
                                            LE.le.{0}
                                              (Norm.norm.{0}
                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀
                                                  P))
                                              1) ∧
                                        (∀ (c : A),
                                            Membership.mem.{u_2, u_2} columns c →
                                              ∀ (b : A),
                                                Membership.mem.{u_2, u_2}
                                                    (Finset.image.{u_2, u_2}
                                                      HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2} pairs)
                                                    b →
                                                  LE.le.{0}
                                                    (Norm.norm.{0}
                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.{u_1,
                                                          u_2}
                                                        D (⇑normI) gamma Ω B C c b))
                                                    1) ∧
                                          Eq.{1}
                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawBlockSourceEnergy.{u_1,
                                                u_2}
                                              D (⇑normI) first prefactor atZero phase a₀ ρ₀
                                              (HeckeSkeleton.LowFrozenCube.FrozenReduction.annularColumn.{u_2} (⇑normI)
                                                lam)
                                              pow sup rows marks columns inputs)
                                            (HMul.hMul.{0, 0, 0}
                                              (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} C B) 2) N)
                                              (HeckeSkeleton.LowHybrid.hybridEnergy.{u_2}
                                                (fun a b =>
                                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D
                                                      a)
                                                    b)
                                                (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
                                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2}
                                                    D))
                                                (⇑normI)
                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mark.{u_1, u_2} D a₀)
                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.{u_1, u_2} D
                                                  (⇑normI) gamma Ω B C)
                                                residual marks columns
                                                (Finset.image.{u_2, u_2} HeckeSkeleton.LowFrozenCube.cubeProduct.{u_2}
                                                  pairs)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.weighted_raw_hybrid_bound

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : MonoidHom.{u_2, 0} A ℝ) (q : A → ℕ),
  (∀ (a : A), Eq.{1} (normI a) ↑(q a)) →
    (∀ (a : A), LE.le.{0} 1 (q a)) →
      ∀ (Ccount : ℝ),
        LT.lt.{0} 0 Ccount →
          HeckeSkeleton.LowHybrid.LinearNormCounting.{u_2} q Ccount →
            (HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_2} (⇑normI)
                (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b) →
              (HeckeSkeleton.LowHybrid.CubicSieveInput.{u_2} (⇑normI)
                  (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
                  fun a b => (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D a) b) →
                ∀ (eps : ℝ),
                  LT.lt.{0} 0 eps →
                    ∃ C0,
                      LT.lt.{0} 0 C0 ∧
                        ∀ (R K N B L Nmin Bmin : ℝ),
                          LE.le.{0} 1 K →
                            LE.le.{0} 1 N →
                              LE.le.{0} 1 B →
                                LE.le.{0} 1 L →
                                  LT.lt.{0} 0 Nmin →
                                    LT.lt.{0} 0 Bmin →
                                      ∀ (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
                                        (a₀ ρ₀ lam : A → ℂ) (pow sup : A) (rows marks columns : Finset.{u_2} A)
                                        (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
                                        (∀ (k : A), Membership.mem.{u_2, u_2} rows k → LE.le.{0} (normI k) R) →
                                          (∀ (d : A),
                                              Membership.mem.{u_2, u_2}
                                                  (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2}
                                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2}
                                                      D)
                                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2}
                                                      D)
                                                    pow sup rows)
                                                  d →
                                                LE.le.{0} (normI d) K) →
                                            (∀ (d : A),
                                                (∀ (p : ι),
                                                    LE.le.{0}
                                                      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1,
                                                            u_2}
                                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                              u_2}
                                                            D)
                                                          d)
                                                        p)
                                                      1) →
                                                  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                          u_2}
                                                        D)
                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1,
                                                          u_2}
                                                        D)
                                                      d →
                                                    Eq.{1} (Norm.norm.{0} (ρ₀ d)) 1) →
                                              (∀ (P : A),
                                                  Membership.mem.{u_2, u_2} marks P →
                                                    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                          u_2}
                                                        D)
                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1,
                                                          u_2}
                                                        D)
                                                      P) →
                                                (∀ (P : A),
                                                    Membership.mem.{u_2, u_2} marks P →
                                                      HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
                                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                              u_2}
                                                            D)
                                                          P ∧
                                                        LE.le.{0} (normI P) L) →
                                                  (∀ (P : A),
                                                      Membership.mem.{u_2, u_2} marks P →
                                                        LE.le.{0} (Norm.norm.{0} (a₀ P)) 1) →
                                                    (∀ (c : A),
                                                        Membership.mem.{u_2, u_2} columns c →
                                                          HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
                                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                                u_2}
                                                              D)
                                                            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1,
                                                                u_2}
                                                              D)
                                                            c) →
                                                      (∀ (c : A),
                                                          Membership.mem.{u_2, u_2} columns c →
                                                            HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1,
                                                                  u_2}
                                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                                    u_2}
                                                                  D)
                                                                c ∧
                                                              LE.le.{0} (normI c) N) →
                                                        (∀ (c : A),
                                                            Membership.mem.{u_2, u_2} columns c →
                                                              LE.le.{0} (Norm.norm.{0} (lam c)) 1) →
                                                          (∀ (c : A),
                                                              Membership.mem.{u_2, u_2} columns c →
                                                                LE.le.{0} Nmin (normI c)) →
                                                            (∀ (u : Prod.{u_2, u_2} A A),
                                                                Membership.mem.{u_2, u_2} inputs u →
                                                                  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1,
                                                                      u_2}
                                                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                                        u_2}
                                                                      D)
                                                                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1,
                                                                        u_2}
                                                                      D)
                                                                    u.1) →
                                                              (∀ (u : Prod.{u_2, u_2} A A),
                                                                  Membership.mem.{u_2, u_2} inputs u →
                                                                    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1,
                                                                        u_2}
                                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                                          u_2}
                                                                        D)
                                                                      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1,
                                                                          u_2}
                                                                        D)
                                                                      u.2) →
                                                                (∀ (c : A),
                                                                    Membership.mem.{u_2, u_2} columns c →
                                                                      ∀ (u : Prod.{u_2, u_2} A A),
                                                                        Membership.mem.{u_2, u_2} inputs u →
                                                                          LE.le.{0} (Norm.norm.{0} (phase c u.1 u.2))
                                                                            1) →
                                                                  (∀ (u : Prod.{u_2, u_2} A A),
                                                                      Membership.mem.{u_2, u_2} inputs u →
                                                                        LE.le.{0} Bmin
                                                                          (normI
                                                                            (HMul.hMul.{u_2, u_2, u_2}
                                                                              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1,
                                                                                  u_2}
                                                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                                                    u_2}
                                                                                  D)
                                                                                u.1)
                                                                              u.2))) →
                                                                    (∀ (u : Prod.{u_2, u_2} A A),
                                                                        Membership.mem.{u_2, u_2} inputs u →
                                                                          LE.le.{0}
                                                                            (normI
                                                                              (HMul.hMul.{u_2, u_2, u_2}
                                                                                (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1,
                                                                                    u_2}
                                                                                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1,
                                                                                      u_2}
                                                                                    D)
                                                                                  u.1)
                                                                                u.2))
                                                                            B) →
                                                                      LE.le.{0}
                                                                        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawBlockSourceEnergy.{u_1,
                                                                            u_2}
                                                                          D (⇑normI) first prefactor atZero phase a₀ ρ₀
                                                                          (HeckeSkeleton.LowFrozenCube.FrozenReduction.annularColumn.{u_2}
                                                                            (⇑normI) lam)
                                                                          pow sup rows marks columns inputs)
                                                                        (HMul.hMul.{0, 0, 0}
                                                                          (HDiv.hDiv.{0, 0, 0}
                                                                            (HPow.hPow.{0, 0, 0}
                                                                              (HDiv.hDiv.{0, 0, 0}
                                                                                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.tableMajorant.{u_1,
                                                                                    u_2}
                                                                                  D (⇑normI) first prefactor atZero)
                                                                                Bmin)
                                                                              2)
                                                                            Nmin)
                                                                          (HMul.hMul.{0, 0, 0}
                                                                            (HMul.hMul.{0, 0, 0}
                                                                              (HMul.hMul.{0, 0, 0}
                                                                                (HMul.hMul.{0, 0, 0} C0
                                                                                  (HPow.hPow.{0, 0, 0}
                                                                                    (HMul.hMul.{0, 0, 0}
                                                                                      (HMul.hMul.{0, 0, 0}
                                                                                        (HMul.hMul.{0, 0, 0} K N) B)
                                                                                      L)
                                                                                    eps))
                                                                                (HAdd.hAdd.{0, 0, 0} K
                                                                                  (HMul.hMul.{0, 0, 0} N B)))
                                                                              B)
                                                                            (HAdd.hAdd.{0, 0, 0}
                                                                              (HAdd.hAdd.{0, 0, 0} N L)
                                                                              (HPow.hPow.{0, 0, 0}
                                                                                (HMul.hMul.{0, 0, 0} N L) (2 / 3)))))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.FrozenFamilyAlignment.coordinates

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))} {base : Finset.{u_1} ι}
  {rows : Finset.{u_2} A} {data : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A}
  {family : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A},
  HeckeSkeleton.LowFrozenCube.FrozenReduction.FrozenFamilyAlignment.{u_1, u_2} coords base rows data family →
    ∀ (pair : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2} coords base rows) pair →
        Eq.{max (u_1 + 1) (u_2 + 1)} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} (data pair))
          coords
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.FrozenFamilyAlignment.original_rows

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))} {base : Finset.{u_1} ι}
  {rows : Finset.{u_2} A} {data : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A}
  {family : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A},
  HeckeSkeleton.LowFrozenCube.FrozenReduction.FrozenFamilyAlignment.{u_1, u_2} coords base rows data family →
    ∀ (pair : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2} coords base rows) pair →
        Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1, u_2} (family pair)) rows
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.FrozenFamilyAlignment.powerful

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))} {base : Finset.{u_1} ι}
  {rows : Finset.{u_2} A} {data : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A}
  {family : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A},
  HeckeSkeleton.LowFrozenCube.FrozenReduction.FrozenFamilyAlignment.{u_1, u_2} coords base rows data family →
    ∀ (pair : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2} coords base rows) pair →
        Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.pow.{u_1, u_2} (family pair)) pair.1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.FrozenFamilyAlignment.support

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))} {base : Finset.{u_1} ι}
  {rows : Finset.{u_2} A} {data : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A}
  {family : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A},
  HeckeSkeleton.LowFrozenCube.FrozenReduction.FrozenFamilyAlignment.{u_1, u_2} coords base rows data family →
    ∀ (pair : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2} coords base rows) pair →
        Eq.{u_1 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} (data pair))
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.extendedFrozenSupport.{u_1, u_2} coords base pair.1)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.FrozenFamilyAlignment.supported

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))} {base : Finset.{u_1} ι}
  {rows : Finset.{u_2} A} {data : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A}
  {family : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A},
  HeckeSkeleton.LowFrozenCube.FrozenReduction.FrozenFamilyAlignment.{u_1, u_2} coords base rows data family →
    ∀ (pair : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.frozenRowPairs.{u_1, u_2} coords base rows) pair →
        Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.sup.{u_1, u_2} (family pair)) pair.2
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.first_sq

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A},
  HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.{u_1, u_2} D normI b →
    ∀ (p : ι),
      Membership.mem.{u_1, u_1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) p →
        LE.le.{0}
          (HPow.hPow.{0, 0, 0}
            (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.first.{u_1, u_2} b p)) 2)
          (HDiv.hDiv.{0, 0, 0} 1 (normI (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.prime.{u_1, u_2} D p)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.prefactor_sq

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A},
  HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.{u_1, u_2} D normI b →
    ∀ (p : ι),
      Membership.mem.{u_1, u_1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) p →
        LE.le.{0}
          (HPow.hPow.{0, 0, 0}
            (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.prefactor.{u_1, u_2} b p)) 2)
          (normI (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.prime.{u_1, u_2} D p))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.zero_sq

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A},
  HeckeSkeleton.LowFrozenCube.FrozenReduction.PrimitiveLocalBounds.{u_1, u_2} D normI b →
    ∀ (p : ι),
      Membership.mem.{u_1, u_1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) p →
        LE.le.{0}
          (HPow.hPow.{0, 0, 0}
            (Norm.norm.{0}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.atZero.{u_1, u_2} b p
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D p)))
            2)
          (ite.{1}
            (Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D p) 0 ∨
              Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D p) 4)
            (HDiv.hDiv.{0, 0, 0} 1 (normI (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.prime.{u_1, u_2} D p))) 1)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.energy_nonneg

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A)
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ),
  LE.le.{0} 0 (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.energy.{u_1, u_2} b D normI)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.energy_zero_of_empty_active

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A)
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ),
  (∀ (q : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) q →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) q.1) →
    Eq.{u_2 + 1}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.activeInputBlock.{u_1, u_2} D normI
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.first.{u_1, u_2} b)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.prefactor.{u_1, u_2} b)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.atZero.{u_1, u_2} b)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b))
        EmptyCollection.emptyCollection.{u_2} →
      Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.energy.{u_1, u_2} b D normI) 0
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceLedgerBound._proof_1

```lean
(HAdd.hAdd.{0, 0, 0} 1 1).AtLeastTwo
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.dyadic_coefficient_scale._simp_1_1

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 2] [NeZero.{u_2} 2], Eq.{1} (Eq.{u_2 + 1} 2 0) False
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.dyadic_coefficient_scale._simp_1_2

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 3] [NeZero.{u_2} 3], Eq.{1} (Eq.{u_2 + 1} 3 0) False
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.dyadic_coefficient_scale._simp_1_3

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 4] [NeZero.{u_2} 4], Eq.{1} (Eq.{u_2 + 1} 4 0) False
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.dyadic_coefficient_scale._simp_1_4

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [NoZeroDivisors.{u_1} M₀] {a b : M₀},
  Ne.{u_1 + 1} a 0 → Ne.{u_1 + 1} b 0 → Eq.{1} (Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} a b) 0) False
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.dyadic_coefficient_scale._simp_1_5

```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀} [IsReduced.{u_1} M₀] (n : ℕ),
  Ne.{u_1 + 1} a 0 → Eq.{1} (Eq.{u_1 + 1} (HPow.hPow.{u_1, 0, u_1} a n) 0) False
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.dyadic_coefficient_scale._simp_1_6

```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero.{u_3} G₀] {a : G₀} (n : ℤ),
  Ne.{u_3 + 1} a 0 → Eq.{1} (Eq.{u_3 + 1} (HPow.hPow.{u_3, 0, u_3} a n) 0) False
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.dyadic_coefficient_scale._simp_1_7

```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne.{u_1} R] [CharZero.{u_1} R] (n : ℕ),
  Eq.{1} (Eq.{u_1 + 1} (HAdd.hAdd.{u_1, u_1, u_1} (↑n) 1) 0) False
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.unitAnnularColumn.eq_1

```lean
∀ {A : Type u_2} (normI : A → ℝ) (N : ℝ) (lam : A → ℂ) (c : A),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.unitAnnularColumn.{u_2} normI N lam c)
    (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} ↑√N ↑√(normI c)) (lam c))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.varyingFamilySourceRow.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (base : Finset.{u_1} ι) (normI : A → ℝ)
  (data : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A)
  (family : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A) (k : A),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.varyingFamilySourceRow.{u_1, u_2} coords base normI data family k)
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceRow.{u_1, u_2}
      (data
        (Prod.mk.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k)
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords base k)))
      normI
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.first.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords base k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.prefactor.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords base k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.atZero.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords base k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.phase.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords base k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.a₀.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords base k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.ρ₀.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords base k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.annularColumn.{u_2} normI
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.lam.{u_1, u_2}
          (family
            (Prod.mk.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k)
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords base k)))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords base k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords base k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords base k))))
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2} coords base k))
```

## HeckeSkeleton.LowFrozenCube.LocalTable.minimumCharge.eq_1

```lean
∀ (j m : ℕ),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.LocalTable.minimumCharge j m)
    (ite.{1} (Eq.{1} m 3 ∨ Eq.{1} m 0 ∧ (Eq.{1} j 0 ∨ Eq.{1} j 4)) 1 0)
```

## HeckeSkeleton.LowFrozenCube.LocalTable.minimumCharge_le_one._proof_1_1

```lean
¬LE.le.{0} 1 1 → False
```

## HeckeSkeleton.LowFrozenCube.LocalTable.minimumCharge_le_one._proof_1_2

```lean
¬LE.le.{0} 0 1 → False
```

## HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar.eq_1

```lean
∀ (q first prefactor : ℂ) (atZero : ℕ → ℂ) (j e : ℕ),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar q first prefactor atZero j e)
    (ite.{1} (Eq.{1} e 0) (atZero j)
      (ite.{1} (Eq.{1} j 4)
        (HMul.hMul.{0, 0, 0} prefactor (HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar q first e)) 0))
```

## HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar_add_cube._proof_1_1

```lean
∀ (e : ℕ), LT.lt.{0} 0 e → Eq.{1} e 0 → False
```

## HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar_add_cube._proof_1_2

```lean
∀ (e x : ℕ), LT.lt.{0} 0 e → Eq.{1} (HAdd.hAdd.{0, 0, 0} e (HMul.hMul.{0, 0, 0} 3 x)) 0 → False
```

## HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar_frozen._proof_1_1

```lean
∀ (e : ℕ),
  Ne.{1} (HeckeSkeleton.LowFrozenCube.frozenMin e) 0 → ¬LT.lt.{0} 0 (HeckeSkeleton.LowFrozenCube.frozenMin e) → False
```

## HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar_nonzero_admissible._proof_1_1

```lean
∀ (e : ℕ),
  LT.lt.{0} (HMod.hMod.{0, 0, 0} e 3) 3 →
    Ne.{1} (HMod.hMod.{0, 0, 0} e 3) 2 →
      ¬(Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 0 ∨ Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 1) → False
```

## HeckeSkeleton.LowFrozenCube.LocalTable.ordinaryScalar_residue_two._proof_1_1

```lean
∀ (e : ℕ), Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 2 → Eq.{1} e 0 → False
```

## HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar.eq_1

```lean
∀ (q first : ℂ) (e : ℕ),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar q first e)
    (ite.{1} (Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 0) (HPow.hPow.{0, 0, 0} (Inv.inv.{0} q) (HDiv.hDiv.{0, 0, 0} e 3))
      (ite.{1} (Eq.{1} (HMod.hMod.{0, 0, 0} e 3) 1)
        (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Inv.inv.{0} q) (HDiv.hDiv.{0, 0, 0} e 3)) first) 0))
```

## HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar_add_cube._proof_1_1

```lean
∀ (e x : ℕ),
  ¬Eq.{1} (HMod.hMod.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} e (HMul.hMul.{0, 0, 0} 3 x)) 3) (HMod.hMod.{0, 0, 0} e 3) → False
```

## HeckeSkeleton.LowFrozenCube.LocalTable.sphericalScalar_add_cube._proof_1_2

```lean
∀ (e x : ℕ),
  Eq.{1} (HMod.hMod.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} e (HMul.hMul.{0, 0, 0} 3 x)) 3) (HMod.hMod.{0, 0, 0} e 3) →
    ¬Eq.{1} (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} e (HMul.hMul.{0, 0, 0} 3 x)) 3)
          (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} e 3) x) →
      False
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.awayFactor.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (a : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.awayFactor.{u_1, u_2} coords s a)
    ((MulEquiv.symm.{u_2, u_1} coords)
      (Multiplicative.ofAdd.{u_1}
        (Finsupp.filter.{u_1, 0} (fun p => p ∉ s)
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a))))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.extendedFrozenSupport.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (base : Finset.{u_1} ι) (pow : A),
  Eq.{u_1 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.extendedFrozenSupport.{u_1, u_2} coords base pow)
    (Union.union.{u_1} base
      (Finsupp.support.{u_1, 0} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords pow)))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.mapExponents.congr_simp

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords coords_1 : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))),
  Eq.{max (u_1 + 1) (u_2 + 1)} coords coords_1 →
    ∀ (f f_1 : ℕ → ℕ) (e_f : Eq.{1} f f_1) (hf : Eq.{1} (f 0) 0) (a a_1 : A),
      Eq.{u_2 + 1} a a_1 →
        Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.mapExponents.{u_1, u_2} coords f hf a)
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.mapExponents.{u_1, u_2} coords_1 f_1 (Eq.ndrec.{0, 1} hf e_f)
            a_1)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.mapExponents.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (f : ℕ → ℕ) (hf : Eq.{1} (f 0) 0)
  (a : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.mapExponents.{u_1, u_2} coords f hf a)
    ((MulEquiv.symm.{u_2, u_1} coords)
      (Multiplicative.ofAdd.{u_1}
        (Finsupp.mapRange.{u_1, 0, 0} f hf
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a))))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.minimumFactor.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.minimumFactor.{u_1, u_2} coords a)
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.mapExponents.{u_1, u_2} coords HeckeSkeleton.LowFrozenCube.frozenMin
      HeckeSkeleton.LowFrozenCube.frozenMin_zero a)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulCubeFactor._proof_1

```lean
Eq.{1} 0 0
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor._proof_1

```lean
Eq.{1} (ite.{1} (LE.le.{0} 2 0) 0 0) 0
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (k : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k)
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.mapExponents.{u_1, u_2} coords (fun e => ite.{1} (LE.le.{0} 2 e) e 0)
      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor._proof_1 k)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulSquareFactor._proof_1

```lean
Eq.{1} (HeckeSkeleton.LowFrozenCube.powerfulSquareExp 0) 0
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulSquareFactor.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulSquareFactor.{u_1, u_2} coords a)
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.mapExponents.{u_1, u_2} coords
      HeckeSkeleton.LowFrozenCube.powerfulSquareExp
      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulSquareFactor._proof_1 a)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.primeElement.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (p : ι),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.primeElement.{u_1, u_2} coords p)
    ((MulEquiv.symm.{u_2, u_1} coords) (Multiplicative.ofAdd.{u_1} (Finsupp.single.{u_1, 0} p 1)))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2} coords a)
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.mapExponents.{u_1, u_2} coords
      HeckeSkeleton.LowFrozenCube.frozenCubeExp HeckeSkeleton.LowFrozenCube.frozenCubeExp_zero a)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (k : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2} coords s k)
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.awayFactor.{u_1, u_2} coords s
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.singleRowFactor.{u_1, u_2} coords k))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.rowBlock.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (pow sup : A)
  (rows : Finset.{u_2} A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.rowBlock.{u_1, u_2} coords s pow sup rows)
    ({k ∈ rows |
      Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2} coords k) pow ∧
        Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords s k) sup})
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.rowBlock_extended._simp_1_1

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred.{u_1 + 1} p] {s : Finset.{u_1} α} {a : α},
  Eq.{1} (Membership.mem.{u_1, u_1} (Finset.filter.{u_1} p s) a) (Membership.mem.{u_1, u_1} s a ∧ p a)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.singleRowFactor._proof_1

```lean
Eq.{1} (ite.{1} (Eq.{1} 0 1) 1 0) 0
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.singleRowFactor.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (k : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.singleRowFactor.{u_1, u_2} coords k)
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.mapExponents.{u_1, u_2} coords (fun e => ite.{1} (Eq.{1} e 1) 1 0)
      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.singleRowFactor._proof_1 k)
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedFactor.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (a : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedFactor.{u_1, u_2} coords s a)
    ((MulEquiv.symm.{u_2, u_1} coords)
      (Multiplicative.ofAdd.{u_1}
        (Finsupp.filter.{u_1, 0} (fun p => Membership.mem.{u_1, u_1} s p)
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a))))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι) (k : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2} coords s k)
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedFactor.{u_1, u_2} coords s
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.singleRowFactor.{u_1, u_2} coords k))
```

## HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A),
  Eq.{u_1 + 1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a)
    (Multiplicative.toAdd.{u_1} (coords a))
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.completed_energy_le._simp_1_1

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 2] [NeZero.{u_2} 2], Eq.{1} (Eq.{u_2 + 1} 2 0) False
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.completed_energy_le._simp_1_2

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 3] [NeZero.{u_2} 3], Eq.{1} (Eq.{u_2 + 1} 3 0) False
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.completed_energy_le._simp_1_3

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 4] [NeZero.{u_2} 4], Eq.{1} (Eq.{u_2 + 1} 4 0) False
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.completed_energy_le._simp_1_4

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [NoZeroDivisors.{u_1} M₀] {a b : M₀},
  Ne.{u_1 + 1} a 0 → Ne.{u_1 + 1} b 0 → Eq.{1} (Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} a b) 0) False
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.completed_energy_le._simp_1_5

```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀} [IsReduced.{u_1} M₀] (n : ℕ),
  Ne.{u_1 + 1} a 0 → Eq.{1} (Eq.{u_1 + 1} (HPow.hPow.{u_1, 0, u_1} a n) 0) False
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.completed_energy_le._simp_1_6

```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero.{u_3} G₀] {a : G₀} (n : ℤ),
  Ne.{u_3 + 1} a 0 → Eq.{1} (Eq.{u_3 + 1} (HPow.hPow.{u_3, 0, u_3} a n) 0) False
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.completed_energy_le._simp_1_7

```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne.{u_1} R] [CharZero.{u_1} R] (n : ℕ),
  Eq.{1} (Eq.{u_1 + 1} (HAdd.hAdd.{u_1, u_1, u_1} (↑n) 1) 0) False
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.completed_quadratic_positive._simp_1_1

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] (a : α), Eq.{1} (LE.le.{u_1} a a) True
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.productCoefficient.eq_1

```lean
∀ {A : Type u_2} [inst : CommMonoid.{u_2} A] (columns cubes : Finset.{u_2} A) (beta : A → A → ℂ) (y : A),
  Eq.{1} (HeckeSkeleton.LowHybrid.CompletedQuadratic.productCoefficient.{u_2} columns cubes beta y)
    (∑ u ∈ SProd.sprod.{u_2, u_2, u_2} columns cubes with Eq.{u_2 + 1} (HMul.hMul.{u_2, u_2, u_2} u.1 u.2) y,
      beta u.1 u.2)
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.product_fiber_card._proof_1_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) ⦃u v : Prod.{u_2, u_2} A A⦄ (p : ι),
  Eq.{1}
      (HAdd.hAdd.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords v.1) p)
        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords u.2) p))
      (HAdd.hAdd.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords v.1) p)
        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords v.2) p)) →
    ¬Eq.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords u.2) p)
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords v.2) p) →
      False
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.squarePart.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (y : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowHybrid.CompletedQuadratic.squarePart.{u_1, u_2} coords y)
    (HeckeSkeleton.LowHybrid.PrimeArithmetic.squarePart.{u_1, u_2} coords y)
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.square_decomposition._proof_1_4

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (y : A) (p : ι),
  ¬Eq.{1}
        (HAdd.hAdd.{0, 0, 0}
          (HMod.hMod.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords y) p) 2)
          (HMul.hMul.{0, 0, 0} 2
            (HDiv.hDiv.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords y) p) 2)))
        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords y) p) →
    False
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreeColumns.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (ys : Finset.{u_2} A) (t : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreeColumns.{u_1, u_2} coords ys t)
    (Finset.image.{u_2, u_2} (HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreePart.{u_1, u_2} coords)
      ({y ∈ ys | Eq.{u_2 + 1} (HeckeSkeleton.LowHybrid.CompletedQuadratic.squarePart.{u_1, u_2} coords y) t}))
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreePart._proof_1

```lean
Eq.{1} (HMod.hMod.{0, 0, 0} 0 2) (HMod.hMod.{0, 0, 0} 0 2)
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreePart.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (y : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreePart.{u_1, u_2} coords y)
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.mapExponents.{u_1, u_2} coords (fun e => HMod.hMod.{0, 0, 0} e 2)
      HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreePart._proof_1 y)
```

## HeckeSkeleton.LowHybrid.CompletedQuadratic.squarefreePart_squarefree._proof_1_2

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (y : A) (p : ι),
  ¬LE.le.{0} (HMod.hMod.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords y) p) 2)
        1 →
    False
```

## HeckeSkeleton.LowHybrid.Factorization.commonExp.eq_1

```lean
∀ (n b : ℕ),
  Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b)
    (Min.min.{0} n (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b))
```

## HeckeSkeleton.LowHybrid.Factorization.common_left_disjoint._proof_1_1

```lean
∀ (n b : ℕ),
  LE.le.{0} n 1 →
    Eq.{1} n
        (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b)
          (HeckeSkeleton.LowHybrid.Factorization.leftExp n b)) →
      ¬(Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b) 0 ∨
            Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.leftExp n b) 0) →
        False
```

## HeckeSkeleton.LowHybrid.Factorization.common_right_disjoint._proof_1_1

```lean
∀ (n b : ℕ),
  Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b)
      (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b)
        (HeckeSkeleton.LowHybrid.Factorization.rightExp n b)) →
    LE.le.{0} (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b) 1 →
      ¬(Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b) 0 ∨
            Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.rightExp n b) 0) →
        False
```

## HeckeSkeleton.LowHybrid.Factorization.completed_cubic_mask._proof_1_1

```lean
∀ {ι : Type u_1} (r c m : ι → ℕ) (p : ι),
  ¬Eq.{1} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (r p) (c p)) (m p))
        (HAdd.hAdd.{0, 0, 0} (r p) (HAdd.hAdd.{0, 0, 0} (c p) (m p))) →
    False
```

## HeckeSkeleton.LowHybrid.Factorization.completed_quadratic_symbol._proof_1_1

```lean
∀ {ι : Type u_1} (n b : ι → ℕ) (p : ι),
  Eq.{1} (HAdd.hAdd.{0, 0, 0} (n p) (b p))
      (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.residualProduct.{u_1} n b p)
        (HMul.hMul.{0, 0, 0} 2 (HeckeSkeleton.LowHybrid.Factorization.maskPart.{u_1} n b p))) →
    ¬Eq.{1} (HAdd.hAdd.{0, 0, 0} (n p) (b p))
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.residualProduct.{u_1} n b p)
              (HeckeSkeleton.LowHybrid.Factorization.maskPart.{u_1} n b p))
            (HeckeSkeleton.LowHybrid.Factorization.maskPart.{u_1} n b p)) →
      False
```

## HeckeSkeleton.LowHybrid.Factorization.completed_square_exponent._proof_1_1

```lean
∀ (n b : ℕ),
  Eq.{1} b
      (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b)
        (HMul.hMul.{0, 0, 0} 2 (HeckeSkeleton.LowHybrid.Factorization.squareExp b))) →
    Eq.{1} n
        (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b)
          (HeckeSkeleton.LowHybrid.Factorization.leftExp n b)) →
      Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b)
          (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b)
            (HeckeSkeleton.LowHybrid.Factorization.rightExp n b)) →
        ¬Eq.{1} (HAdd.hAdd.{0, 0, 0} n b)
              (HAdd.hAdd.{0, 0, 0}
                (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.leftExp n b)
                  (HeckeSkeleton.LowHybrid.Factorization.rightExp n b))
                (HMul.hMul.{0, 0, 0} 2
                  (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b)
                    (HeckeSkeleton.LowHybrid.Factorization.squareExp b)))) →
          False
```

## HeckeSkeleton.LowHybrid.Factorization.coprimeVector_add_right._proof_1_1

```lean
∀ {ι : Type u_1} (P a b : ι → ℕ) (p : ι),
  Eq.{1} (P p) 0 ∨ Eq.{1} (HAdd.hAdd.{0, 0, 0} (a p) (b p)) 0 → ¬(Eq.{1} (P p) 0 ∨ Eq.{1} (a p) 0) → False
```

## HeckeSkeleton.LowHybrid.Factorization.coprimeVector_add_right._proof_1_2

```lean
∀ {ι : Type u_1} (P a b : ι → ℕ) (p : ι),
  Eq.{1} (P p) 0 ∨ Eq.{1} (HAdd.hAdd.{0, 0, 0} (a p) (b p)) 0 → ¬(Eq.{1} (P p) 0 ∨ Eq.{1} (b p) 0) → False
```

## HeckeSkeleton.LowHybrid.Factorization.coprimeVector_add_right._proof_1_3

```lean
∀ {ι : Type u_1} (P a b : ι → ℕ) (p : ι),
  Eq.{1} (P p) 0 ∨ Eq.{1} (a p) 0 →
    Eq.{1} (P p) 0 ∨ Eq.{1} (b p) 0 → ¬(Eq.{1} (P p) 0 ∨ Eq.{1} (HAdd.hAdd.{0, 0, 0} (a p) (b p)) 0) → False
```

## HeckeSkeleton.LowHybrid.Factorization.cubicColumn_decomposition._proof_1_1

```lean
∀ {ι : Type u_1} (n b r c' : ι → ℕ) (p : ι),
  Eq.{1} (n p)
      (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.commonExp (n p) (b p))
        (HeckeSkeleton.LowHybrid.Factorization.leftExp (n p) (b p))) →
    Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.commonExp (n p) (b p)) (HAdd.hAdd.{0, 0, 0} (r p) (c' p)) →
      ¬Eq.{1} (n p)
            (HAdd.hAdd.{0, 0, 0} (r p)
              (HAdd.hAdd.{0, 0, 0} (c' p) (HeckeSkeleton.LowHybrid.Factorization.leftExp (n p) (b p)))) →
        False
```

## HeckeSkeleton.LowHybrid.Factorization.cubicColumn_factors_coprime._proof_1_1

```lean
∀ {ι : Type u_1} (n b c' : ι → ℕ) (p : ι),
  LE.le.{0} (HAdd.hAdd.{0, 0, 0} (c' p) (HeckeSkeleton.LowHybrid.Factorization.leftPart.{u_1} n b p)) 1 →
    ¬(Eq.{1} (c' p) 0 ∨ Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.leftPart.{u_1} n b p) 0) → False
```

## HeckeSkeleton.LowHybrid.Factorization.cubicColumn_squarefree._proof_1_1

```lean
∀ {ι : Type u_1} (n b r c' : ι → ℕ) (p : ι),
  Eq.{1} (n p)
      (HAdd.hAdd.{0, 0, 0} (r p)
        (HAdd.hAdd.{0, 0, 0} (c' p) (HeckeSkeleton.LowHybrid.Factorization.leftPart.{u_1} n b p))) →
    LE.le.{0} (n p) 1 →
      ¬LE.le.{0} (HAdd.hAdd.{0, 0, 0} (c' p) (HeckeSkeleton.LowHybrid.Factorization.leftPart.{u_1} n b p)) 1 → False
```

## HeckeSkeleton.LowHybrid.Factorization.cubic_mask_equivalence._proof_1_1

```lean
∀ {ι : Type u_1} (P r c h t : ι → ℕ) (p : ι),
  Eq.{1} (P p) 0 ∨
      Eq.{1}
        (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (r p) (c p)) (h p))
          (HMul.hMul.{0, 0, 0} 2 (t p)))
        0 →
    ¬(Eq.{1} (P p) 0 ∨ Eq.{1} (HAdd.hAdd.{0, 0, 0} (h p) (t p)) 0) → False
```

## HeckeSkeleton.LowHybrid.Factorization.cubic_mask_equivalence._proof_1_2

```lean
∀ {ι : Type u_1} (P r c m h t : ι → ℕ) (p : ι),
  Eq.{1} (P p) 0 ∨ Eq.{1} (HAdd.hAdd.{0, 0, 0} (h p) (t p)) 0 →
    Eq.{1} (P p) 0 ∨ Eq.{1} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (r p) (c p)) (m p)) 0 →
      ¬(Eq.{1} (P p) 0 ∨
            Eq.{1}
              (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (r p) (c p)) (h p))
                (HMul.hMul.{0, 0, 0} 2 (t p)))
              0) →
        False
```

## HeckeSkeleton.LowHybrid.Factorization.leftExp_le_one._proof_1_1

```lean
∀ (n b : ℕ),
  LE.le.{0} n 1 → ¬LE.le.{0} (HSub.hSub.{0, 0, 0} n (HeckeSkeleton.LowHybrid.Factorization.commonExp n b)) 1 → False
```

## HeckeSkeleton.LowHybrid.Factorization.left_right_disjoint._proof_1_1

```lean
∀ (n b : ℕ),
  LE.le.{0} n (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b) →
    ¬(Eq.{1} (HSub.hSub.{0, 0, 0} n n) 0 ∨
          Eq.{1} (HSub.hSub.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b) n) 0) →
      False
```

## HeckeSkeleton.LowHybrid.Factorization.left_right_disjoint._proof_1_2

```lean
∀ (n b : ℕ),
  ¬(Eq.{1} (HSub.hSub.{0, 0, 0} n (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b)) 0 ∨
        Eq.{1}
          (HSub.hSub.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b)
            (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b))
          0) →
    False
```

## HeckeSkeleton.LowHybrid.Factorization.local_factorization_unique._proof_1_3

```lean
∀ (n b g t c m h : ℕ),
  LE.le.{0} g 1 →
    Eq.{1} b (HAdd.hAdd.{0, 0, 0} g (HMul.hMul.{0, 0, 0} 2 t)) →
      Eq.{1} n (HAdd.hAdd.{0, 0, 0} c m) →
        Eq.{1} g (HAdd.hAdd.{0, 0, 0} c h) →
          Eq.{1} m 0 ∨ Eq.{1} h 0 →
            LE.le.{0} n (HMod.hMod.{0, 0, 0} b 2) →
              ¬(Eq.{1} g (HMod.hMod.{0, 0, 0} b 2) ∧
                    Eq.{1} t (HDiv.hDiv.{0, 0, 0} b 2) ∧
                      Eq.{1} c n ∧
                        Eq.{1} m (HSub.hSub.{0, 0, 0} n n) ∧
                          Eq.{1} h (HSub.hSub.{0, 0, 0} (HMod.hMod.{0, 0, 0} b 2) n)) →
                False
```

## HeckeSkeleton.LowHybrid.Factorization.local_factorization_unique._proof_1_4

```lean
∀ (n b g t c m h : ℕ),
  LE.le.{0} g 1 →
    Eq.{1} b (HAdd.hAdd.{0, 0, 0} g (HMul.hMul.{0, 0, 0} 2 t)) →
      Eq.{1} n (HAdd.hAdd.{0, 0, 0} c m) →
        Eq.{1} g (HAdd.hAdd.{0, 0, 0} c h) →
          Eq.{1} m 0 ∨ Eq.{1} h 0 →
            ¬LE.le.{0} n (HMod.hMod.{0, 0, 0} b 2) →
              ¬(Eq.{1} g (HMod.hMod.{0, 0, 0} b 2) ∧
                    Eq.{1} t (HDiv.hDiv.{0, 0, 0} b 2) ∧
                      Eq.{1} c (HMod.hMod.{0, 0, 0} b 2) ∧
                        Eq.{1} m (HSub.hSub.{0, 0, 0} n (HMod.hMod.{0, 0, 0} b 2)) ∧
                          Eq.{1} h (HSub.hSub.{0, 0, 0} (HMod.hMod.{0, 0, 0} b 2) (HMod.hMod.{0, 0, 0} b 2))) →
                False
```

## HeckeSkeleton.LowHybrid.Factorization.residual_exponent_le_one._proof_1_1

```lean
∀ (n b : ℕ),
  LE.le.{0} (HeckeSkeleton.LowHybrid.Factorization.leftExp n b) 1 →
    LE.le.{0} (HeckeSkeleton.LowHybrid.Factorization.rightExp n b) 1 →
      Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.leftExp n b) 0 ∨
          Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.rightExp n b) 0 →
        ¬LE.le.{0}
              (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.leftExp n b)
                (HeckeSkeleton.LowHybrid.Factorization.rightExp n b))
              1 →
          False
```

## HeckeSkeleton.LowHybrid.Factorization.rightExp_le_one._proof_1_1

```lean
∀ (n b : ℕ),
  LE.le.{0} (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b) 1 →
    ¬LE.le.{0}
          (HSub.hSub.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b)
            (HeckeSkeleton.LowHybrid.Factorization.commonExp n b))
          1 →
      False
```

## HeckeSkeleton.LowHybrid.Factorization.split_left._proof_1_1

```lean
∀ (n b : ℕ),
  LE.le.{0} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b) n →
    ¬Eq.{1} n
          (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b)
            (HSub.hSub.{0, 0, 0} n (HeckeSkeleton.LowHybrid.Factorization.commonExp n b))) →
      False
```

## HeckeSkeleton.LowHybrid.Factorization.split_right._proof_1_1

```lean
∀ (n b : ℕ),
  LE.le.{0} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b)
      (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b) →
    ¬Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b)
          (HAdd.hAdd.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.commonExp n b)
            (HSub.hSub.{0, 0, 0} (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b)
              (HeckeSkeleton.LowHybrid.Factorization.commonExp n b))) →
      False
```

## HeckeSkeleton.LowHybrid.Factorization.square_extraction._proof_1_1

```lean
∀ (b : ℕ),
  ¬Eq.{1} b (HAdd.hAdd.{0, 0, 0} (HMod.hMod.{0, 0, 0} b 2) (HMul.hMul.{0, 0, 0} 2 (HDiv.hDiv.{0, 0, 0} b 2))) → False
```

## HeckeSkeleton.LowHybrid.Factorization.squarefreeExp.eq_1

```lean
∀ (b : ℕ), Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp b) (HMod.hMod.{0, 0, 0} b 2)
```

## HeckeSkeleton.LowHybrid.Factorization.squarefreeExp_le_one._proof_1_1

```lean
∀ (b : ℕ), ¬LE.le.{0} (HMod.hMod.{0, 0, 0} b 2) 1 → False
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockA_mass_le

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I),
  (∀ (x : I), LE.le.{0} 1 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S x)) →
    ∀ (a : I → ℂ) (marks : Finset.{u_1} I) (d r t h : I),
      LE.le.{0}
        (∑ p ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.markQuotients.{u_1} S marks d,
          HPow.hPow.{0, 0, 0} (Norm.norm.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockA.{u_1} S a d r t h p))
            2)
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.columnMass.{u_1} S a marks d)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockBeta_budget

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  {columns cubes : Finset.{u_1} I} (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes),
  (∀ (x : I), LE.le.{0} 1 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S x)) →
    ∀ (beta : I → I → ℂ),
      (∀ (n : I),
          Membership.mem.{u_1, u_1} columns n →
            ∀ (b : I), Membership.mem.{u_1, u_1} cubes b → LE.le.{0} (Norm.norm.{0} (beta n b)) 1) →
        ∀ (B : ℝ),
          LE.le.{0} 0 B →
            (∀ (b : I),
                Membership.mem.{u_1, u_1} cubes b →
                  LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S b) B) →
              ∀ (d r t c m h : I),
                LE.le.{0}
                  (HMul.hMul.{0, 0, 0}
                    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S t)
                      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S c))
                    (HPow.hPow.{0, 0, 0}
                      (Norm.norm.{0}
                        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockBeta.{u_1} S beta
                          (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) d r t c m h))
                      2))
                  (HDiv.hDiv.{0, 0, 0}
                    (HDiv.hDiv.{0, 0, 0} B (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S r))
                    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S t)
                      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S h)))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockBeta_column_support

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  {columns cubes : Finset.{u_1} I} (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes)
  (beta : I → I → ℂ) (N : ℝ),
  (∀ (n : I),
      Membership.mem.{u_1, u_1} columns n →
        LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S n) N) →
    ∀ (d r t c m h : I),
      Ne.{1}
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockBeta.{u_1} S beta
            (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) d r t c m h)
          0 →
        LE.le.{0}
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S r)
              (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S c))
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S m))
          N
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockBeta_cube_support

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  {columns cubes : Finset.{u_1} I} (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes)
  (beta : I → I → ℂ) (B : ℝ),
  (∀ (b : I),
      Membership.mem.{u_1, u_1} cubes b → LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S b) B) →
    ∀ (d r t c m h : I),
      Ne.{1}
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockBeta.{u_1} S beta
            (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) d r t c m h)
          0 →
        LE.le.{0}
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S r)
                (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S c))
              (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S h))
            (HPow.hPow.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S t) 2))
          B
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockBeta_ne_zero_mem

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (beta : I → I → ℂ) (support : Finset.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I))
  (d r t c m h : I),
  Ne.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockBeta.{u_1} S beta support d r t c m h) 0 →
    Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_1} S support r)
      (Prod.mk.{u_1, u_1} t (Prod.mk.{u_1, u_1} c (Prod.mk.{u_1, u_1} m h)))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockBeta_ne_zero_original_mem

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  {columns cubes : Finset.{u_1} I} (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes)
  (beta : I → I → ℂ) (d r t c m h : I),
  Ne.{1}
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockBeta.{u_1} S beta
        (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) d r t c m h)
      0 →
    Membership.mem.{u_1, u_1} columns (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} r c) m) ∧
      Membership.mem.{u_1, u_1} cubes
        (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} r c) h)
          (HPow.hPow.{u_1, 0, u_1} t 2))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockRowBox_eq_zero

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (beta : I → I → ℂ) (marks : Finset.{u_1} I)
  (support : Finset.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I)) (ts cs ms hs : Finset.{u_1} I)
  (goodPairs goodMC : Finset.{u_1} (Prod.{u_1, u_1} I I)) (d r k : I),
  (∀ (v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I),
      Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_1} S support r) v →
        Membership.mem.{u_1, u_1} goodPairs (Prod.mk.{u_1, u_1} v.2.2.1 v.2.2.2)) →
    (∀ (v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I),
        Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_1} S support r) v →
          Membership.mem.{u_1, u_1} goodMC (Prod.mk.{u_1, u_1} v.2.2.1 v.2.1)) →
      Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockRowBox.{u_1} S a beta marks support ts cs ms hs d r k)
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockRowZero.{u_1} S a beta marks support ts cs ms hs goodPairs
          goodMC d r k)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockRowSupport_eq_box

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (beta : I → I → ℂ) (marks : Finset.{u_1} I)
  (support : Finset.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I)) (ts cs ms hs : Finset.{u_1} I)
  (d r k : I),
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_1} S support r ⊆
      HeckeSkeleton.LowHybrid.NormalForm.completedBox.{u_1} ts cs ms hs →
    Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockRowSupport.{u_1} S a beta marks support d r k)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockRowBox.{u_1} S a beta marks support ts cs ms hs d r k)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport_original_mem

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  {columns cubes : Finset.{u_1} I} (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes) {r : I}
  {v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I},
  Membership.mem.{u_1, u_1}
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_1} S
        (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) r)
      v →
    Membership.mem.{u_1, u_1} columns (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} r v.2.1) v.2.2.1) ∧
      Membership.mem.{u_1, u_1} cubes
        (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} r v.2.1) v.2.2.2)
          (HPow.hPow.{u_1, 0, u_1} v.1 2))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport_restore_mem

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  {support : Finset.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I)} {r : I}
  {v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I},
  Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_1} S support r) v →
    Membership.mem.{u_1, u_1} support (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.restoreCommon.{u_1} S r v)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.card_divisorPairs

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (k : I),
  Eq.{1} (Finset.card.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisorPairs.{u_1} S k))
    (∑ d ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k,
      Finset.card.{u_1}
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S d k)))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.columnMass_div_eq

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (marks : Finset.{u_1} I) (d : I),
  Eq.{1}
    (HDiv.hDiv.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.columnMass.{u_1} S a marks d)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S d))
    (∑ p ∈ marks with Dvd.dvd.{u_1} d p,
      HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a p)) 2)
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S p))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.columnMass_nonneg

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (marks : Finset.{u_1} I) (d : I),
  LE.le.{0} 0 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.columnMass.{u_1} S a marks d)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.columnMass_sum_le_divisors

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (marks ds : Finset.{u_1} I) (D : ℝ),
  (∀ (p : I),
      Membership.mem.{u_1, u_1} marks p →
        ∀ (d : I),
          Dvd.dvd.{u_1} d p →
            Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S p) d) →
    (∀ (p : I),
        Membership.mem.{u_1, u_1} marks p →
          LE.le.{0} (↑(Finset.card.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S p))) D) →
      LE.le.{0}
        (∑ d ∈ ds,
          HDiv.hDiv.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.columnMass.{u_1} S a marks d)
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S d))
        (HMul.hMul.{0, 0, 0} D
          (∑ p ∈ marks,
            HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a p)) 2)
              (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S p)))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.completed_column_norm

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (r c m : I),
  Eq.{1}
    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S
      (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} r c) m))
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S r)
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S c))
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S m))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.completed_cube_norm

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (r t c h : I),
  Eq.{1}
    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S
      (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} r c) h)
        (HPow.hPow.{u_1, 0, u_1} t 2)))
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0}
        (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S r)
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S c))
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S h))
      (HPow.hPow.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S t) 2))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.completed_cubic

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (p r t c m h : I),
  Eq.{1}
    (HMul.hMul.{0, 0, 0}
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S p
        (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} r c) m))
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S p
        (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} r c) h)
          (HPow.hPow.{u_1, 0, u_1} t 2))))
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S p r)
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S p (HMul.hMul.{u_1, u_1, u_1} c m)))
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S p (HMul.hMul.{u_1, u_1, u_1} h t)))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.completed_quadratic

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (k t c m h : I),
  Eq.{1}
    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.{u_1} S k
      (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} c m)
        (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} c h) (HPow.hPow.{u_1, 0, u_1} t 2))))
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0}
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.{u_1} S k (HMul.hMul.{u_1, u_1, u_1} m h))
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S k c))
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S k t))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop_mul_left

```lean
∀ {I : Type u_2} [inst : CommMonoid.{u_2} I] (self : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} I)
  (x y z : I),
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_2} self (HMul.hMul.{u_2, u_2, u_2} x y) z ↔
    HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_2} self x z ∧
      HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_2} self y z
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop_mul_right

```lean
∀ {I : Type u_2} [inst : CommMonoid.{u_2} I] (self : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} I)
  (x y z : I),
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_2} self x (HMul.hMul.{u_2, u_2, u_2} y z) ↔
    HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_2} self x y ∧
      HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_2} self x z
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop_symm

```lean
∀ {I : Type u_2} [inst : CommMonoid.{u_2} I] (self : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} I)
  (x y : I),
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_2} self x y ↔
    HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_2} self y x
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic_mask

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (x y : I),
  Eq.{1}
    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S x y)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S x y))
    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S x y)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic_mul_left

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (x y z : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S (HMul.hMul.{u_1, u_1, u_1} x y) z)
    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S x z)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S y z))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic_mul_right

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (x y z : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S x (HMul.hMul.{u_1, u_1, u_1} y z))
    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S x y)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S x z))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisorPairs_disjoint

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (k : I),
  Set.PairwiseDisjoint.{u_1, u_1} ↑(HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k) fun d =>
    Finset.image.{u_1, u_1} (fun r => Prod.mk.{u_1, u_1} d r)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S d k))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisor_dvd

```lean
∀ {I : Type u_2} [inst : CommMonoid.{u_2} I] (self : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} I)
  (x d : I),
  Membership.mem.{u_2, u_2} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_2} self x) d → Dvd.dvd.{u_2} d x
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.firstColumn_completed

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (marks : Finset.{u_1} I) (d r t c m h : I),
  Eq.{1}
    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.firstColumn.{u_1} S a marks d
      (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} r c) m)
      (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} r c) h)
        (HPow.hPow.{u_1, 0, u_1} t 2)))
    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockColumn.{u_1} S a marks d r t c m h)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.firstRow_completed

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (beta : I → I → ℂ) (marks columns cubes : Finset.{u_1} I)
  (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes) (d k : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.firstRow.{u_1} S a beta marks columns cubes d k)
    (∑ v ∈ HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C,
      HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S k v.2.1)
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S k v.1)
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.{u_1} S k
              (HMul.hMul.{u_1, u_1, u_1} v.2.2.1 v.2.2.2)))
          (HMul.hMul.{0, 0, 0}
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.firstBeta.{u_1} S beta d
              (HeckeSkeleton.LowHybrid.NormalForm.recombine.{u_1} v).1
              (HeckeSkeleton.LowHybrid.NormalForm.recombine.{u_1} v).2)
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.firstColumn.{u_1} S a marks d
              (HeckeSkeleton.LowHybrid.NormalForm.recombine.{u_1} v).1
              (HeckeSkeleton.LowHybrid.NormalForm.recombine.{u_1} v).2))))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.firstRow_second_expansion

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (beta : I → I → ℂ) (marks columns cubes : Finset.{u_1} I)
  (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes) (d k : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.firstRow.{u_1} S a beta marks columns cubes d k)
    (∑ r ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k,
      HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mu.{u_1} S r)
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockRowSupport.{u_1} S a beta marks
          (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) d r k))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.first_divisor_column_sum

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (beta : I → I → ℂ) (marks columns cubes : Finset.{u_1} I) (d k : I),
  Eq.{1}
    (∑ p ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.markQuotients.{u_1} S marks d,
      HMul.hMul.{0, 0, 0}
        (HDiv.hDiv.{0, 0, 0} (a (HMul.hMul.{u_1, u_1, u_1} d p))
          ↑√(HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S (HMul.hMul.{u_1, u_1, u_1} d p)))
        (∑ n ∈ columns,
          ∑ b ∈ cubes,
            HMul.hMul.{0, 0, 0} (beta n b)
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0}
                  (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.{u_1} S (HMul.hMul.{u_1, u_1, u_1} d k)
                    (HMul.hMul.{u_1, u_1, u_1} n b))
                  (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S (HMul.hMul.{u_1, u_1, u_1} d p) n))
                (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S (HMul.hMul.{u_1, u_1, u_1} d p) b))))
    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.weight.{u_1} S d)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.firstRow.{u_1} S a beta marks columns cubes d k))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.first_divisor_summand

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (beta : I → I → ℂ) (d k p n b : I),
  Eq.{1}
    (HMul.hMul.{0, 0, 0}
      (HDiv.hDiv.{0, 0, 0} (a (HMul.hMul.{u_1, u_1, u_1} d p))
        ↑√(HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S (HMul.hMul.{u_1, u_1, u_1} d p)))
      (HMul.hMul.{0, 0, 0} (beta n b)
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0}
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.{u_1} S (HMul.hMul.{u_1, u_1, u_1} d k)
              (HMul.hMul.{u_1, u_1, u_1} n b))
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S (HMul.hMul.{u_1, u_1, u_1} d p) n))
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S (HMul.hMul.{u_1, u_1, u_1} d p) b))))
    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.weight.{u_1} S d)
      (HMul.hMul.{0, 0, 0}
        (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.firstBeta.{u_1} S beta d n b)
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.{u_1} S k (HMul.hMul.{u_1, u_1, u_1} n b)))
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0}
            (HDiv.hDiv.{0, 0, 0} (a (HMul.hMul.{u_1, u_1, u_1} d p))
              ↑√(HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S p))
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S p n))
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S p b))))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.hybridEnergy_finite_bound

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (sf : I → Prop),
  (∀ (x : I), LE.le.{0} 1 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S x)) →
    (∀ (x : I), LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mu.{u_1} S x)) 1) →
      HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S) sf
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_1} S) →
        HeckeSkeleton.LowHybrid.CubicSieveInput.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S) sf
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_1} S) →
          ∀ (eta : ℝ),
            LT.lt.{0} 0 eta →
              ∃ C0,
                LT.lt.{0} 0 C0 ∧
                  ∀ (K Y N L : ℝ),
                    LE.le.{0} 1 K →
                      LE.le.{0} 1 Y →
                        LE.le.{0} 1 N →
                          LE.le.{0} 1 L →
                            ∀ (rows marks columns cubes ds rs : Finset.{u_1} I)
                              (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes)
                              (ts cs ms hs : I → I → Finset.{u_1} I)
                              (goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I))
                              (qset jset : Finset.{u_1} I) (a : I → ℂ) (beta : I → I → ℂ) (B Delta Dq Dc Ht Hc Hh : ℝ),
                              LE.le.{0} 0 B →
                                LE.le.{0} 0 Delta →
                                  LE.le.{0} 0 Dq →
                                    LE.le.{0} 0 Dc →
                                      LE.le.{0} 0 Ht →
                                        LE.le.{0} 0 Hc →
                                          LE.le.{0} 0 Hh →
                                            (∀ (n : I),
                                                Membership.mem.{u_1, u_1} columns n →
                                                  ∀ (b : I),
                                                    Membership.mem.{u_1, u_1} cubes b →
                                                      LE.le.{0} (Norm.norm.{0} (beta n b)) 1) →
                                              (∀ (b : I),
                                                  Membership.mem.{u_1, u_1} cubes b →
                                                    LE.le.{0}
                                                      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S b)
                                                      B) →
                                                HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf
                                                    rows marks columns cubes ds rs C ts cs ms hs goodPairs goodMC qset
                                                    jset K Y N L Delta Dq Dc Ht Hc Hh →
                                                  LE.le.{0}
                                                    (HeckeSkeleton.LowHybrid.hybridEnergy.{u_1}
                                                      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_1} S)
                                                      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_1} S)
                                                      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S) a
                                                      beta rows marks columns cubes)
                                                    (HMul.hMul.{0, 0, 0}
                                                      (HMul.hMul.{0, 0, 0}
                                                        (HMul.hMul.{0, 0, 0}
                                                          (HMul.hMul.{0, 0, 0}
                                                            (HMul.hMul.{0, 0, 0}
                                                              (HMul.hMul.{0, 0, 0}
                                                                (HMul.hMul.{0, 0, 0}
                                                                  (HMul.hMul.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0}
                                                                      (HMul.hMul.{0, 0, 0}
                                                                        (HMul.hMul.{0, 0, 0}
                                                                          (HMul.hMul.{0, 0, 0} C0 Delta) Dq)
                                                                        Dc)
                                                                      (HPow.hPow.{0, 0, 0}
                                                                        (HMul.hMul.{0, 0, 0}
                                                                          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K Y)
                                                                            N)
                                                                          L)
                                                                        eta))
                                                                    (HAdd.hAdd.{0, 0, 0} K Y))
                                                                  B)
                                                                (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} N L)
                                                                  (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} N L)
                                                                    (2 / 3))))
                                                              (HPow.hPow.{0, 0, 0} Ht 2))
                                                            Hc)
                                                          Hh)
                                                        (∑ d ∈ ds,
                                                          HDiv.hDiv.{0, 0, 0}
                                                            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.columnMass.{u_1}
                                                              S a marks d)
                                                            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S
                                                              d)))
                                                      (∑ r ∈ rs,
                                                        HDiv.hDiv.{0, 0, 0} 1
                                                          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S
                                                            r)))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.hybridRow_eq_weightedBlocks

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (beta : I → I → ℂ) (marks columns cubes : Finset.{u_1} I)
  (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes) (ts cs ms hs : I → I → Finset.{u_1} I)
  (goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)) (k : I),
  (∀ (d : I),
      Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k) d →
        ∀ (r : I),
          Membership.mem.{u_1, u_1}
              (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S
                (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S d k))
              r →
            HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_1} S
                (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) r ⊆
              HeckeSkeleton.LowHybrid.NormalForm.completedBox.{u_1} (ts d r) (cs d r) (ms d r) (hs d r)) →
    (∀ (d : I),
        Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k) d →
          ∀ (r : I),
            Membership.mem.{u_1, u_1}
                (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S
                  (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S d k))
                r →
              ∀ (v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I),
                Membership.mem.{u_1, u_1}
                    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_1} S
                      (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) r)
                    v →
                  Membership.mem.{u_1, u_1} (goodPairs d r) (Prod.mk.{u_1, u_1} v.2.2.1 v.2.2.2)) →
      (∀ (d : I),
          Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k) d →
            ∀ (r : I),
              Membership.mem.{u_1, u_1}
                  (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S
                    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S d k))
                  r →
                ∀ (v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I),
                  Membership.mem.{u_1, u_1}
                      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_1} S
                        (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) r)
                      v →
                    Membership.mem.{u_1, u_1} (goodMC d r) (Prod.mk.{u_1, u_1} v.2.2.1 v.2.1)) →
        Eq.{1}
          (HeckeSkeleton.LowHybrid.hybridRow.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_1} S)
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_1} S)
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S) a beta marks columns cubes k)
          (∑ dr ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisorPairs.{u_1} S k,
            HMul.hMul.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mu.{u_1} S dr.1)
                (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mu.{u_1} S dr.2))
              (HMul.hMul.{0, 0, 0}
                (HDiv.hDiv.{0, 0, 0} 1 ↑√(HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S dr.1))
                (HeckeSkeleton.LowHybrid.WeightedBlock.row.{u_1, u_1}
                  (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.weightedBlock.{u_1} S a beta marks
                    (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) (ts dr.1 dr.2) (cs dr.1 dr.2)
                    (ms dr.1 dr.2) (hs dr.1 dr.2) (goodPairs dr.1 dr.2) (goodMC dr.1 dr.2) dr.1 dr.2)
                  k)))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.hybridRow_first_expansion

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (beta : I → I → ℂ) (marks columns cubes : Finset.{u_1} I) (k : I),
  Eq.{1}
    (HeckeSkeleton.LowHybrid.hybridRow.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_1} S)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_1} S)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S) a beta marks columns cubes k)
    (∑ d ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k,
      HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mu.{u_1} S d)
        (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.weight.{u_1} S d)
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.firstRow.{u_1} S a beta marks columns cubes d
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S d k))))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.hybridRow_normal_form

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (beta : I → I → ℂ) (marks columns cubes : Finset.{u_1} I)
  (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes) (k : I),
  Eq.{1}
    (HeckeSkeleton.LowHybrid.hybridRow.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_1} S)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_1} S)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S) a beta marks columns cubes k)
    (∑ d ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k,
      ∑
        r ∈
          HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S d k),
        HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mu.{u_1} S d)
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mu.{u_1} S r))
          (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.weight.{u_1} S d)
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockRowSupport.{u_1} S a beta marks
              (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) d r
              (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S d k))))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.hybrid_energy_of_finite_inputs

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (sf : I → Prop),
  (∀ (x : I), LE.le.{0} 1 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S x)) →
    (∀ (x : I), LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mu.{u_1} S x)) 1) →
      HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S) sf
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_1} S) →
        HeckeSkeleton.LowHybrid.CubicSieveInput.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S) sf
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_1} S) →
          ∀ (divisor harmonic : ℝ → ℝ),
            (∀ (X : ℝ), LE.le.{0} 1 X → LE.le.{0} 0 (divisor X)) →
              (∀ (X : ℝ), LE.le.{0} 1 X → LE.le.{0} 0 (harmonic X)) →
                HeckeSkeleton.LowHybrid.SubpowerBound divisor →
                  HeckeSkeleton.LowHybrid.SubpowerBound harmonic →
                    ∀ (eps : ℝ),
                      LT.lt.{0} 0 eps →
                        ∃ C0,
                          LT.lt.{0} 0 C0 ∧
                            ∀ (K N B L : ℝ),
                              LE.le.{0} 1 K →
                                LE.le.{0} 1 N →
                                  LE.le.{0} 1 B →
                                    LE.le.{0} 1 L →
                                      ∀ (rows marks columns cubes ds rs : Finset.{u_1} I)
                                        (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes)
                                        (ts cs ms hs : I → I → Finset.{u_1} I)
                                        (goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I))
                                        (qset jset : Finset.{u_1} I) (a : I → ℂ) (beta : I → I → ℂ),
                                        (∀ (n : I),
                                            Membership.mem.{u_1, u_1} columns n →
                                              ∀ (b : I),
                                                Membership.mem.{u_1, u_1} cubes b →
                                                  LE.le.{0} (Norm.norm.{0} (beta n b)) 1) →
                                          (∀ (b : I),
                                              Membership.mem.{u_1, u_1} cubes b →
                                                LE.le.{0}
                                                  (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S b) B) →
                                            HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows
                                                marks columns cubes ds rs C ts cs ms hs goodPairs goodMC qset jset K
                                                (HMul.hMul.{0, 0, 0} N B) N L (HPow.hPow.{0, 0, 0} (divisor K) 2)
                                                (divisor (HMul.hMul.{0, 0, 0} N B)) (divisor N) (harmonic B)
                                                (harmonic N) (harmonic B) →
                                              LE.le.{0}
                                                  (∑ d ∈ ds,
                                                    HDiv.hDiv.{0, 0, 0}
                                                      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.columnMass.{u_1} S
                                                        a marks d)
                                                      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S d))
                                                  (HMul.hMul.{0, 0, 0} (divisor L)
                                                    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.originalColumnMass.{u_1}
                                                      S a marks)) →
                                                LE.le.{0}
                                                    (∑ r ∈ rs,
                                                      HDiv.hDiv.{0, 0, 0} 1
                                                        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S r))
                                                    (harmonic K) →
                                                  LE.le.{0}
                                                    (HeckeSkeleton.LowHybrid.hybridEnergy.{u_1}
                                                      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_1} S)
                                                      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_1} S)
                                                      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S) a
                                                      beta rows marks columns cubes)
                                                    (HMul.hMul.{0, 0, 0}
                                                      (HMul.hMul.{0, 0, 0}
                                                        (HMul.hMul.{0, 0, 0}
                                                          (HMul.hMul.{0, 0, 0}
                                                            (HMul.hMul.{0, 0, 0} C0
                                                              (HPow.hPow.{0, 0, 0}
                                                                (HMul.hMul.{0, 0, 0}
                                                                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} K N) B) L)
                                                                eps))
                                                            (HAdd.hAdd.{0, 0, 0} K (HMul.hMul.{0, 0, 0} N B)))
                                                          B)
                                                        (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} N L)
                                                          (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} N L) (2 / 3))))
                                                      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.originalColumnMass.{u_1}
                                                        S a marks))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.markQuotients_mul_mem

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  {marks : Finset.{u_1} I} {d p : I},
  Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.markQuotients.{u_1} S marks d) p →
    Membership.mem.{u_1, u_1} marks (HMul.hMul.{u_1, u_1, u_1} d p)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask_common_expansion

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (support : Finset.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I)) (k : I)
  (F : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I → ℂ),
  Eq.{1} (∑ v ∈ support, HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S k v.2.1) (F v))
    (∑ r ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k,
      HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mu.{u_1} S r)
        (∑ v ∈ support with Dvd.dvd.{u_1} r v.2.1, F v))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask_mul_left

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (x y z : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S (HMul.hMul.{u_1, u_1, u_1} x y) z)
    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S x z)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S y z))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask_mul_right

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (x y z : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S x (HMul.hMul.{u_1, u_1, u_1} y z))
    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S x y)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S x z))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask_square

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (x y : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S x (HPow.hPow.{u_1, 0, u_1} y 2))
    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S x y)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask_sum_expansion

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (marks : Finset.{u_1} I) (k : I) (F : I → ℂ),
  Eq.{1} (∑ p ∈ marks, HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S p k) (F p))
    (∑ d ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k,
      HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mu.{u_1} S d)
        (∑ p ∈ marks with Dvd.dvd.{u_1} d p, F p))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask_symm

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (x y : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S x y)
    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S y x)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mem_divisorPairs

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (k d r : I),
  Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisorPairs.{u_1} S k)
      (Prod.mk.{u_1, u_1} d r) ↔
    Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k) d ∧
      Membership.mem.{u_1, u_1}
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S d k))
        r
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mobius_expansion

```lean
∀ {I : Type u_2} [inst : CommMonoid.{u_2} I] (self : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} I)
  (p k : I),
  Eq.{1} (ite.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_2} self p k) 1 0)
    (∑ d ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_2} self k,
      ite.{1} (Dvd.dvd.{u_2} d p) (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mu.{u_2} self d) 0)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.norm_blockBetaCore_le

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (beta : I → I → ℂ) (d r t c m h : I),
  LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockBetaCore.{u_1} S beta d r t c m h))
    (Norm.norm.{0}
      (beta (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} r c) m)
        (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} r c) h)
          (HPow.hPow.{u_1, 0, u_1} t 2))))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.norm_blockBeta_le_one

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  {columns cubes : Finset.{u_1} I} (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes)
  (beta : I → I → ℂ),
  (∀ (n : I),
      Membership.mem.{u_1, u_1} columns n →
        ∀ (b : I), Membership.mem.{u_1, u_1} cubes b → LE.le.{0} (Norm.norm.{0} (beta n b)) 1) →
    ∀ (d r t c m h : I),
      LE.le.{0}
        (Norm.norm.{0}
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockBeta.{u_1} S beta
            (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) d r t c m h))
        1
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.norm_cubic_le_one

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (x y : I),
  LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S x y)) 1
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.norm_firstBeta_le

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (beta : I → I → ℂ) (d n b : I),
  LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.firstBeta.{u_1} S beta d n b))
    (Norm.norm.{0} (beta n b))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.norm_mask_le_one

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (x y : I),
  LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S x y)) 1
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.norm_mul

```lean
∀ {I : Type u_2} [inst : CommMonoid.{u_2} I] (self : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} I)
  (x y : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} self (HMul.hMul.{u_2, u_2, u_2} x y))
    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} self x)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} self y))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.norm_nonneg

```lean
∀ {I : Type u_2} [inst : CommMonoid.{u_2} I] (self : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} I)
  (x : I), LE.le.{0} 0 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_2} self x)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.norm_quadratic_le_one

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (x y : I),
  LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.{u_1} S x y)) 1
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normalization_mul

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (d p : I)
  (a : ℂ),
  Eq.{1}
    (HDiv.hDiv.{0, 0, 0} a
      ↑√(HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S (HMul.hMul.{u_1, u_1, u_1} d p)))
    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.weight.{u_1} S d)
      (HDiv.hDiv.{0, 0, 0} a ↑√(HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S p)))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.originalColumnMass_nonneg

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (marks : Finset.{u_1} I),
  LE.le.{0} 0 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.originalColumnMass.{u_1} S a marks)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic_mul_left

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (x y z : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.{u_1} S (HMul.hMul.{u_1, u_1, u_1} x y) z)
    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.{u_1} S x z)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.{u_1} S y z))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic_mul_right

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (x y z : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.{u_1} S x (HMul.hMul.{u_1, u_1, u_1} y z))
    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.{u_1} S x y)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.{u_1} S x z))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic_square

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (x y : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.{u_1} S x (HPow.hPow.{u_1, 0, u_1} y 2))
    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S x y)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotientTwice_injOn

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (rows : Finset.{u_1} I) (d r : I),
  (∀ (k : I),
      Membership.mem.{u_1, u_1} rows k →
        Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k) d ∧
          Membership.mem.{u_1, u_1}
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S
              (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S d k))
            r) →
    Set.InjOn.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotientTwice.{u_1} S d r) ↑rows
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotientTwice_reconstruct

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (d r k : I),
  Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k) d →
    Membership.mem.{u_1, u_1}
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S d k))
        r →
      Eq.{u_1 + 1}
        (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} d r)
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotientTwice.{u_1} S d r k))
        k
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient_spec

```lean
∀ {I : Type u_2} [inst : CommMonoid.{u_2} I] (self : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} I)
  (d x : I),
  Dvd.dvd.{u_2} d x →
    Eq.{u_2 + 1} (HMul.hMul.{u_2, u_2, u_2} d (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_2} self d x)) x
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.restore_quotient_common

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (r : I)
  (v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I),
  Dvd.dvd.{u_1} r v.2.1 →
    Eq.{u_1 + 1}
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.restoreCommon.{u_1} S r
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotientCommon.{u_1} S r v))
      v
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.six

```lean
∀ {I : Type u_2} [inst : CommMonoid.{u_2} I] (self : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} I)
  (x y : I),
  Eq.{1} (HPow.hPow.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_2} self x y) 6)
    (ite.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_2} self x y) 1 0)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.sum_common_reindex

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (support : Finset.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I)) (r : I)
  (F : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I → ℂ),
  Eq.{1} (∑ v ∈ support with Dvd.dvd.{u_1} r v.2.1, F v)
    (∑ v ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_1} S support r,
      F (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.restoreCommon.{u_1} S r v))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.sum_divisorPairs

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (k : I)
  (F : Prod.{u_1, u_1} I I → ℂ),
  Eq.{1} (∑ dr ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisorPairs.{u_1} S k, F dr)
    (∑ d ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k,
      ∑
        r ∈
          HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S
            (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S d k),
        F (Prod.mk.{u_1, u_1} d r))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.sum_divisor_reindex

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (marks : Finset.{u_1} I) (d : I) (F : I → ℂ),
  Eq.{1} (∑ p ∈ marks with Dvd.dvd.{u_1} d p, F p)
    (∑ p ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.markQuotients.{u_1} S marks d,
      F (HMul.hMul.{u_1, u_1, u_1} d p))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol_mul_left

```lean
∀ {I : Type u_2} [inst : CommMonoid.{u_2} I] (self : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} I)
  (x y z : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_2} self (HMul.hMul.{u_2, u_2, u_2} x y) z)
    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_2} self x z)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_2} self y z))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol_mul_right

```lean
∀ {I : Type u_2} [inst : CommMonoid.{u_2} I] (self : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_2} I)
  (x y z : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_2} self x (HMul.hMul.{u_2, u_2, u_2} y z))
    (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_2} self x y)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_2} self x z))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol_zero

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (x y : I),
  ¬HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_1} S x y →
    Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_1} S x y) 0
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.weightedBlock_admissible_from_sieves

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (sf : I → Prop),
  (∀ (x : I), LE.le.{0} 1 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S x)) →
    HeckeSkeleton.LowHybrid.QuadraticSieveInput.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S) sf
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_1} S) →
      HeckeSkeleton.LowHybrid.CubicSieveInput.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S) sf
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_1} S) →
        ∀ (eta : ℝ),
          LT.lt.{0} 0 eta →
            ∃ Cq Cc,
              LT.lt.{0} 0 Cq ∧
                LT.lt.{0} 0 Cc ∧
                  ∀ (K Y N L : ℝ),
                    LE.le.{0} 1 K →
                      LE.le.{0} 1 Y →
                        LE.le.{0} 1 N →
                          LE.le.{0} 1 L →
                            ∀ (rows marks columns cubes ts cs ms hs qset jset : Finset.{u_1} I)
                              (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes)
                              (goodPairs goodMC : Finset.{u_1} (Prod.{u_1, u_1} I I)) (a : I → ℂ) (beta : I → I → ℂ)
                              (d r : I) (B Dq Dc : ℝ),
                              LE.le.{0} 0 B →
                                LE.le.{0} 0 Dq →
                                  LE.le.{0} 0 Dc →
                                    (∀ (k : I),
                                        Membership.mem.{u_1, u_1} rows k →
                                          Membership.mem.{u_1, u_1}
                                              (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k) d ∧
                                            Membership.mem.{u_1, u_1}
                                              (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S
                                                (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S d k))
                                              r) →
                                      (∀ (k : I),
                                          Membership.mem.{u_1, u_1} rows k →
                                            sf
                                                (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotientTwice.{u_1} S d r
                                                  k) ∧
                                              LE.le.{0}
                                                (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S
                                                  (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotientTwice.{u_1} S d
                                                    r k))
                                                K) →
                                        (∀ (j : I),
                                            Membership.mem.{u_1, u_1} qset j →
                                              sf j ∧
                                                LE.le.{0}
                                                  (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S j) Y) →
                                          (∀ (j : I),
                                              Membership.mem.{u_1, u_1} jset j →
                                                sf j ∧
                                                  LE.le.{0}
                                                    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S j) N) →
                                            (∀ (p : I),
                                                Membership.mem.{u_1, u_1}
                                                    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.markQuotients.{u_1} S
                                                      marks d)
                                                    p →
                                                  sf p ∧
                                                    LE.le.{0}
                                                      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S p)
                                                      L) →
                                              goodPairs ⊆ SProd.sprod.{u_1, u_1, u_1} ms hs →
                                                goodMC ⊆ SProd.sprod.{u_1, u_1, u_1} ms cs →
                                                  (∀ (u : Prod.{u_1, u_1} I I),
                                                      Membership.mem.{u_1, u_1} goodPairs u →
                                                        Membership.mem.{u_1, u_1} qset
                                                          (HMul.hMul.{u_1, u_1, u_1} u.1 u.2)) →
                                                    (∀ (j : I),
                                                        Membership.mem.{u_1, u_1} qset j →
                                                          LE.le.{0}
                                                            (↑(Finset.card.{u_1}
                                                                ({u ∈ goodPairs |
                                                                  Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} u.1 u.2) j})))
                                                            Dq) →
                                                      (∀ (u : Prod.{u_1, u_1} I I),
                                                          Membership.mem.{u_1, u_1} goodMC u →
                                                            Membership.mem.{u_1, u_1} jset
                                                              (HMul.hMul.{u_1, u_1, u_1} u.2 u.1)) →
                                                        (∀ (j : I),
                                                            Membership.mem.{u_1, u_1} jset j →
                                                              LE.le.{0}
                                                                (↑(Finset.card.{u_1}
                                                                    ({u ∈ goodMC |
                                                                      Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} u.2 u.1)
                                                                        j})))
                                                                Dc) →
                                                          (∀ (n : I),
                                                              Membership.mem.{u_1, u_1} columns n →
                                                                ∀ (b : I),
                                                                  Membership.mem.{u_1, u_1} cubes b →
                                                                    LE.le.{0} (Norm.norm.{0} (beta n b)) 1) →
                                                            (∀ (b : I),
                                                                Membership.mem.{u_1, u_1} cubes b →
                                                                  LE.le.{0}
                                                                    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1}
                                                                      S b)
                                                                    B) →
                                                              HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.{u_1,
                                                                  u_1}
                                                                (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.weightedBlock.{u_1}
                                                                  S a beta marks
                                                                  (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1}
                                                                    C)
                                                                  ts cs ms hs goodPairs goodMC d r)
                                                                rows
                                                                (HMul.hMul.{0, 0, 0}
                                                                  (HMul.hMul.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0} Cq
                                                                      (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} K Y)
                                                                        eta))
                                                                    (HAdd.hAdd.{0, 0, 0} K Y))
                                                                  Dq)
                                                                (HMul.hMul.{0, 0, 0}
                                                                  (HMul.hMul.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0} Cc
                                                                      (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} N L)
                                                                        eta))
                                                                    (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} N L)
                                                                      (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} N L)
                                                                        (2 / 3))))
                                                                  Dc)
                                                                (HDiv.hDiv.{0, 0, 0} B
                                                                  (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1}
                                                                    S r))
                                                                (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.columnMass.{u_1}
                                                                  S a marks d)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.weightedBlock_row

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (beta : I → I → ℂ) (marks : Finset.{u_1} I)
  (support : Finset.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I)) (ts cs ms hs : Finset.{u_1} I)
  (goodPairs goodMC : Finset.{u_1} (Prod.{u_1, u_1} I I)) (d r k : I),
  Eq.{1}
    (HeckeSkeleton.LowHybrid.WeightedBlock.row.{u_1, u_1}
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.weightedBlock.{u_1} S a beta marks support ts cs ms hs goodPairs
        goodMC d r)
      k)
    (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockRowZero.{u_1} S a beta marks support ts cs ms hs goodPairs
      goodMC d r (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S d k))
```

## HeckeSkeleton.LowHybrid.NormalForm.Completion.mem_support_recombine

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {columns cubes : Finset.{u_1} I}
  (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes)
  {v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I},
  Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) v →
    Membership.mem.{u_1, u_1} (SProd.sprod.{u_1, u_1, u_1} columns cubes)
      (HeckeSkeleton.LowHybrid.NormalForm.recombine.{u_1} v)
```

## HeckeSkeleton.LowHybrid.NormalForm.Completion.reconstruct

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {columns cubes : Finset.{u_1} I}
  (self : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes) (x : Prod.{u_1, u_1} I I),
  Membership.mem.{u_1, u_1} (SProd.sprod.{u_1, u_1, u_1} columns cubes) x →
    Eq.{u_1 + 1}
      (HeckeSkeleton.LowHybrid.NormalForm.recombine.{u_1}
        (HeckeSkeleton.LowHybrid.NormalForm.Completion.split.{u_1} self x))
      x
```

## HeckeSkeleton.LowHybrid.NormalForm.Completion.split_injective_on

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {columns cubes : Finset.{u_1} I}
  (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes),
  Set.InjOn.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Completion.split.{u_1} C)
    ↑(SProd.sprod.{u_1, u_1, u_1} columns cubes)
```

## HeckeSkeleton.LowHybrid.NormalForm.Completion.sum_reindex

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {columns cubes : Finset.{u_1} I}
  (C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes) (F : I → I → ℂ),
  Eq.{1} (∑ n ∈ columns, ∑ b ∈ cubes, F n b)
    (∑ v ∈ HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C,
      F (HeckeSkeleton.LowHybrid.NormalForm.recombine.{u_1} v).1
        (HeckeSkeleton.LowHybrid.NormalForm.recombine.{u_1} v).2)
```

## HeckeSkeleton.LowHybrid.NormalForm.completedBox.eq_1

```lean
∀ {I : Type u_1} (ts cs ms hs : Finset.{u_1} I),
  Eq.{u_1 + 1} (HeckeSkeleton.LowHybrid.NormalForm.completedBox.{u_1} ts cs ms hs)
    (SProd.sprod.{u_1, u_1, u_1} ts (SProd.sprod.{u_1, u_1, u_1} cs (SProd.sprod.{u_1, u_1, u_1} ms hs)))
```

## HeckeSkeleton.LowHybrid.NormalForm.recombine.eq_1

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I),
  Eq.{u_1 + 1} (HeckeSkeleton.LowHybrid.NormalForm.recombine.{u_1} v)
    (Prod.mk.{u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} v.2.1 v.2.2.1)
      (HMul.hMul.{u_1, u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} v.2.1 v.2.2.2) (HPow.hPow.{u_1, 0, u_1} v.1 2)))
```

## HeckeSkeleton.LowHybrid.NormalForm.sum_zero_extend_box._simp_1_1

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred.{u_1 + 1} p] {s : Finset.{u_1} α} {a : α},
  Eq.{1} (Membership.mem.{u_1, u_1} (Finset.filter.{u_1} p s) a) (Membership.mem.{u_1, u_1} s a ∧ p a)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.arithmetic._proof_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a b c : A),
  HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords (HMul.hMul.{u_2, u_2, u_2} a b) c ↔
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords a c ∧
      HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2} coords b c
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.commonPart._proof_1

```lean
Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.commonExp 0 0) (HeckeSkeleton.LowHybrid.Factorization.commonExp 0 0)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.commonPart.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (n b : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.commonPart.{u_1, u_2} coords n b)
    (HeckeSkeleton.LowHybrid.PrimeArithmetic.mapTwo.{u_1, u_2} coords HeckeSkeleton.LowHybrid.Factorization.commonExp
      HeckeSkeleton.LowHybrid.PrimeArithmetic.commonPart._proof_1 n b)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.completedSplit_reconstruct._proof_1_4

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (n b : A) (p : ι),
  Eq.{1}
      (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp
        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p))
      (HAdd.hAdd.{0, 0, 0}
        (HeckeSkeleton.LowHybrid.Factorization.commonExp
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords n) p)
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p))
        (HeckeSkeleton.LowHybrid.Factorization.rightExp
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords n) p)
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p))) →
    Eq.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p)
        (HAdd.hAdd.{0, 0, 0}
          (HeckeSkeleton.LowHybrid.Factorization.squarefreeExp
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p))
          (HMul.hMul.{0, 0, 0} 2
            (HDiv.hDiv.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p) 2))) →
      ¬Eq.{1}
            (HAdd.hAdd.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0}
                (HeckeSkeleton.LowHybrid.Factorization.commonExp
                  ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords n) p)
                  ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p))
                (HeckeSkeleton.LowHybrid.Factorization.rightExp
                  ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords n) p)
                  ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p)))
              (HMul.hMul.{0, 0, 0} 2
                (HDiv.hDiv.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p)
                  2)))
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p) →
        False
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.dvd_iff_coordinates_le._proof_1_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a c : A) (p : ι),
  ¬LE.le.{0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p)
        (HAdd.hAdd.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p)
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords c) p)) →
    False
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.dvd_iff_coordinates_le._proof_1_2

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a b : A) (p : ι),
  LE.le.{0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p)
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p) →
    ¬Eq.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p)
          (HAdd.hAdd.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p)
            (HSub.hSub.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p)
              ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p))) →
      False
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport._proof_1

```lean
∀ {ι : Type u_1} (s : Finset.{u_1} ι) (p : ι),
  Ne.{1} (ite.{1} (Membership.mem.{u_1, u_1} s p) 1 0) 0 → Membership.mem.{u_1, u_1} s p
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (s : Finset.{u_1} ι),
  Eq.{u_2 + 1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport.{u_1, u_2} coords s)
    ((MulEquiv.symm.{u_2, u_1} coords)
      (Multiplicative.ofAdd.{u_1}
        (Finsupp.onFinset.{u_1, 0} s (fun p => ite.{1} (Membership.mem.{u_1, u_1} s p) 1 0)
          (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport._proof_1.{u_1} s))))
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport_dvd_iff._proof_1_2

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A) ⦃p : ι⦄,
  LE.le.{0} 1 ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) →
    Eq.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) 0 → False
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport_dvd_iff._proof_1_3

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A) (p : ι),
  Ne.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) 0 →
    ¬LE.le.{0} 1 ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) → False
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport_support_of_squarefree._proof_1_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) {a : A} (p : ι),
  Ne.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) 0 →
    LE.le.{0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) 1 →
      ¬Eq.{1} 1 ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) → False
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.leftPart._proof_1

```lean
Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.leftExp 0 0) (HeckeSkeleton.LowHybrid.Factorization.leftExp 0 0)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.leftPart.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (n b : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.leftPart.{u_1, u_2} coords n b)
    (HeckeSkeleton.LowHybrid.PrimeArithmetic.mapTwo.{u_1, u_2} coords HeckeSkeleton.LowHybrid.Factorization.leftExp
      HeckeSkeleton.LowHybrid.PrimeArithmetic.leftPart._proof_1 n b)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.mapTwo.congr_simp

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords coords_1 : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))),
  Eq.{max (u_1 + 1) (u_2 + 1)} coords coords_1 →
    ∀ (f f_1 : ℕ → ℕ → ℕ) (e_f : Eq.{1} f f_1) (hf : Eq.{1} (f 0 0) 0) (a a_1 : A),
      Eq.{u_2 + 1} a a_1 →
        ∀ (b b_1 : A),
          Eq.{u_2 + 1} b b_1 →
            Eq.{u_2 + 1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.mapTwo.{u_1, u_2} coords f hf a b)
              (HeckeSkeleton.LowHybrid.PrimeArithmetic.mapTwo.{u_1, u_2} coords_1 f_1 (Eq.ndrec.{0, 1} hf e_f) a_1 b_1)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.mapTwo.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (f : ℕ → ℕ → ℕ) (hf : Eq.{1} (f 0 0) 0)
  (a b : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.mapTwo.{u_1, u_2} coords f hf a b)
    ((MulEquiv.symm.{u_2, u_1} coords)
      (Multiplicative.ofAdd.{u_1}
        (Finsupp.zipWith.{u_1, 0, 0, 0} f hf
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a)
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b))))
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.mem_normCutoff._simp_1

```lean
∀ {A : Type u_2} [CommMonoid.{u_2} A] (normI : A → ℝ)
  (hfinite : ∀ (X : ℝ), Set.Finite.{u_2} (Set.ofPred.{u_2} fun a => LE.le.{0} (normI a) X)) (X : ℝ) (a : A),
  Eq.{1} (Membership.mem.{u_2, u_2} (HeckeSkeleton.LowHybrid.PrimeArithmetic.normCutoff.{u_2} normI hfinite X) a)
    (LE.le.{0} (normI a) X)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.mobius.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A),
  Eq.{1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.mobius.{u_1, u_2} coords a)
    (HPow.hPow.{0, 0, 0} (-1) (Finset.card.{u_1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.support.{u_1, u_2} coords a)))
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.prime_product_le_norm._proof_1_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A) (p : ι),
  Ne.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) 0 →
    ¬LE.le.{0} 1 ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) → False
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.product_fiber_card_le_squarefree_divisors._proof_1_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) ⦃u v : Prod.{u_2, u_2} A A⦄ (p : ι),
  Eq.{1}
      (HAdd.hAdd.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords v.1) p)
        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords u.2) p))
      (HAdd.hAdd.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords v.1) p)
        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords v.2) p)) →
    ¬Eq.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords u.2) p)
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords v.2) p) →
      False
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.quotient._proof_1

```lean
Eq.{1} (HSub.hSub.{0, 0, 0} 0 0) (HSub.hSub.{0, 0, 0} 0 0)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.quotient.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (d k : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.quotient.{u_1, u_2} coords d k)
    (HeckeSkeleton.LowHybrid.PrimeArithmetic.mapTwo.{u_1, u_2} coords (fun a b => HSub.hSub.{0, 0, 0} b a)
      HeckeSkeleton.LowHybrid.PrimeArithmetic.quotient._proof_1 d k)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.quotient_spec._proof_1_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (d k : A) (p : ι),
  LE.le.{0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords d) p)
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords k) p) →
    ¬Eq.{1}
          (HAdd.hAdd.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords d) p)
            (HSub.hSub.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords k) p)
              ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords d) p)))
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords k) p) →
      False
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.rightPart._proof_1

```lean
Eq.{1} (HeckeSkeleton.LowHybrid.Factorization.rightExp 0 0) (HeckeSkeleton.LowHybrid.Factorization.rightExp 0 0)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.rightPart.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (n b : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.rightPart.{u_1, u_2} coords n b)
    (HeckeSkeleton.LowHybrid.PrimeArithmetic.mapTwo.{u_1, u_2} coords HeckeSkeleton.LowHybrid.Factorization.rightExp
      HeckeSkeleton.LowHybrid.PrimeArithmetic.rightPart._proof_1 n b)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.squarePart._proof_1

```lean
Eq.{1} (0 / 2) (0 / 2)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.squarePart.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (b : A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.squarePart.{u_1, u_2} coords b)
    (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.mapExponents.{u_1, u_2} coords (fun e => HDiv.hDiv.{0, 0, 0} e 2)
      HeckeSkeleton.LowHybrid.PrimeArithmetic.squarePart._proof_1 b)
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.squarefree_mem_divisors._proof_1_1

```lean
¬LE.le.{0} 1 1 → False
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.squarefree_mem_divisors._proof_1_2

```lean
¬LE.le.{0} 0 1 → False
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.support.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) (a : A),
  Eq.{u_1 + 1} (HeckeSkeleton.LowHybrid.PrimeArithmetic.support.{u_1, u_2} coords a)
    (Finsupp.support.{u_1, 0} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a))
```

## HeckeSkeleton.LowHybrid.PrimeArithmetic.support_subset_of_dvd._proof_1_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (coords : MulEquiv.{u_2, u_1} A (Multiplicative.{u_1} (Finsupp.{u_1, 0} ι ℕ))) {a b : A} ⦃p : ι⦄,
  Ne.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p) 0 →
    LE.le.{0} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords a) p)
        ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p) →
      Eq.{1} ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2} coords b) p) 0 → False
```

## HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.budget

```lean
∀ {I : Type u} {b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I} {rows : Finset.{u} I} {Q S Rbudget A : ℝ},
  HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.{u, v} b rows Q S Rbudget A →
    ∀ (t : HeckeSkeleton.LowHybrid.WeightedBlock.T.{u, v} b),
      Membership.mem.{v, v} (HeckeSkeleton.LowHybrid.WeightedBlock.ts.{u, v} b) t →
        ∀ (c : HeckeSkeleton.LowHybrid.WeightedBlock.C.{u, v} b),
          Membership.mem.{v, v} (HeckeSkeleton.LowHybrid.WeightedBlock.cs.{u, v} b) c →
            ∀ (m : HeckeSkeleton.LowHybrid.WeightedBlock.M.{u, v} b),
              Membership.mem.{v, v} (HeckeSkeleton.LowHybrid.WeightedBlock.ms.{u, v} b) m →
                ∀ (h : HeckeSkeleton.LowHybrid.WeightedBlock.H.{u, v} b),
                  Membership.mem.{v, v} (HeckeSkeleton.LowHybrid.WeightedBlock.hs.{u, v} b) h →
                    LE.le.{0}
                      (HMul.hMul.{0, 0, 0}
                        (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.WeightedBlock.wt.{u, v} b t)
                          (HeckeSkeleton.LowHybrid.WeightedBlock.wc.{u, v} b c))
                        (HPow.hPow.{0, 0, 0}
                          (Norm.norm.{0} (HeckeSkeleton.LowHybrid.WeightedBlock.beta.{u, v} b t c m h)) 2))
                      (HDiv.hDiv.{0, 0, 0} Rbudget
                        (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.WeightedBlock.wt.{u, v} b t)
                          (HeckeSkeleton.LowHybrid.WeightedBlock.wh.{u, v} b h)))
```

## HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.column_mass

```lean
∀ {I : Type u} {b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I} {rows : Finset.{u} I} {Q S Rbudget A : ℝ},
  HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.{u, v} b rows Q S Rbudget A →
    ∀ (t : HeckeSkeleton.LowHybrid.WeightedBlock.T.{u, v} b),
      Membership.mem.{v, v} (HeckeSkeleton.LowHybrid.WeightedBlock.ts.{u, v} b) t →
        ∀ (h : HeckeSkeleton.LowHybrid.WeightedBlock.H.{u, v} b),
          Membership.mem.{v, v} (HeckeSkeleton.LowHybrid.WeightedBlock.hs.{u, v} b) h →
            LE.le.{0}
              (∑ p ∈ HeckeSkeleton.LowHybrid.WeightedBlock.ps.{u, v} b,
                HPow.hPow.{0, 0, 0} (Norm.norm.{0} (HeckeSkeleton.LowHybrid.WeightedBlock.a.{u, v} b t h p)) 2)
              A
```

## HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.cubic

```lean
∀ {I : Type u} {b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I} {rows : Finset.{u} I} {Q S Rbudget A : ℝ},
  HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.{u, v} b rows Q S Rbudget A →
    ∀ (f : HeckeSkeleton.LowHybrid.WeightedBlock.P.{u, v} b → ℂ),
      LE.le.{0}
        (∑ m ∈ HeckeSkeleton.LowHybrid.WeightedBlock.ms.{u, v} b,
          ∑ c ∈ HeckeSkeleton.LowHybrid.WeightedBlock.cs.{u, v} b,
            HPow.hPow.{0, 0, 0}
              (Norm.norm.{0}
                (∑ p ∈ HeckeSkeleton.LowHybrid.WeightedBlock.ps.{u, v} b,
                  HMul.hMul.{0, 0, 0} (f p) (HeckeSkeleton.LowHybrid.WeightedBlock.chi.{u, v} b m c p)))
              2)
        (HMul.hMul.{0, 0, 0} S
          (∑ p ∈ HeckeSkeleton.LowHybrid.WeightedBlock.ps.{u, v} b, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (f p)) 2))
```

## HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.mask

```lean
∀ {I : Type u} {b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I} {rows : Finset.{u} I} {Q S Rbudget A : ℝ},
  HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.{u, v} b rows Q S Rbudget A →
    ∀ (i : I),
      Membership.mem.{u, u} rows i →
        ∀ (t : HeckeSkeleton.LowHybrid.WeightedBlock.T.{u, v} b),
          Membership.mem.{v, v} (HeckeSkeleton.LowHybrid.WeightedBlock.ts.{u, v} b) t →
            LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowHybrid.WeightedBlock.rowMask.{u, v} b i t)) 1
```

## HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.quadratic

```lean
∀ {I : Type u} {b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I} {rows : Finset.{u} I} {Q S Rbudget A : ℝ},
  HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.{u, v} b rows Q S Rbudget A →
    ∀ (f : HeckeSkeleton.LowHybrid.WeightedBlock.M.{u, v} b → HeckeSkeleton.LowHybrid.WeightedBlock.H.{u, v} b → ℂ),
      LE.le.{0}
        (∑ i ∈ rows,
          HPow.hPow.{0, 0, 0}
            (Norm.norm.{0}
              (∑ m ∈ HeckeSkeleton.LowHybrid.WeightedBlock.ms.{u, v} b,
                ∑ h ∈ HeckeSkeleton.LowHybrid.WeightedBlock.hs.{u, v} b,
                  HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.WeightedBlock.q.{u, v} b i m h) (f m h)))
            2)
        (HMul.hMul.{0, 0, 0} Q
          (∑ m ∈ HeckeSkeleton.LowHybrid.WeightedBlock.ms.{u, v} b,
            ∑ h ∈ HeckeSkeleton.LowHybrid.WeightedBlock.hs.{u, v} b, HPow.hPow.{0, 0, 0} (Norm.norm.{0} (f m h)) 2))
```

## HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.wc_pos

```lean
∀ {I : Type u} {b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I} {rows : Finset.{u} I} {Q S Rbudget A : ℝ},
  HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.{u, v} b rows Q S Rbudget A →
    ∀ (c : HeckeSkeleton.LowHybrid.WeightedBlock.C.{u, v} b),
      Membership.mem.{v, v} (HeckeSkeleton.LowHybrid.WeightedBlock.cs.{u, v} b) c →
        LT.lt.{0} 0 (HeckeSkeleton.LowHybrid.WeightedBlock.wc.{u, v} b c)
```

## HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.wh_pos

```lean
∀ {I : Type u} {b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I} {rows : Finset.{u} I} {Q S Rbudget A : ℝ},
  HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.{u, v} b rows Q S Rbudget A →
    ∀ (h : HeckeSkeleton.LowHybrid.WeightedBlock.H.{u, v} b),
      Membership.mem.{v, v} (HeckeSkeleton.LowHybrid.WeightedBlock.hs.{u, v} b) h →
        LT.lt.{0} 0 (HeckeSkeleton.LowHybrid.WeightedBlock.wh.{u, v} b h)
```

## HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.wt_pos

```lean
∀ {I : Type u} {b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I} {rows : Finset.{u} I} {Q S Rbudget A : ℝ},
  HeckeSkeleton.LowHybrid.WeightedBlock.Admissible.{u, v} b rows Q S Rbudget A →
    ∀ (t : HeckeSkeleton.LowHybrid.WeightedBlock.T.{u, v} b),
      Membership.mem.{v, v} (HeckeSkeleton.LowHybrid.WeightedBlock.ts.{u, v} b) t →
        LT.lt.{0} 0 (HeckeSkeleton.LowHybrid.WeightedBlock.wt.{u, v} b t)
```

## HeckeSkeleton.LowHybrid.WeightedBlock.cHarmonic.eq_1

```lean
∀ {I : Type u} (b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I),
  Eq.{1} (HeckeSkeleton.LowHybrid.WeightedBlock.cHarmonic.{u, v} b)
    (∑ c ∈ HeckeSkeleton.LowHybrid.WeightedBlock.cs.{u, v} b,
      HDiv.hDiv.{0, 0, 0} 1 (HeckeSkeleton.LowHybrid.WeightedBlock.wc.{u, v} b c))
```

## HeckeSkeleton.LowHybrid.WeightedBlock.hHarmonic.eq_1

```lean
∀ {I : Type u} (b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I),
  Eq.{1} (HeckeSkeleton.LowHybrid.WeightedBlock.hHarmonic.{u, v} b)
    (∑ h ∈ HeckeSkeleton.LowHybrid.WeightedBlock.hs.{u, v} b,
      HDiv.hDiv.{0, 0, 0} 1 (HeckeSkeleton.LowHybrid.WeightedBlock.wh.{u, v} b h))
```

## HeckeSkeleton.LowHybrid.WeightedBlock.mk.inj

```lean
∀ {I : Type u} {T C M H P : Type v} {ts : Finset.{v} T} {cs : Finset.{v} C} {ms : Finset.{v} M} {hs : Finset.{v} H}
  {ps : Finset.{v} P} {q : I → M → H → ℂ} {chi : M → C → P → ℂ} {a : T → H → P → ℂ} {beta : T → C → M → H → ℂ}
  {rowMask : I → T → ℂ} {wt : T → ℝ} {wc : C → ℝ} {wh : H → ℝ} {T_1 C_1 M_1 H_1 P_1 : Type v} {ts_1 : Finset.{v} T_1}
  {cs_1 : Finset.{v} C_1} {ms_1 : Finset.{v} M_1} {hs_1 : Finset.{v} H_1} {ps_1 : Finset.{v} P_1}
  {q_1 : I → M_1 → H_1 → ℂ} {chi_1 : M_1 → C_1 → P_1 → ℂ} {a_1 : T_1 → H_1 → P_1 → ℂ}
  {beta_1 : T_1 → C_1 → M_1 → H_1 → ℂ} {rowMask_1 : I → T_1 → ℂ} {wt_1 : T_1 → ℝ} {wc_1 : C_1 → ℝ} {wh_1 : H_1 → ℝ},
  Eq.{max (u + 1) (v + 2)}
      (HeckeSkeleton.LowHybrid.WeightedBlock.mk.{u, v} T C M H P ts cs ms hs ps q chi a beta rowMask wt wc wh)
      (HeckeSkeleton.LowHybrid.WeightedBlock.mk.{u, v} T_1 C_1 M_1 H_1 P_1 ts_1 cs_1 ms_1 hs_1 ps_1 q_1 chi_1 a_1 beta_1
        rowMask_1 wt_1 wc_1 wh_1) →
    Eq.{v + 2} T T_1 ∧
      Eq.{v + 2} C C_1 ∧
        Eq.{v + 2} M M_1 ∧
          Eq.{v + 2} H H_1 ∧
            Eq.{v + 2} P P_1 ∧
              HEq.{v + 1} ts ts_1 ∧
                HEq.{v + 1} cs cs_1 ∧
                  HEq.{v + 1} ms ms_1 ∧
                    HEq.{v + 1} hs hs_1 ∧
                      HEq.{v + 1} ps ps_1 ∧
                        HEq.{max (u + 1) (v + 1)} q q_1 ∧
                          HEq.{v + 1} chi chi_1 ∧
                            HEq.{v + 1} a a_1 ∧
                              HEq.{v + 1} beta beta_1 ∧
                                HEq.{max (u + 1) (v + 1)} rowMask rowMask_1 ∧
                                  HEq.{v + 1} wt wt_1 ∧ HEq.{v + 1} wc wc_1 ∧ HEq.{v + 1} wh wh_1
```

## HeckeSkeleton.LowHybrid.WeightedBlock.mk.injEq

```lean
∀ {I : Type u} (T C M H P : Type v) (ts : Finset.{v} T) (cs : Finset.{v} C) (ms : Finset.{v} M) (hs : Finset.{v} H)
  (ps : Finset.{v} P) (q : I → M → H → ℂ) (chi : M → C → P → ℂ) (a : T → H → P → ℂ) (beta : T → C → M → H → ℂ)
  (rowMask : I → T → ℂ) (wt : T → ℝ) (wc : C → ℝ) (wh : H → ℝ) (T_1 C_1 M_1 H_1 P_1 : Type v) (ts_1 : Finset.{v} T_1)
  (cs_1 : Finset.{v} C_1) (ms_1 : Finset.{v} M_1) (hs_1 : Finset.{v} H_1) (ps_1 : Finset.{v} P_1)
  (q_1 : I → M_1 → H_1 → ℂ) (chi_1 : M_1 → C_1 → P_1 → ℂ) (a_1 : T_1 → H_1 → P_1 → ℂ)
  (beta_1 : T_1 → C_1 → M_1 → H_1 → ℂ) (rowMask_1 : I → T_1 → ℂ) (wt_1 : T_1 → ℝ) (wc_1 : C_1 → ℝ) (wh_1 : H_1 → ℝ),
  Eq.{1}
    (Eq.{max (u + 1) (v + 2)}
      (HeckeSkeleton.LowHybrid.WeightedBlock.mk.{u, v} T C M H P ts cs ms hs ps q chi a beta rowMask wt wc wh)
      (HeckeSkeleton.LowHybrid.WeightedBlock.mk.{u, v} T_1 C_1 M_1 H_1 P_1 ts_1 cs_1 ms_1 hs_1 ps_1 q_1 chi_1 a_1 beta_1
        rowMask_1 wt_1 wc_1 wh_1))
    (Eq.{v + 2} T T_1 ∧
      Eq.{v + 2} C C_1 ∧
        Eq.{v + 2} M M_1 ∧
          Eq.{v + 2} H H_1 ∧
            Eq.{v + 2} P P_1 ∧
              HEq.{v + 1} ts ts_1 ∧
                HEq.{v + 1} cs cs_1 ∧
                  HEq.{v + 1} ms ms_1 ∧
                    HEq.{v + 1} hs hs_1 ∧
                      HEq.{v + 1} ps ps_1 ∧
                        HEq.{max (u + 1) (v + 1)} q q_1 ∧
                          HEq.{v + 1} chi chi_1 ∧
                            HEq.{v + 1} a a_1 ∧
                              HEq.{v + 1} beta beta_1 ∧
                                HEq.{max (u + 1) (v + 1)} rowMask rowMask_1 ∧
                                  HEq.{v + 1} wt wt_1 ∧ HEq.{v + 1} wc wc_1 ∧ HEq.{v + 1} wh wh_1)
```

## HeckeSkeleton.LowHybrid.WeightedBlock.mk.sizeOf_spec

```lean
∀ {I : Type u} [inst : SizeOf.{u + 1} I] (T C M H P : Type v) (ts : Finset.{v} T) (cs : Finset.{v} C)
  (ms : Finset.{v} M) (hs : Finset.{v} H) (ps : Finset.{v} P) (q : I → M → H → ℂ) (chi : M → C → P → ℂ)
  (a : T → H → P → ℂ) (beta : T → C → M → H → ℂ) (rowMask : I → T → ℂ) (wt : T → ℝ) (wc : C → ℝ) (wh : H → ℝ),
  Eq.{1}
    (SizeOf.sizeOf.{max (u + 1) (v + 2)}
      (HeckeSkeleton.LowHybrid.WeightedBlock.mk.{u, v} T C M H P ts cs ms hs ps q chi a beta rowMask wt wc wh))
    (HAdd.hAdd.{0, 0, 0}
      (HAdd.hAdd.{0, 0, 0}
        (HAdd.hAdd.{0, 0, 0}
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0}
                (HAdd.hAdd.{0, 0, 0}
                  (HAdd.hAdd.{0, 0, 0}
                    (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 (SizeOf.sizeOf.{v + 2} T)) (SizeOf.sizeOf.{v + 2} C))
                    (SizeOf.sizeOf.{v + 2} M))
                  (SizeOf.sizeOf.{v + 2} H))
                (SizeOf.sizeOf.{v + 2} P))
              (SizeOf.sizeOf.{v + 1} ts))
            (SizeOf.sizeOf.{v + 1} cs))
          (SizeOf.sizeOf.{v + 1} ms))
        (SizeOf.sizeOf.{v + 1} hs))
      (SizeOf.sizeOf.{v + 1} ps))
```

## HeckeSkeleton.LowHybrid.WeightedBlock.row.eq_1

```lean
∀ {I : Type u} (b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I) (i : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.WeightedBlock.row.{u, v} b i)
    (∑ t ∈ HeckeSkeleton.LowHybrid.WeightedBlock.ts.{u, v} b,
      ∑ c ∈ HeckeSkeleton.LowHybrid.WeightedBlock.cs.{u, v} b,
        HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.WeightedBlock.rowMask.{u, v} b i t)
          (∑ m ∈ HeckeSkeleton.LowHybrid.WeightedBlock.ms.{u, v} b,
            ∑ h ∈ HeckeSkeleton.LowHybrid.WeightedBlock.hs.{u, v} b,
              HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.WeightedBlock.q.{u, v} b i m h)
                (HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.WeightedBlock.beta.{u, v} b t c m h)
                  (∑ p ∈ HeckeSkeleton.LowHybrid.WeightedBlock.ps.{u, v} b,
                    HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.WeightedBlock.a.{u, v} b t h p)
                      (HeckeSkeleton.LowHybrid.WeightedBlock.chi.{u, v} b m c p)))))
```

## HeckeSkeleton.LowHybrid.WeightedBlock.tHarmonic.eq_1

```lean
∀ {I : Type u} (b : HeckeSkeleton.LowHybrid.WeightedBlock.{u, v} I),
  Eq.{1} (HeckeSkeleton.LowHybrid.WeightedBlock.tHarmonic.{u, v} b)
    (∑ t ∈ HeckeSkeleton.LowHybrid.WeightedBlock.ts.{u, v} b,
      HDiv.hDiv.{0, 0, 0} 1 (HeckeSkeleton.LowHybrid.WeightedBlock.wt.{u, v} b t))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.mk.inj

```lean
∀ {ι : Type u_1} {A : Type u_2} {inst : CommMonoid.{u_2} A}
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A} {rowBall : ℝ}
  {rows_norm :
    ∀ (k : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1, u_2} b) k →
        LE.le.{0} (normI k) rowBall}
  {residual_norm :
    ∀ (d : A),
      Membership.mem.{u_2, u_2}
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.pow.{u_1, u_2} b)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.sup.{u_1, u_2} b)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1, u_2} b))
          d →
        LE.le.{0} (normI d) (HPow.hPow.{0, 0, 0} Z H)}
  {rho_norm :
    ∀ (d : A),
      (∀ (p : ι),
          LE.le.{0}
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) d)
              p)
            1) →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d →
          Eq.{1} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.ρ₀.{u_1, u_2} b d)) 1}
  {marks_away :
    ∀ (P : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P}
  {marks_sf_norm :
    ∀ (P : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
        HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P ∧
          LE.le.{0} (normI P) (HPow.hPow.{0, 0, 0} Z z)}
  {marks_coeff :
    ∀ (P : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
        LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.a₀.{u_1, u_2} b P)) 1}
  {columns_away :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c}
  {columns_sf_norm :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) c ∧
          LE.le.{0} (normI c) (HPow.hPow.{0, 0, 0} Z v)}
  {columns_coeff :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.lam.{u_1, u_2} b c)) 1}
  {columns_lower :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z v) 2) (normI c)}
  {input_supported :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) u.1}
  {input_away :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) u.2}
  {input_phase :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        ∀ (u : Prod.{u_2, u_2} A A),
          Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
            LE.le.{0}
              (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.phase.{u_1, u_2} b c u.1 u.2)) 1}
  {cube_lower :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z ell) 2)
          (normI
            (HMul.hMul.{u_2, u_2, u_2}
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) u.1)
              u.2))}
  {cube_upper :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        LE.le.{0}
          (normI
            (HMul.hMul.{u_2, u_2, u_2}
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) u.1)
              u.2))
          (HPow.hPow.{0, 0, 0} Z ell)}
  {rowBall_1 : ℝ}
  {rows_norm_1 :
    ∀ (k : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1, u_2} b) k →
        LE.le.{0} (normI k) rowBall_1}
  {residual_norm_1 :
    ∀ (d : A),
      Membership.mem.{u_2, u_2}
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.pow.{u_1, u_2} b)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.sup.{u_1, u_2} b)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1, u_2} b))
          d →
        LE.le.{0} (normI d) (HPow.hPow.{0, 0, 0} Z H)}
  {rho_norm_1 :
    ∀ (d : A),
      (∀ (p : ι),
          LE.le.{0}
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) d)
              p)
            1) →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d →
          Eq.{1} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.ρ₀.{u_1, u_2} b d)) 1}
  {marks_away_1 :
    ∀ (P : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P}
  {marks_sf_norm_1 :
    ∀ (P : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
        HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P ∧
          LE.le.{0} (normI P) (HPow.hPow.{0, 0, 0} Z z)}
  {marks_coeff_1 :
    ∀ (P : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
        LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.a₀.{u_1, u_2} b P)) 1}
  {columns_away_1 :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c}
  {columns_sf_norm_1 :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) c ∧
          LE.le.{0} (normI c) (HPow.hPow.{0, 0, 0} Z v)}
  {columns_coeff_1 :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.lam.{u_1, u_2} b c)) 1}
  {columns_lower_1 :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z v) 2) (normI c)}
  {input_supported_1 :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) u.1}
  {input_away_1 :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) u.2}
  {input_phase_1 :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        ∀ (u : Prod.{u_2, u_2} A A),
          Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
            LE.le.{0}
              (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.phase.{u_1, u_2} b c u.1 u.2)) 1}
  {cube_lower_1 :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z ell) 2)
          (normI
            (HMul.hMul.{u_2, u_2, u_2}
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) u.1)
              u.2))}
  {cube_upper_1 :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        LE.le.{0}
          (normI
            (HMul.hMul.{u_2, u_2, u_2}
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) u.1)
              u.2))
          (HPow.hPow.{0, 0, 0} Z ell)},
  Eq.{1}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.mk.{u_1, u_2} rowBall rows_norm residual_norm rho_norm
        marks_away marks_sf_norm marks_coeff columns_away columns_sf_norm columns_coeff columns_lower input_supported
        input_away input_phase cube_lower cube_upper)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.mk.{u_1, u_2} rowBall_1 rows_norm_1 residual_norm_1
        rho_norm_1 marks_away_1 marks_sf_norm_1 marks_coeff_1 columns_away_1 columns_sf_norm_1 columns_coeff_1
        columns_lower_1 input_supported_1 input_away_1 input_phase_1 cube_lower_1 cube_upper_1) →
    Eq.{1} rowBall rowBall_1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.mk.injEq

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A} (rowBall : ℝ)
  (rows_norm :
    ∀ (k : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1, u_2} b) k →
        LE.le.{0} (normI k) rowBall)
  (residual_norm :
    ∀ (d : A),
      Membership.mem.{u_2, u_2}
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.pow.{u_1, u_2} b)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.sup.{u_1, u_2} b)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1, u_2} b))
          d →
        LE.le.{0} (normI d) (HPow.hPow.{0, 0, 0} Z H))
  (rho_norm :
    ∀ (d : A),
      (∀ (p : ι),
          LE.le.{0}
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) d)
              p)
            1) →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d →
          Eq.{1} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.ρ₀.{u_1, u_2} b d)) 1)
  (marks_away :
    ∀ (P : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P)
  (marks_sf_norm :
    ∀ (P : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
        HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P ∧
          LE.le.{0} (normI P) (HPow.hPow.{0, 0, 0} Z z))
  (marks_coeff :
    ∀ (P : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
        LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.a₀.{u_1, u_2} b P)) 1)
  (columns_away :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c)
  (columns_sf_norm :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) c ∧
          LE.le.{0} (normI c) (HPow.hPow.{0, 0, 0} Z v))
  (columns_coeff :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.lam.{u_1, u_2} b c)) 1)
  (columns_lower :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z v) 2) (normI c))
  (input_supported :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) u.1)
  (input_away :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) u.2)
  (input_phase :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        ∀ (u : Prod.{u_2, u_2} A A),
          Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
            LE.le.{0}
              (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.phase.{u_1, u_2} b c u.1 u.2)) 1)
  (cube_lower :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z ell) 2)
          (normI
            (HMul.hMul.{u_2, u_2, u_2}
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) u.1)
              u.2)))
  (cube_upper :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        LE.le.{0}
          (normI
            (HMul.hMul.{u_2, u_2, u_2}
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) u.1)
              u.2))
          (HPow.hPow.{0, 0, 0} Z ell))
  (rowBall_1 : ℝ)
  (rows_norm_1 :
    ∀ (k : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1, u_2} b) k →
        LE.le.{0} (normI k) rowBall_1)
  (residual_norm_1 :
    ∀ (d : A),
      Membership.mem.{u_2, u_2}
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.pow.{u_1, u_2} b)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.sup.{u_1, u_2} b)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1, u_2} b))
          d →
        LE.le.{0} (normI d) (HPow.hPow.{0, 0, 0} Z H))
  (rho_norm_1 :
    ∀ (d : A),
      (∀ (p : ι),
          LE.le.{0}
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) d)
              p)
            1) →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d →
          Eq.{1} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.ρ₀.{u_1, u_2} b d)) 1)
  (marks_away_1 :
    ∀ (P : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P)
  (marks_sf_norm_1 :
    ∀ (P : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
        HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P ∧
          LE.le.{0} (normI P) (HPow.hPow.{0, 0, 0} Z z))
  (marks_coeff_1 :
    ∀ (P : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
        LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.a₀.{u_1, u_2} b P)) 1)
  (columns_away_1 :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c)
  (columns_sf_norm_1 :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) c ∧
          LE.le.{0} (normI c) (HPow.hPow.{0, 0, 0} Z v))
  (columns_coeff_1 :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.lam.{u_1, u_2} b c)) 1)
  (columns_lower_1 :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z v) 2) (normI c))
  (input_supported_1 :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) u.1)
  (input_away_1 :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) u.2)
  (input_phase_1 :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        ∀ (u : Prod.{u_2, u_2} A A),
          Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
            LE.le.{0}
              (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.phase.{u_1, u_2} b c u.1 u.2)) 1)
  (cube_lower_1 :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z ell) 2)
          (normI
            (HMul.hMul.{u_2, u_2, u_2}
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) u.1)
              u.2)))
  (cube_upper_1 :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        LE.le.{0}
          (normI
            (HMul.hMul.{u_2, u_2, u_2}
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) u.1)
              u.2))
          (HPow.hPow.{0, 0, 0} Z ell)),
  Eq.{1}
    (Eq.{1}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.mk.{u_1, u_2} rowBall rows_norm residual_norm rho_norm
        marks_away marks_sf_norm marks_coeff columns_away columns_sf_norm columns_coeff columns_lower input_supported
        input_away input_phase cube_lower cube_upper)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.mk.{u_1, u_2} rowBall_1 rows_norm_1 residual_norm_1
        rho_norm_1 marks_away_1 marks_sf_norm_1 marks_coeff_1 columns_away_1 columns_sf_norm_1 columns_coeff_1
        columns_lower_1 input_supported_1 input_away_1 input_phase_1 cube_lower_1 cube_upper_1))
    (Eq.{1} rowBall rowBall_1)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.mk.sizeOf_spec

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  {D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A} {normI : A → ℝ} {Z H v ell z : ℝ}
  {b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A} [inst_1 : SizeOf.{u_1 + 1} ι]
  [inst_2 : SizeOf.{u_2 + 1} A] (rowBall : ℝ)
  (rows_norm :
    ∀ (k : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1, u_2} b) k →
        LE.le.{0} (normI k) rowBall)
  (residual_norm :
    ∀ (d : A),
      Membership.mem.{u_2, u_2}
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRows.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.pow.{u_1, u_2} b)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.sup.{u_1, u_2} b)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1, u_2} b))
          d →
        LE.le.{0} (normI d) (HPow.hPow.{0, 0, 0} Z H))
  (rho_norm :
    ∀ (d : A),
      (∀ (p : ι),
          LE.le.{0}
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) d)
              p)
            1) →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) d →
          Eq.{1} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.ρ₀.{u_1, u_2} b d)) 1)
  (marks_away :
    ∀ (P : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) P)
  (marks_sf_norm :
    ∀ (P : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
        HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P ∧
          LE.le.{0} (normI P) (HPow.hPow.{0, 0, 0} Z z))
  (marks_coeff :
    ∀ (P : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b) P →
        LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.a₀.{u_1, u_2} b P)) 1)
  (columns_away :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) c)
  (columns_sf_norm :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) c ∧
          LE.le.{0} (normI c) (HPow.hPow.{0, 0, 0} Z v))
  (columns_coeff :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        LE.le.{0} (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.lam.{u_1, u_2} b c)) 1)
  (columns_lower :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z v) 2) (normI c))
  (input_supported :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) u.1)
  (input_away :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Avoids.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D) u.2)
  (input_phase :
    ∀ (c : A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b) c →
        ∀ (u : Prod.{u_2, u_2} A A),
          Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
            LE.le.{0}
              (Norm.norm.{0} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.phase.{u_1, u_2} b c u.1 u.2)) 1)
  (cube_lower :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} Z ell) 2)
          (normI
            (HMul.hMul.{u_2, u_2, u_2}
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) u.1)
              u.2)))
  (cube_upper :
    ∀ (u : Prod.{u_2, u_2} A A),
      Membership.mem.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b) u →
        LE.le.{0}
          (normI
            (HMul.hMul.{u_2, u_2, u_2}
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) u.1)
              u.2))
          (HPow.hPow.{0, 0, 0} Z ell)),
  Eq.{1}
    (SizeOf.sizeOf.{1}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.AnnularSupport.mk.{u_1, u_2} rowBall rows_norm residual_norm rho_norm
        marks_away marks_sf_norm marks_coeff columns_away columns_sf_norm columns_coeff columns_lower input_supported
        input_away input_phase cube_lower cube_upper))
    (HAdd.hAdd.{0, 0, 0} 1 (SizeOf.sizeOf.{1} rowBall))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.WeightedRawHybridBound._proof_1

```lean
(HAdd.hAdd.{0, 0, 0} 1 1).AtLeastTwo
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.WeightedRawHybridBound._proof_2

```lean
(HAdd.hAdd.{0, 0, 0} 2 1).AtLeastTwo
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.activeInputBlock.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  Eq.{u_2 + 1}
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.activeInputBlock.{u_1, u_2} D normI first prefactor atZero inputs)
    ({q ∈ HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimumBlock.{u_1, u_2} D inputs |
      Ne.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawTable.{u_1, u_2} D normI first prefactor atZero q.1)
        0})
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.beta.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (lam : A → ℂ)
  (Ω : A → A → A → ℂ),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.beta.{u_1, u_2} D normI lam Ω)
    (HeckeSkeleton.LowFrozenCube.fullCubeCoefficient.{u_2}
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.cubeSplit.{u_1, u_2}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.residualCoefficient.{u_1, u_2} D normI lam Ω))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.canonical_supported._proof_1_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (x : A) (p : ι),
  Eq.{1}
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
        p)
      0 →
    Eq.{1}
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
            p)
          1 ∨
        Eq.{1}
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
              p)
            3 ∨
          Eq.{1}
              ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
                p)
              0 ∧
            Eq.{1}
              ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) x)
                p)
              0 →
      ¬Eq.{1}
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) x)
              p)
            0 →
        False
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.canonical_supported_on._proof_1_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (x : A) (p : ι),
  Eq.{1}
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
        p)
      0 →
    Eq.{1}
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
            p)
          1 ∨
        Eq.{1}
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
              p)
            3 ∨
          Eq.{1}
              ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
                p)
              0 ∧
            Eq.{1}
              ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) x)
                p)
              0 →
      ¬Eq.{1}
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) x)
              p)
            0 →
        False
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.canonical_supported_ordinary._proof_1_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (x : A) (p : ι),
  Eq.{1}
      ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
        p)
      0 →
    Eq.{1}
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
            p)
          1 ∨
        Eq.{1}
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
              p)
            3 ∨
          Eq.{1}
              ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
                p)
              0 ∧
            Eq.{1}
              ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) x)
                p)
              0 →
      ¬Eq.{1}
            ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) x)
              p)
            0 →
        False
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.chargeIdeal.{u_1, u_2} D)
    (∏ p ∈ HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D,
      HPow.hPow.{u_2, 0, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.prime.{u_1, u_2} D p)
        (HeckeSkeleton.LowFrozenCube.LocalTable.minimumCharge
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D p)
          ((HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D))
            p)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.exponents.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (x : A),
  Eq.{u_1 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.exponents.{u_1, u_2} D x)
    ⇑(HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
        (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D)
          (HPow.hPow.{u_2, 0, u_2} x 3)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.familySourceRow.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ)
  (family : Prod.{u_2, u_2} A A → HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A) (k : A),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.familySourceRow.{u_1, u_2} D normI family k)
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceRow.{u_1, u_2} D normI
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.first.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2}
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.prefactor.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2}
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.atZero.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2}
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.phase.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2}
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.a₀.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2}
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.ρ₀.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2}
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.annularColumn.{u_2} normI
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.lam.{u_1, u_2}
          (family
            (Prod.mk.{u_2, u_2}
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) k)
              (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) k)))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2}
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2}
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) k))))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2}
        (family
          (Prod.mk.{u_2, u_2}
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.powerfulRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) k)
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.supportedRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) k))))
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) k))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.freezePair.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (q : Prod.{u_2, u_2} A A),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.freezePair.{u_1, u_2} D q)
    (Prod.mk.{u_2, u_2}
      (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualCubeFactor.{u_1, u_2}
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) q.1)
      q.2)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenInputPairs.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  Eq.{u_2 + 1}
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.frozenInputPairs.{u_1, u_2} D normI first prefactor atZero inputs)
    (Finset.image.{u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.freezePair.{u_1, u_2} D)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.activeInputBlock.{u_1, u_2} D normI first prefactor atZero
        inputs))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mem_activeInputBlock._simp_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)) (q : Prod.{u_2, u_2} A A),
  Eq.{1}
    (Membership.mem.{u_2, u_2}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.activeInputBlock.{u_1, u_2} D normI first prefactor atZero
        inputs)
      q)
    (Membership.mem.{u_2, u_2} inputs q ∧
      Eq.{u_2 + 1}
          (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.minimumFactor.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) q.1)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D) ∧
        Ne.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawTable.{u_1, u_2} D normI first prefactor atZero q.1)
          0)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mem_activeInputBlock._simp_1_3

```lean
∀ {a b c : Prop}, Eq.{1} ((a ∧ b) ∧ c) (a ∧ b ∧ c)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimumBlock.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimumBlock.{u_1, u_2} D inputs)
    ({q ∈ inputs |
      Eq.{u_2 + 1}
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.minimumFactor.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) q.1)
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D)})
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mixedPhase.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (d P c n : A),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mixedPhase.{u_1, u_2} D d P c n)
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0}
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0}
              (HPow.hPow.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D d) P) 4)
              (HPow.hPow.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D P) d) 2))
            (HMul.hMul.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D d) c)
              (HPow.hPow.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D c) d) 2)))
          (HPow.hPow.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D d) n) 3))
        (HMul.hMul.{0, 0, 0}
          (HPow.hPow.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D P) c) 2)
          (HPow.hPow.{0, 0, 0} ((HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D c) P) 2)))
      (ite.{1}
        (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) P n)
        1 0))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mk.inj

```lean
∀ {ι : Type u_3} {A : Type u_4} {inst : CommMonoid.{u_4} A}
  {coords : MulEquiv.{u_4, u_3} A (Multiplicative.{u_3} (Finsupp.{u_3, 0} ι ℕ))} {symbol : A → MonoidHom.{u_4, 0} A ℂ}
  {sixth :
    ∀ (a b : A),
      Eq.{1} (HPow.hPow.{0, 0, 0} ((symbol a) b) 6)
        (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_3, u_4} coords a b) 1 0)}
  {reciprocal : ∀ (a b : A), Eq.{1} ((symbol a) b) ((symbol b) a)} {support ordinary : Finset.{u_3} ι}
  {ordinary_subset : ordinary ⊆ support} {digit : ι → ℕ} {minimum : A}
  {minimum_ordinary : HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_3, u_4} coords ordinary minimum}
  {coords_1 : MulEquiv.{u_4, u_3} A (Multiplicative.{u_3} (Finsupp.{u_3, 0} ι ℕ))}
  {symbol_1 : A → MonoidHom.{u_4, 0} A ℂ}
  {sixth_1 :
    ∀ (a b : A),
      Eq.{1} (HPow.hPow.{0, 0, 0} ((symbol_1 a) b) 6)
        (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_3, u_4} coords_1 a b) 1 0)}
  {reciprocal_1 : ∀ (a b : A), Eq.{1} ((symbol_1 a) b) ((symbol_1 b) a)} {support_1 ordinary_1 : Finset.{u_3} ι}
  {ordinary_subset_1 : ordinary_1 ⊆ support_1} {digit_1 : ι → ℕ} {minimum_1 : A}
  {minimum_ordinary_1 :
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_3, u_4} coords_1 ordinary_1 minimum_1},
  Eq.{max (u_3 + 1) (u_4 + 1)}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mk.{u_3, u_4} coords symbol sixth reciprocal support ordinary
        ordinary_subset digit minimum minimum_ordinary)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mk.{u_3, u_4} coords_1 symbol_1 sixth_1 reciprocal_1 support_1
        ordinary_1 ordinary_subset_1 digit_1 minimum_1 minimum_ordinary_1) →
    Eq.{max (u_3 + 1) (u_4 + 1)} coords coords_1 ∧
      Eq.{u_4 + 1} symbol symbol_1 ∧
        Eq.{u_3 + 1} support support_1 ∧
          Eq.{u_3 + 1} ordinary ordinary_1 ∧ Eq.{u_3 + 1} digit digit_1 ∧ Eq.{u_4 + 1} minimum minimum_1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mk.injEq

```lean
∀ {ι : Type u_3} {A : Type u_4} [inst : CommMonoid.{u_4} A]
  (coords : MulEquiv.{u_4, u_3} A (Multiplicative.{u_3} (Finsupp.{u_3, 0} ι ℕ))) (symbol : A → MonoidHom.{u_4, 0} A ℂ)
  (sixth :
    ∀ (a b : A),
      Eq.{1} (HPow.hPow.{0, 0, 0} ((symbol a) b) 6)
        (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_3, u_4} coords a b) 1 0))
  (reciprocal : ∀ (a b : A), Eq.{1} ((symbol a) b) ((symbol b) a)) (support ordinary : Finset.{u_3} ι)
  (ordinary_subset : ordinary ⊆ support) (digit : ι → ℕ) (minimum : A)
  (minimum_ordinary : HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_3, u_4} coords ordinary minimum)
  (coords_1 : MulEquiv.{u_4, u_3} A (Multiplicative.{u_3} (Finsupp.{u_3, 0} ι ℕ)))
  (symbol_1 : A → MonoidHom.{u_4, 0} A ℂ)
  (sixth_1 :
    ∀ (a b : A),
      Eq.{1} (HPow.hPow.{0, 0, 0} ((symbol_1 a) b) 6)
        (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_3, u_4} coords_1 a b) 1 0))
  (reciprocal_1 : ∀ (a b : A), Eq.{1} ((symbol_1 a) b) ((symbol_1 b) a)) (support_1 ordinary_1 : Finset.{u_3} ι)
  (ordinary_subset_1 : ordinary_1 ⊆ support_1) (digit_1 : ι → ℕ) (minimum_1 : A)
  (minimum_ordinary_1 :
    HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_3, u_4} coords_1 ordinary_1 minimum_1),
  Eq.{1}
    (Eq.{max (u_3 + 1) (u_4 + 1)}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mk.{u_3, u_4} coords symbol sixth reciprocal support ordinary
        ordinary_subset digit minimum minimum_ordinary)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mk.{u_3, u_4} coords_1 symbol_1 sixth_1 reciprocal_1 support_1
        ordinary_1 ordinary_subset_1 digit_1 minimum_1 minimum_ordinary_1))
    (Eq.{max (u_3 + 1) (u_4 + 1)} coords coords_1 ∧
      Eq.{u_4 + 1} symbol symbol_1 ∧
        Eq.{u_3 + 1} support support_1 ∧
          Eq.{u_3 + 1} ordinary ordinary_1 ∧ Eq.{u_3 + 1} digit digit_1 ∧ Eq.{u_4 + 1} minimum minimum_1)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mk.sizeOf_spec

```lean
∀ {ι : Type u_3} {A : Type u_4} [inst : CommMonoid.{u_4} A] [inst_1 : SizeOf.{u_3 + 1} ι]
  [inst_2 : SizeOf.{u_4 + 1} A] (coords : MulEquiv.{u_4, u_3} A (Multiplicative.{u_3} (Finsupp.{u_3, 0} ι ℕ)))
  (symbol : A → MonoidHom.{u_4, 0} A ℂ)
  (sixth :
    ∀ (a b : A),
      Eq.{1} (HPow.hPow.{0, 0, 0} ((symbol a) b) 6)
        (ite.{1} (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Coprime.{u_3, u_4} coords a b) 1 0))
  (reciprocal : ∀ (a b : A), Eq.{1} ((symbol a) b) ((symbol b) a)) (support ordinary : Finset.{u_3} ι)
  (ordinary_subset : ordinary ⊆ support) (digit : ι → ℕ) (minimum : A)
  (minimum_ordinary : HeckeSkeleton.LowFrozenCube.PrimeCoordinates.Supported.{u_3, u_4} coords ordinary minimum),
  Eq.{1}
    (SizeOf.sizeOf.{max (u_3 + 1) (u_4 + 1)}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mk.{u_3, u_4} coords symbol sixth reciprocal support ordinary
        ordinary_subset digit minimum minimum_ordinary))
    (HAdd.hAdd.{0, 0, 0}
      (HAdd.hAdd.{0, 0, 0}
        (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 (SizeOf.sizeOf.{max (u_3 + 1) (u_4 + 1)} coords))
          (SizeOf.sizeOf.{u_3 + 1} support))
        (SizeOf.sizeOf.{u_3 + 1} ordinary))
      (SizeOf.sizeOf.{u_4 + 1} minimum))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.prime.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (p : ι),
  Eq.{u_2 + 1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.prime.{u_1, u_2} D p)
    ((MulEquiv.symm.{u_2, u_1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D))
      (Multiplicative.ofAdd.{u_1} (Finsupp.single.{u_1, 0} p 1)))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawBlockSourceEnergy.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ) (pow sup : A) (rows marks columns : Finset.{u_2} A)
  (inputs : Finset.{u_2} (Prod.{u_2, u_2} A A)),
  Eq.{1}
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawBlockSourceEnergy.{u_1, u_2} D normI first prefactor atZero
      phase a₀ ρ₀ lam pow sup rows marks columns inputs)
    (∑
      k ∈
        HeckeSkeleton.LowFrozenCube.PrimeCoordinates.rowBlock.{u_1, u_2}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) pow sup rows,
      HPow.hPow.{0, 0, 0}
        (Norm.norm.{0}
          (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceRow.{u_1, u_2} D normI first prefactor atZero phase
            a₀ ρ₀ lam marks columns inputs
            (HeckeSkeleton.LowFrozenCube.PrimeCoordinates.residualRowFactor.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.support.{u_1, u_2} D) k)))
        2)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceTerm.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ) (d P c a n : A),
  Eq.{1}
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawSourceTerm.{u_1, u_2} D normI first prefactor atZero phase a₀
      ρ₀ lam d P c a n)
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0}
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0}
            (HDiv.hDiv.{0, 0, 0}
              (HeckeSkeleton.LowFrozenCube.markCoefficient.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinarySymbol.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D)
                (⇑(HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) a))
                a₀ a P)
              ↑√(normI P))
            (HeckeSkeleton.LowFrozenCube.rowCoefficient.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinarySymbol.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D)
              (⇑(HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                  (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) a))
              ρ₀ a d))
          (HeckeSkeleton.LowFrozenCube.columnCoefficient.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinarySymbol.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D)
            (⇑(HeckeSkeleton.LowFrozenCube.PrimeCoordinates.valuation.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.coords.{u_1, u_2} D) a))
            lam a c))
        (HDiv.hDiv.{0, 0, 0}
          (HMul.hMul.{0, 0, 0} (phase c a n)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawTable.{u_1, u_2} D normI first prefactor atZero a))
          ↑(normI n)))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mixedPhase.{u_1, u_2} D d P c n))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceRow.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
  (Ω : A → A → A → ℂ) (marks columns : Finset.{u_2} A) (pairs : Finset.{u_2} (Prod.{u_2, u_2} A A)) (d : A),
  Eq.{1}
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceRow.{u_1, u_2} D normI a₀ ρ₀ lam Ω marks columns pairs d)
    (∑ P ∈ marks,
      ∑ c ∈ columns,
        ∑ q ∈ pairs,
          HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceTerm.{u_1, u_2} D normI a₀ ρ₀ lam Ω d P c q.1 q.2)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceTerm.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
  (Ω : A → A → A → ℂ) (d P c x n : A),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.sourceTerm.{u_1, u_2} D normI a₀ ρ₀ lam Ω d P c x n)
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0}
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0}
            (HDiv.hDiv.{0, 0, 0}
              (HeckeSkeleton.LowFrozenCube.markCoefficient.{u_1, u_2}
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinarySymbol.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D)
                (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.exponents.{u_1, u_2} D x) a₀
                (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D)
                  (HPow.hPow.{u_2, 0, u_2} x 3))
                P)
              ↑√(normI P))
            (HeckeSkeleton.LowFrozenCube.rowCoefficient.{u_1, u_2}
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinarySymbol.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D)
              (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.exponents.{u_1, u_2} D x) ρ₀
              (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D)
                (HPow.hPow.{u_2, 0, u_2} x 3))
              d))
          (HeckeSkeleton.LowFrozenCube.columnCoefficient.{u_1, u_2}
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.symbol.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinary.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.ordinarySymbol.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.digit.{u_1, u_2} D)
            (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.exponents.{u_1, u_2} D x) lam
            (HMul.hMul.{u_2, u_2, u_2} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.minimum.{u_1, u_2} D)
              (HPow.hPow.{u_2, 0, u_2} x 3))
            c))
        (HDiv.hDiv.{0, 0, 0} (Ω c x n) ↑(normI n)))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.mixedPhase.{u_1, u_2} D d P c n))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ) (lam : A → ℂ)
  (Ω : A → A → A → ℂ) (B C : ℝ) (c b : A),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.unitBeta.{u_1, u_2} D normI lam Ω B C c b)
    (HeckeSkeleton.LowFrozenCube.normalizedCubeCoefficient B C
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.beta.{u_1, u_2} D normI lam Ω c b))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.energy.eq_1

```lean
∀ {ι : Type u_1} {A : Type u_2} [inst : CommMonoid.{u_2} A]
  (b : HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.{u_1, u_2} ι A)
  (D : HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.{u_1, u_2} ι A) (normI : A → ℝ),
  Eq.{1} (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.energy.{u_1, u_2} b D normI)
    (HeckeSkeleton.LowFrozenCube.FrozenReduction.Data.rawBlockSourceEnergy.{u_1, u_2} D normI
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.first.{u_1, u_2} b)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.prefactor.{u_1, u_2} b)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.atZero.{u_1, u_2} b)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.phase.{u_1, u_2} b)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.a₀.{u_1, u_2} b)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.ρ₀.{u_1, u_2} b)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.annularColumn.{u_2} normI
        (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.lam.{u_1, u_2} b))
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.pow.{u_1, u_2} b)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.sup.{u_1, u_2} b)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.rows.{u_1, u_2} b)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.marks.{u_1, u_2} b)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.columns.{u_1, u_2} b)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.inputs.{u_1, u_2} b))
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.mk.inj

```lean
∀ {ι : Type u_3} {A : Type u_4} {first prefactor : ι → ℂ} {atZero : ι → ℕ → ℂ} {phase : A → A → A → ℂ}
  {a₀ ρ₀ lam : A → ℂ} {pow sup : A} {rows marks columns : Finset.{u_4} A} {inputs : Finset.{u_4} (Prod.{u_4, u_4} A A)}
  {first_1 prefactor_1 : ι → ℂ} {atZero_1 : ι → ℕ → ℂ} {phase_1 : A → A → A → ℂ} {a₀_1 ρ₀_1 lam_1 : A → ℂ}
  {pow_1 sup_1 : A} {rows_1 marks_1 columns_1 : Finset.{u_4} A} {inputs_1 : Finset.{u_4} (Prod.{u_4, u_4} A A)},
  Eq.{max (u_3 + 1) (u_4 + 1)}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.mk.{u_3, u_4} first prefactor atZero phase a₀ ρ₀ lam pow
        sup rows marks columns inputs)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.mk.{u_3, u_4} first_1 prefactor_1 atZero_1 phase_1 a₀_1
        ρ₀_1 lam_1 pow_1 sup_1 rows_1 marks_1 columns_1 inputs_1) →
    Eq.{u_3 + 1} first first_1 ∧
      Eq.{u_3 + 1} prefactor prefactor_1 ∧
        Eq.{u_3 + 1} atZero atZero_1 ∧
          Eq.{u_4 + 1} phase phase_1 ∧
            Eq.{u_4 + 1} a₀ a₀_1 ∧
              Eq.{u_4 + 1} ρ₀ ρ₀_1 ∧
                Eq.{u_4 + 1} lam lam_1 ∧
                  Eq.{u_4 + 1} pow pow_1 ∧
                    Eq.{u_4 + 1} sup sup_1 ∧
                      Eq.{u_4 + 1} rows rows_1 ∧
                        Eq.{u_4 + 1} marks marks_1 ∧ Eq.{u_4 + 1} columns columns_1 ∧ Eq.{u_4 + 1} inputs inputs_1
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.mk.injEq

```lean
∀ {ι : Type u_3} {A : Type u_4} (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
  (a₀ ρ₀ lam : A → ℂ) (pow sup : A) (rows marks columns : Finset.{u_4} A) (inputs : Finset.{u_4} (Prod.{u_4, u_4} A A))
  (first_1 prefactor_1 : ι → ℂ) (atZero_1 : ι → ℕ → ℂ) (phase_1 : A → A → A → ℂ) (a₀_1 ρ₀_1 lam_1 : A → ℂ)
  (pow_1 sup_1 : A) (rows_1 marks_1 columns_1 : Finset.{u_4} A) (inputs_1 : Finset.{u_4} (Prod.{u_4, u_4} A A)),
  Eq.{1}
    (Eq.{max (u_3 + 1) (u_4 + 1)}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.mk.{u_3, u_4} first prefactor atZero phase a₀ ρ₀ lam pow
        sup rows marks columns inputs)
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.mk.{u_3, u_4} first_1 prefactor_1 atZero_1 phase_1 a₀_1
        ρ₀_1 lam_1 pow_1 sup_1 rows_1 marks_1 columns_1 inputs_1))
    (Eq.{u_3 + 1} first first_1 ∧
      Eq.{u_3 + 1} prefactor prefactor_1 ∧
        Eq.{u_3 + 1} atZero atZero_1 ∧
          Eq.{u_4 + 1} phase phase_1 ∧
            Eq.{u_4 + 1} a₀ a₀_1 ∧
              Eq.{u_4 + 1} ρ₀ ρ₀_1 ∧
                Eq.{u_4 + 1} lam lam_1 ∧
                  Eq.{u_4 + 1} pow pow_1 ∧
                    Eq.{u_4 + 1} sup sup_1 ∧
                      Eq.{u_4 + 1} rows rows_1 ∧
                        Eq.{u_4 + 1} marks marks_1 ∧ Eq.{u_4 + 1} columns columns_1 ∧ Eq.{u_4 + 1} inputs inputs_1)
```

## HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.mk.sizeOf_spec

```lean
∀ {ι : Type u_3} {A : Type u_4} [inst : SizeOf.{u_3 + 1} ι] [inst_1 : SizeOf.{u_4 + 1} A] (first prefactor : ι → ℂ)
  (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ) (pow sup : A) (rows marks columns : Finset.{u_4} A)
  (inputs : Finset.{u_4} (Prod.{u_4, u_4} A A)),
  Eq.{1}
    (SizeOf.sizeOf.{max (u_3 + 1) (u_4 + 1)}
      (HeckeSkeleton.LowFrozenCube.FrozenReduction.SourceBlock.mk.{u_3, u_4} first prefactor atZero phase a₀ ρ₀ lam pow
        sup rows marks columns inputs))
    (HAdd.hAdd.{0, 0, 0}
      (HAdd.hAdd.{0, 0, 0}
        (HAdd.hAdd.{0, 0, 0}
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 (SizeOf.sizeOf.{u_4 + 1} pow)) (SizeOf.sizeOf.{u_4 + 1} sup))
            (SizeOf.sizeOf.{u_4 + 1} rows))
          (SizeOf.sizeOf.{u_4 + 1} marks))
        (SizeOf.sizeOf.{u_4 + 1} columns))
      (SizeOf.sizeOf.{u_4 + 1} inputs))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.box

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (d : I),
      Membership.mem.{u_1, u_1} ds d →
        ∀ (r : I),
          Membership.mem.{u_1, u_1} rs r →
            HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_1} S
                (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) r ⊆
              HeckeSkeleton.LowHybrid.NormalForm.completedBox.{u_1} (ts d r) (cs d r) (ms d r) (hs d r)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.c_harmonic

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (d : I),
      Membership.mem.{u_1, u_1} ds d →
        ∀ (r : I),
          Membership.mem.{u_1, u_1} rs r →
            LE.le.{0}
              (∑ c ∈ cs d r, HDiv.hDiv.{0, 0, 0} 1 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S c)) Hc
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.cubic_completion

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (d : I),
      Membership.mem.{u_1, u_1} ds d →
        ∀ (r : I),
          Membership.mem.{u_1, u_1} rs r →
            ∀ (v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I),
              Membership.mem.{u_1, u_1}
                  (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_1} S
                    (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) r)
                  v →
                Membership.mem.{u_1, u_1} (goodMC d r) (Prod.mk.{u_1, u_1} v.2.2.1 v.2.1)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.cubic_fibers

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (d : I),
      Membership.mem.{u_1, u_1} ds d →
        ∀ (r : I),
          Membership.mem.{u_1, u_1} rs r →
            ∀ (j : I),
              Membership.mem.{u_1, u_1} jset j →
                LE.le.{0} (↑(Finset.card.{u_1} ({u ∈ goodMC d r | Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} u.2 u.1) j})))
                  Dc
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.cubic_products

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (d : I),
      Membership.mem.{u_1, u_1} ds d →
        ∀ (r : I),
          Membership.mem.{u_1, u_1} rs r →
            ∀ (u : Prod.{u_1, u_1} I I),
              Membership.mem.{u_1, u_1} (goodMC d r) u →
                Membership.mem.{u_1, u_1} jset (HMul.hMul.{u_1, u_1, u_1} u.2 u.1)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.cubic_rectangle

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (d : I),
      Membership.mem.{u_1, u_1} ds d →
        ∀ (r : I), Membership.mem.{u_1, u_1} rs r → goodMC d r ⊆ SProd.sprod.{u_1, u_1, u_1} (ms d r) (cs d r)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.cubic_support

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (j : I),
      Membership.mem.{u_1, u_1} jset j →
        sf j ∧ LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S j) N
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.h_harmonic

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (d : I),
      Membership.mem.{u_1, u_1} ds d →
        ∀ (r : I),
          Membership.mem.{u_1, u_1} rs r →
            LE.le.{0}
              (∑ h ∈ hs d r, HDiv.hDiv.{0, 0, 0} 1 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S h)) Hh
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.local_pairs

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (k : I),
      Membership.mem.{u_1, u_1} rows k →
        HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisorPairs.{u_1} S k ⊆ SProd.sprod.{u_1, u_1, u_1} ds rs
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.mark_columns

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (d : I),
      Membership.mem.{u_1, u_1} ds d →
        ∀ (p : I),
          Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.markQuotients.{u_1} S marks d) p →
            sf p ∧ LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S p) L
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.pair_count

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (k : I),
      Membership.mem.{u_1, u_1} rows k →
        LE.le.{0} (↑(Finset.card.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisorPairs.{u_1} S k))) Delta
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.quadratic_completion

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (d : I),
      Membership.mem.{u_1, u_1} ds d →
        ∀ (r : I),
          Membership.mem.{u_1, u_1} rs r →
            ∀ (v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I),
              Membership.mem.{u_1, u_1}
                  (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_1} S
                    (HeckeSkeleton.LowHybrid.NormalForm.Completion.support.{u_1} C) r)
                  v →
                Membership.mem.{u_1, u_1} (goodPairs d r) (Prod.mk.{u_1, u_1} v.2.2.1 v.2.2.2)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.quadratic_fibers

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (d : I),
      Membership.mem.{u_1, u_1} ds d →
        ∀ (r : I),
          Membership.mem.{u_1, u_1} rs r →
            ∀ (j : I),
              Membership.mem.{u_1, u_1} qset j →
                LE.le.{0}
                  (↑(Finset.card.{u_1} ({u ∈ goodPairs d r | Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} u.1 u.2) j}))) Dq
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.quadratic_products

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (d : I),
      Membership.mem.{u_1, u_1} ds d →
        ∀ (r : I),
          Membership.mem.{u_1, u_1} rs r →
            ∀ (u : Prod.{u_1, u_1} I I),
              Membership.mem.{u_1, u_1} (goodPairs d r) u →
                Membership.mem.{u_1, u_1} qset (HMul.hMul.{u_1, u_1, u_1} u.1 u.2)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.quadratic_rectangle

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (d : I),
      Membership.mem.{u_1, u_1} ds d →
        ∀ (r : I), Membership.mem.{u_1, u_1} rs r → goodPairs d r ⊆ SProd.sprod.{u_1, u_1, u_1} (ms d r) (hs d r)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.quadratic_support

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (j : I),
      Membership.mem.{u_1, u_1} qset j →
        sf j ∧ LE.le.{0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S j) Y
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.quotient_rows

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (d : I),
      Membership.mem.{u_1, u_1} ds d →
        ∀ (r : I),
          Membership.mem.{u_1, u_1} rs r →
            ∀ (k : I),
              Membership.mem.{u_1, u_1} rows k →
                Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisorPairs.{u_1} S k)
                    (Prod.mk.{u_1, u_1} d r) →
                  sf (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotientTwice.{u_1} S d r k) ∧
                    LE.le.{0}
                      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S
                        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotientTwice.{u_1} S d r k))
                      K
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.t_harmonic

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I}
  {sf : I → Prop} {rows marks columns cubes ds rs : Finset.{u_1} I}
  {C : HeckeSkeleton.LowHybrid.NormalForm.Completion.{u_1} columns cubes} {ts cs ms hs : I → I → Finset.{u_1} I}
  {goodPairs goodMC : I → I → Finset.{u_1} (Prod.{u_1, u_1} I I)} {qset jset : Finset.{u_1} I}
  {K Y N L Delta Dq Dc Ht Hc Hh : ℝ},
  HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.FiniteInputs.{u_1} S sf rows marks columns cubes ds rs C ts cs ms hs
      goodPairs goodMC qset jset K Y N L Delta Dq Dc Ht Hc Hh →
    ∀ (d : I),
      Membership.mem.{u_1, u_1} ds d →
        ∀ (r : I),
          Membership.mem.{u_1, u_1} rs r →
            LE.le.{0}
              (∑ t ∈ ts d r, HDiv.hDiv.{0, 0, 0} 1 (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S t)) Ht
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockA.eq_1

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (d r t h p : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockA.{u_1} S a d r t h p)
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0}
        (HDiv.hDiv.{0, 0, 0} (a (HMul.hMul.{u_1, u_1, u_1} d p))
          ↑√(HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S p))
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S p r))
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S p (HMul.hMul.{u_1, u_1, u_1} h t)))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockBeta.eq_1

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (beta : I → I → ℂ) (support : Finset.{u_1} (HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I))
  (d r t c m h : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockBeta.{u_1} S beta support d r t c m h)
    (ite.{1}
      (Membership.mem.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport.{u_1} S support r)
        (Prod.mk.{u_1, u_1} t (Prod.mk.{u_1, u_1} c (Prod.mk.{u_1, u_1} m h))))
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockBetaCore.{u_1} S beta d r t c m h) 0)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockColumn.eq_1

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (marks : Finset.{u_1} I) (d r t c m h : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockColumn.{u_1} S a marks d r t c m h)
    (∑ p ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.markQuotients.{u_1} S marks d,
      HMul.hMul.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockA.{u_1} S a d r t h p)
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S p (HMul.hMul.{u_1, u_1, u_1} c m)))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.blockSupport_original_mem._simp_1_1

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  Eq.{1} (Membership.mem.{max u_1 u_2, max u_1 u_2} (SProd.sprod.{u_1, u_2, max u_1 u_2} s t) p)
    (Membership.mem.{u_1, u_1} s p.1 ∧ Membership.mem.{u_2, u_2} t p.2)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.columnMass.eq_1

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I)
  (a : I → ℂ) (marks : Finset.{u_1} I) (d : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.columnMass.{u_1} S a marks d)
    (∑ p ∈ HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.markQuotients.{u_1} S marks d,
      HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (a (HMul.hMul.{u_1, u_1, u_1} d p))) 2)
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S p))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.eq_1

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (x y : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cubic.{u_1} S x y)
    (HPow.hPow.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_1} S x y) (-2))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisorPairs.eq_1

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (k : I),
  Eq.{u_1 + 1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisorPairs.{u_1} S k)
    (Finset.biUnion.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S k) fun d =>
      Finset.image.{u_1, u_1} (fun r => Prod.mk.{u_1, u_1} d r)
        (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.divisors.{u_1} S
          (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S d k)))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.eq_1

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (x y : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mask.{u_1} S x y)
    (ite.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.cop.{u_1} S x y) 1 0)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mem_divisorPairs._simp_1_2

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : α → Finset.{u_2} β} [inst : DecidableEq.{u_2 + 1} β]
  {b : β},
  Eq.{1} (Membership.mem.{u_2, u_2} (Finset.biUnion.{u_1, u_2} s t) b)
    (∃ a, Membership.mem.{u_1, u_1} s a ∧ Membership.mem.{u_2, u_2} (t a) b)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mem_divisorPairs._simp_1_3

```lean
∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq.{u_2 + 1} β] {f : α → β} {s : Finset.{u_1} α} {b : β},
  Eq.{1} (Membership.mem.{u_2, u_2} (Finset.image.{u_1, u_2} f s) b)
    (∃ a, Membership.mem.{u_1, u_1} s a ∧ Eq.{u_2 + 1} (f a) b)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mk.inj

```lean
∀ {I : Type u_2} {inst : CommMonoid.{u_2} I} {normI : I → ℝ} {norm_nonneg : ∀ (x : I), LE.le.{0} 0 (normI x)}
  {norm_mul : ∀ (x y : I), Eq.{1} (normI (HMul.hMul.{u_2, u_2, u_2} x y)) (HMul.hMul.{0, 0, 0} (normI x) (normI y))}
  {symbol : I → I → ℂ}
  {symbol_mul_left :
    ∀ (x y z : I), Eq.{1} (symbol (HMul.hMul.{u_2, u_2, u_2} x y) z) (HMul.hMul.{0, 0, 0} (symbol x z) (symbol y z))}
  {symbol_mul_right :
    ∀ (x y z : I), Eq.{1} (symbol x (HMul.hMul.{u_2, u_2, u_2} y z)) (HMul.hMul.{0, 0, 0} (symbol x y) (symbol x z))}
  {cop : I → I → Prop} {cop_symm : ∀ (x y : I), cop x y ↔ cop y x}
  {cop_mul_left : ∀ (x y z : I), cop (HMul.hMul.{u_2, u_2, u_2} x y) z ↔ cop x z ∧ cop y z}
  {cop_mul_right : ∀ (x y z : I), cop x (HMul.hMul.{u_2, u_2, u_2} y z) ↔ cop x y ∧ cop x z}
  {six : ∀ (x y : I), Eq.{1} (HPow.hPow.{0, 0, 0} (symbol x y) 6) (ite.{1} (cop x y) 1 0)}
  {divisors : I → Finset.{u_2} I} {mu : I → ℂ} {quotient : I → I → I}
  {divisor_dvd : ∀ (x d : I), Membership.mem.{u_2, u_2} (divisors x) d → Dvd.dvd.{u_2} d x}
  {quotient_spec : ∀ (d x : I), Dvd.dvd.{u_2} d x → Eq.{u_2 + 1} (HMul.hMul.{u_2, u_2, u_2} d (quotient d x)) x}
  {mobius_expansion :
    ∀ (p k : I), Eq.{1} (ite.{1} (cop p k) 1 0) (∑ d ∈ divisors k, ite.{1} (Dvd.dvd.{u_2} d p) (mu d) 0)}
  {normI_1 : I → ℝ} {norm_nonneg_1 : ∀ (x : I), LE.le.{0} 0 (normI_1 x)}
  {norm_mul_1 :
    ∀ (x y : I), Eq.{1} (normI_1 (HMul.hMul.{u_2, u_2, u_2} x y)) (HMul.hMul.{0, 0, 0} (normI_1 x) (normI_1 y))}
  {symbol_1 : I → I → ℂ}
  {symbol_mul_left_1 :
    ∀ (x y z : I),
      Eq.{1} (symbol_1 (HMul.hMul.{u_2, u_2, u_2} x y) z) (HMul.hMul.{0, 0, 0} (symbol_1 x z) (symbol_1 y z))}
  {symbol_mul_right_1 :
    ∀ (x y z : I),
      Eq.{1} (symbol_1 x (HMul.hMul.{u_2, u_2, u_2} y z)) (HMul.hMul.{0, 0, 0} (symbol_1 x y) (symbol_1 x z))}
  {cop_1 : I → I → Prop} {cop_symm_1 : ∀ (x y : I), cop_1 x y ↔ cop_1 y x}
  {cop_mul_left_1 : ∀ (x y z : I), cop_1 (HMul.hMul.{u_2, u_2, u_2} x y) z ↔ cop_1 x z ∧ cop_1 y z}
  {cop_mul_right_1 : ∀ (x y z : I), cop_1 x (HMul.hMul.{u_2, u_2, u_2} y z) ↔ cop_1 x y ∧ cop_1 x z}
  {six_1 : ∀ (x y : I), Eq.{1} (HPow.hPow.{0, 0, 0} (symbol_1 x y) 6) (ite.{1} (cop_1 x y) 1 0)}
  {divisors_1 : I → Finset.{u_2} I} {mu_1 : I → ℂ} {quotient_1 : I → I → I}
  {divisor_dvd_1 : ∀ (x d : I), Membership.mem.{u_2, u_2} (divisors_1 x) d → Dvd.dvd.{u_2} d x}
  {quotient_spec_1 : ∀ (d x : I), Dvd.dvd.{u_2} d x → Eq.{u_2 + 1} (HMul.hMul.{u_2, u_2, u_2} d (quotient_1 d x)) x}
  {mobius_expansion_1 :
    ∀ (p k : I), Eq.{1} (ite.{1} (cop_1 p k) 1 0) (∑ d ∈ divisors_1 k, ite.{1} (Dvd.dvd.{u_2} d p) (mu_1 d) 0)},
  Eq.{u_2 + 1}
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mk.{u_2} normI norm_nonneg norm_mul symbol symbol_mul_left
        symbol_mul_right cop cop_symm cop_mul_left cop_mul_right six divisors mu quotient divisor_dvd quotient_spec
        mobius_expansion)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mk.{u_2} normI_1 norm_nonneg_1 norm_mul_1 symbol_1
        symbol_mul_left_1 symbol_mul_right_1 cop_1 cop_symm_1 cop_mul_left_1 cop_mul_right_1 six_1 divisors_1 mu_1
        quotient_1 divisor_dvd_1 quotient_spec_1 mobius_expansion_1) →
    Eq.{u_2 + 1} normI normI_1 ∧
      Eq.{u_2 + 1} symbol symbol_1 ∧
        Eq.{u_2 + 1} cop cop_1 ∧
          Eq.{u_2 + 1} divisors divisors_1 ∧ Eq.{u_2 + 1} mu mu_1 ∧ Eq.{u_2 + 1} quotient quotient_1
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mk.injEq

```lean
∀ {I : Type u_2} [inst : CommMonoid.{u_2} I] (normI : I → ℝ) (norm_nonneg : ∀ (x : I), LE.le.{0} 0 (normI x))
  (norm_mul : ∀ (x y : I), Eq.{1} (normI (HMul.hMul.{u_2, u_2, u_2} x y)) (HMul.hMul.{0, 0, 0} (normI x) (normI y)))
  (symbol : I → I → ℂ)
  (symbol_mul_left :
    ∀ (x y z : I), Eq.{1} (symbol (HMul.hMul.{u_2, u_2, u_2} x y) z) (HMul.hMul.{0, 0, 0} (symbol x z) (symbol y z)))
  (symbol_mul_right :
    ∀ (x y z : I), Eq.{1} (symbol x (HMul.hMul.{u_2, u_2, u_2} y z)) (HMul.hMul.{0, 0, 0} (symbol x y) (symbol x z)))
  (cop : I → I → Prop) (cop_symm : ∀ (x y : I), cop x y ↔ cop y x)
  (cop_mul_left : ∀ (x y z : I), cop (HMul.hMul.{u_2, u_2, u_2} x y) z ↔ cop x z ∧ cop y z)
  (cop_mul_right : ∀ (x y z : I), cop x (HMul.hMul.{u_2, u_2, u_2} y z) ↔ cop x y ∧ cop x z)
  (six : ∀ (x y : I), Eq.{1} (HPow.hPow.{0, 0, 0} (symbol x y) 6) (ite.{1} (cop x y) 1 0))
  (divisors : I → Finset.{u_2} I) (mu : I → ℂ) (quotient : I → I → I)
  (divisor_dvd : ∀ (x d : I), Membership.mem.{u_2, u_2} (divisors x) d → Dvd.dvd.{u_2} d x)
  (quotient_spec : ∀ (d x : I), Dvd.dvd.{u_2} d x → Eq.{u_2 + 1} (HMul.hMul.{u_2, u_2, u_2} d (quotient d x)) x)
  (mobius_expansion :
    ∀ (p k : I), Eq.{1} (ite.{1} (cop p k) 1 0) (∑ d ∈ divisors k, ite.{1} (Dvd.dvd.{u_2} d p) (mu d) 0))
  (normI_1 : I → ℝ) (norm_nonneg_1 : ∀ (x : I), LE.le.{0} 0 (normI_1 x))
  (norm_mul_1 :
    ∀ (x y : I), Eq.{1} (normI_1 (HMul.hMul.{u_2, u_2, u_2} x y)) (HMul.hMul.{0, 0, 0} (normI_1 x) (normI_1 y)))
  (symbol_1 : I → I → ℂ)
  (symbol_mul_left_1 :
    ∀ (x y z : I),
      Eq.{1} (symbol_1 (HMul.hMul.{u_2, u_2, u_2} x y) z) (HMul.hMul.{0, 0, 0} (symbol_1 x z) (symbol_1 y z)))
  (symbol_mul_right_1 :
    ∀ (x y z : I),
      Eq.{1} (symbol_1 x (HMul.hMul.{u_2, u_2, u_2} y z)) (HMul.hMul.{0, 0, 0} (symbol_1 x y) (symbol_1 x z)))
  (cop_1 : I → I → Prop) (cop_symm_1 : ∀ (x y : I), cop_1 x y ↔ cop_1 y x)
  (cop_mul_left_1 : ∀ (x y z : I), cop_1 (HMul.hMul.{u_2, u_2, u_2} x y) z ↔ cop_1 x z ∧ cop_1 y z)
  (cop_mul_right_1 : ∀ (x y z : I), cop_1 x (HMul.hMul.{u_2, u_2, u_2} y z) ↔ cop_1 x y ∧ cop_1 x z)
  (six_1 : ∀ (x y : I), Eq.{1} (HPow.hPow.{0, 0, 0} (symbol_1 x y) 6) (ite.{1} (cop_1 x y) 1 0))
  (divisors_1 : I → Finset.{u_2} I) (mu_1 : I → ℂ) (quotient_1 : I → I → I)
  (divisor_dvd_1 : ∀ (x d : I), Membership.mem.{u_2, u_2} (divisors_1 x) d → Dvd.dvd.{u_2} d x)
  (quotient_spec_1 : ∀ (d x : I), Dvd.dvd.{u_2} d x → Eq.{u_2 + 1} (HMul.hMul.{u_2, u_2, u_2} d (quotient_1 d x)) x)
  (mobius_expansion_1 :
    ∀ (p k : I), Eq.{1} (ite.{1} (cop_1 p k) 1 0) (∑ d ∈ divisors_1 k, ite.{1} (Dvd.dvd.{u_2} d p) (mu_1 d) 0)),
  Eq.{1}
    (Eq.{u_2 + 1}
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mk.{u_2} normI norm_nonneg norm_mul symbol symbol_mul_left
        symbol_mul_right cop cop_symm cop_mul_left cop_mul_right six divisors mu quotient divisor_dvd quotient_spec
        mobius_expansion)
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mk.{u_2} normI_1 norm_nonneg_1 norm_mul_1 symbol_1
        symbol_mul_left_1 symbol_mul_right_1 cop_1 cop_symm_1 cop_mul_left_1 cop_mul_right_1 six_1 divisors_1 mu_1
        quotient_1 divisor_dvd_1 quotient_spec_1 mobius_expansion_1))
    (Eq.{u_2 + 1} normI normI_1 ∧
      Eq.{u_2 + 1} symbol symbol_1 ∧
        Eq.{u_2 + 1} cop cop_1 ∧
          Eq.{u_2 + 1} divisors divisors_1 ∧ Eq.{u_2 + 1} mu mu_1 ∧ Eq.{u_2 + 1} quotient quotient_1)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mk.sizeOf_spec

```lean
∀ {I : Type u_2} [inst : CommMonoid.{u_2} I] [inst_1 : SizeOf.{u_2 + 1} I] (normI : I → ℝ)
  (norm_nonneg : ∀ (x : I), LE.le.{0} 0 (normI x))
  (norm_mul : ∀ (x y : I), Eq.{1} (normI (HMul.hMul.{u_2, u_2, u_2} x y)) (HMul.hMul.{0, 0, 0} (normI x) (normI y)))
  (symbol : I → I → ℂ)
  (symbol_mul_left :
    ∀ (x y z : I), Eq.{1} (symbol (HMul.hMul.{u_2, u_2, u_2} x y) z) (HMul.hMul.{0, 0, 0} (symbol x z) (symbol y z)))
  (symbol_mul_right :
    ∀ (x y z : I), Eq.{1} (symbol x (HMul.hMul.{u_2, u_2, u_2} y z)) (HMul.hMul.{0, 0, 0} (symbol x y) (symbol x z)))
  (cop : I → I → Prop) (cop_symm : ∀ (x y : I), cop x y ↔ cop y x)
  (cop_mul_left : ∀ (x y z : I), cop (HMul.hMul.{u_2, u_2, u_2} x y) z ↔ cop x z ∧ cop y z)
  (cop_mul_right : ∀ (x y z : I), cop x (HMul.hMul.{u_2, u_2, u_2} y z) ↔ cop x y ∧ cop x z)
  (six : ∀ (x y : I), Eq.{1} (HPow.hPow.{0, 0, 0} (symbol x y) 6) (ite.{1} (cop x y) 1 0))
  (divisors : I → Finset.{u_2} I) (mu : I → ℂ) (quotient : I → I → I)
  (divisor_dvd : ∀ (x d : I), Membership.mem.{u_2, u_2} (divisors x) d → Dvd.dvd.{u_2} d x)
  (quotient_spec : ∀ (d x : I), Dvd.dvd.{u_2} d x → Eq.{u_2 + 1} (HMul.hMul.{u_2, u_2, u_2} d (quotient d x)) x)
  (mobius_expansion :
    ∀ (p k : I), Eq.{1} (ite.{1} (cop p k) 1 0) (∑ d ∈ divisors k, ite.{1} (Dvd.dvd.{u_2} d p) (mu d) 0)),
  Eq.{1}
    (SizeOf.sizeOf.{u_2 + 1}
      (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.mk.{u_2} normI norm_nonneg norm_mul symbol symbol_mul_left
        symbol_mul_right cop cop_symm cop_mul_left cop_mul_right six divisors mu quotient divisor_dvd quotient_spec
        mobius_expansion))
    1
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.norm_blockBeta_le_one._simp_1_1

```lean
∀ {α : Type u_1} [inst : Zero.{u_1} α] [inst_1 : One.{u_1} α] [inst_2 : LE.{u_1} α] [ZeroLEOneClass.{u_1} α],
  Eq.{1} (LE.le.{u_1} 0 1) True
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.eq_1

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (x y : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quadratic.{u_1} S x y)
    (HPow.hPow.{0, 0, 0} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.symbol.{u_1} S x y) 3)
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotientCommon.eq_1

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (r : I)
  (v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I),
  Eq.{u_1 + 1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotientCommon.{u_1} S r v)
    (Prod.mk.{u_1, u_1} v.1
      (Prod.mk.{u_1, u_1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.quotient.{u_1} S r v.2.1)
        (Prod.mk.{u_1, u_1} v.2.2.1 v.2.2.2)))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.restoreCommon.eq_1

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (_S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (r : I)
  (v : HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I),
  Eq.{u_1 + 1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.restoreCommon.{u_1} _S r v)
    (Prod.mk.{u_1, u_1} v.1
      (Prod.mk.{u_1, u_1} (HMul.hMul.{u_1, u_1, u_1} r v.2.1) (Prod.mk.{u_1, u_1} v.2.2.1 v.2.2.2)))
```

## HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.weight.eq_1

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] (S : HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.{u_1} I) (d : I),
  Eq.{1} (HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.weight.{u_1} S d)
    (Inv.inv.{0} ↑√(HeckeSkeleton.LowHybrid.NormalForm.Arithmetic.normI.{u_1} S d))
```

## HeckeSkeleton.LowHybrid.NormalForm.Completion.mk.inj

```lean
∀ {I : Type u_1} {inst : CommMonoid.{u_1} I} {columns cubes : Finset.{u_1} I}
  {split : Prod.{u_1, u_1} I I → HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I}
  {reconstruct :
    ∀ (x : Prod.{u_1, u_1} I I),
      Membership.mem.{u_1, u_1} (SProd.sprod.{u_1, u_1, u_1} columns cubes) x →
        Eq.{u_1 + 1} (HeckeSkeleton.LowHybrid.NormalForm.recombine.{u_1} (split x)) x}
  {split_1 : Prod.{u_1, u_1} I I → HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I}
  {reconstruct_1 :
    ∀ (x : Prod.{u_1, u_1} I I),
      Membership.mem.{u_1, u_1} (SProd.sprod.{u_1, u_1, u_1} columns cubes) x →
        Eq.{u_1 + 1} (HeckeSkeleton.LowHybrid.NormalForm.recombine.{u_1} (split_1 x)) x},
  Eq.{u_1 + 1} (HeckeSkeleton.LowHybrid.NormalForm.Completion.mk.{u_1} split reconstruct)
      (HeckeSkeleton.LowHybrid.NormalForm.Completion.mk.{u_1} split_1 reconstruct_1) →
    Eq.{u_1 + 1} split split_1
```

## HeckeSkeleton.LowHybrid.NormalForm.Completion.mk.injEq

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {columns cubes : Finset.{u_1} I}
  (split : Prod.{u_1, u_1} I I → HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I)
  (reconstruct :
    ∀ (x : Prod.{u_1, u_1} I I),
      Membership.mem.{u_1, u_1} (SProd.sprod.{u_1, u_1, u_1} columns cubes) x →
        Eq.{u_1 + 1} (HeckeSkeleton.LowHybrid.NormalForm.recombine.{u_1} (split x)) x)
  (split_1 : Prod.{u_1, u_1} I I → HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I)
  (reconstruct_1 :
    ∀ (x : Prod.{u_1, u_1} I I),
      Membership.mem.{u_1, u_1} (SProd.sprod.{u_1, u_1, u_1} columns cubes) x →
        Eq.{u_1 + 1} (HeckeSkeleton.LowHybrid.NormalForm.recombine.{u_1} (split_1 x)) x),
  Eq.{1}
    (Eq.{u_1 + 1} (HeckeSkeleton.LowHybrid.NormalForm.Completion.mk.{u_1} split reconstruct)
      (HeckeSkeleton.LowHybrid.NormalForm.Completion.mk.{u_1} split_1 reconstruct_1))
    (Eq.{u_1 + 1} split split_1)
```

## HeckeSkeleton.LowHybrid.NormalForm.Completion.mk.sizeOf_spec

```lean
∀ {I : Type u_1} [inst : CommMonoid.{u_1} I] {columns cubes : Finset.{u_1} I} [inst_1 : SizeOf.{u_1 + 1} I]
  (split : Prod.{u_1, u_1} I I → HeckeSkeleton.LowHybrid.NormalForm.CompletedIndex.{u_1} I)
  (reconstruct :
    ∀ (x : Prod.{u_1, u_1} I I),
      Membership.mem.{u_1, u_1} (SProd.sprod.{u_1, u_1, u_1} columns cubes) x →
        Eq.{u_1 + 1} (HeckeSkeleton.LowHybrid.NormalForm.recombine.{u_1} (split x)) x),
  Eq.{1} (SizeOf.sizeOf.{u_1 + 1} (HeckeSkeleton.LowHybrid.NormalForm.Completion.mk.{u_1} split reconstruct)) 1
```
