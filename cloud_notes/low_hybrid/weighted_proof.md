# 联合加权 Cauchy 消除全部 dyad 的完整证明

## 结论与审核重点

该去 dyad 推导成立。两个移动掩码仍须完整展开；随后对 \((t,c')\) 联合使用权重 \(1/(q_tq_{c'})\) 的 Cauchy，可直接得到目标混合界，无需 \(C,G,T,D,r\) 的 dyad。

唯一必须明确的顺序是：使用
\[
q_tq_{c'}\le \frac{B}{q_rq_hq_t}
\tag{W}
\]
时，正项和仍受原支撑 \(q_b=q_rq_{c'}q_hq_t^2\le B\) 约束。可以先把 \(|\beta_D|^2\) 换成上界，但不能同时删除其继承的索引支撑。应用 (W) 后，才扩大正项范围并合并 \(j=c'm\)。

本文件证明纸面约化，不宣称实际外部理想上的 Lean 接线已经完成。

## 1. 输入和记号

沿用 hybrid_proof.md 中的理想唯一分解、乘法范数、符号乘法及精确零值条件。所有范数至少为 \(1\)，且 \(K,N,B,L\ge1\)。

平方自由行和列满足
\[
q_k\le K,\quad q_n\le N,\quad q_P\le L,
\]
完整立方变量 \(b\) 任意，满足 \(q_b\le B\)。定义
\[
\mathcal A=\sum_P\frac{|a(P)|^2}{q_P},\qquad
\mathcal B=\sup_{n,b}|\beta(n,b)|^2,\qquad M=KNBL,
\]
\[
H(X)=\sum_{q_I\le X}\frac1{q_I},\qquad
\Delta(X)=\max_{q_I\le X}\tau(I).
\]
理想计数及除数界给出 \(H(X)\ll1+\log(2X)\)、
\(\Delta(X)\ll_\eta X^\eta\)。

可以始终用两个统一参数的大筛：

- 二次：行参数 \(K\)，平方自由列参数 \(NB\)；
  给定项目筛若以列为符号分母，先用有限复矩阵转置交换方向；其算子常数不变。该桥在 `Transpose.lean` 中证明，加权主定理已使用它。
- 三次：平方自由行参数 \(N\)，平方自由列参数 \(L\)。

实际较小的商参数也可保留，但目标主界不需要它们；使用统一参数消除了移动参数小于 \(1\) 的空项分支。

## 2. 第一个完整掩码

展开
\[
\mathbf1_{(P,k)=1}=\sum_{D\mid P,\ D\mid k}\mu(D).
\]
对每个原行的除数集作 Cauchy，令 \(P=DQ,\ k=D\kappa\)，得到
\[
E(a,\beta)\le\Delta(K)\sum_D\frac1{q_D}E_D.
\tag{1}
\]
其中
\[
E_D=\sum_\kappa\left|
\sum_{n,b}\alpha_D(n,b)\chi_\kappa(nb)^3\right|^2,
\]
\[
\begin{aligned}
a_D(Q)&=a(DQ)\mathbf1_{(D,Q)=1},\\
\beta_D(n,b)&=\beta(n,b)\chi_D(nb)^3\chi_D(n)^{-2}
                      \mathbf1_{(D,b)=1},\\
F_D(n,b)&=\sum_Q\frac{a_D(Q)}{\sqrt{q_Q}}\chi_Q(n)^{-2}
                      \mathbf1_{(Q,b)=1},\\
\alpha_D(n,b)&=\beta_D(n,b)F_D(n,b),\\
\mathcal A_D&=\sum_Q|a_D(Q)|^2/q_Q.
\end{aligned}
\tag{2}
\]
原 \(P\) 支撑仍保留在 \(a_D\) 中。此时不存在残余的 \((Q,\kappa)\) 掩码。
\(\beta_D\) 与 \(\kappa,Q\) 无关且 \(|\beta_D|^2\le\mathcal B\)。

## 3. 分解完整立方，展开第二个完整掩码

唯一写
\[
b=gt^2,\qquad c=(n,g),\qquad n=cm,\quad g=ch.
\]
这里 \(g\) 平方自由，\(c,m,h\) 两两互素且平方自由；\(g,t\) 可以共享素因子。精确等式为
\[
\chi_\kappa(nb)^3=\chi_\kappa(mh)^3\mathbf1_{(\kappa,ct)=1}.
\]

保留 \((\kappa,t)\) 掩码，展开整个 \((\kappa,c)\) 掩码。对每行的 \(r\mid\kappa\) 作 Cauchy，再令
\[
\kappa=r\lambda,\qquad c=rc'.
\]
这一步付出第二个 \(\Delta(K)\)，其余是
\[
\sum_r\sum_\lambda\left|
\sum_{t,c'}\mathbf1_{(r\lambda,t)=1}
\sum_{m,h}\alpha_D(rc'm,rc'ht^2)
  \chi_r(mh)^3\chi_\lambda(mh)^3
\right|^2.
\tag{3}
\]

全部列索引仍保留来自唯一分解的条件和
\[
q_rq_{c'}q_m\le N,\qquad q_rq_{c'}q_hq_t^2\le B.
\tag{4}
\]
行 \(Dr\lambda\) 的原支撑及 \((D,r\lambda)=(r,\lambda)=1\) 等限制仍可保留。完整掩码展开后不恢复行与 \(c'\) 的互素条件。

## 4. 联合加权 Cauchy

固定 \(r,\lambda\)，将 (3) 的 \((t,c')\) 项记为 \(U_{t,c'}\)。由 (4)，可将其零延拓至固定集合
\[
q_t\le\sqrt B,\qquad q_{c'}\le N.
\]

取正权重 \(w_{t,c'}=1/(q_tq_{c'})\)，得到
\[
\left|\sum_{t,c'}U_{t,c'}\right|^2
\le
H(\sqrt B)H(N)
\sum_{t,c'}q_tq_{c'}|U_{t,c'}|^2.
\tag{5}
\]
这是对联合索引的一次 Cauchy，未逐个 \(b\) 作 Cauchy，也未拆开共同的 \(Q\) 列和。

固定 \(D,r,t,c'\) 后，行与 \(t\) 的掩码才成为固定行限制，此时可以在正项行和中保留或删除。不能在 (5) 之前删除它。

## 5. 统一参数的二次正项约化

固定 \(D,r,t,c'\)，合并 \(u=mh\)。该乘积平方自由，而且
\[
q_u\le \frac{NB}{q_r^2q_{c'}^2q_t^2}\le NB.
\tag{6}
\]
每个 \(u\) 的分解数至多 \(\Delta(NB)\)。合并后的二次系数是
\[
z_u=\chi_r(u)^3
\sum_{\substack{mh=u\\\text{继承支撑}}}
\alpha_D(rc'm,rc'ht^2),
\]
与残余行 \(\lambda\) 无关，且
\[
\sum_u|z_u|^2\le\Delta(NB)
\sum_{m,h}|\alpha_D(rc'm,rc'ht^2)|^2.
\]
使用二次大筛的统一参数 \((K,NB)\) 后，
\[
\begin{aligned}
E_D\le{}&
\Delta(K)H(\sqrt B)H(N)
C_{q,\eta}(KNB)^\eta(K+NB)\Delta(NB)\\
&\qquad\times
\sum_r\sum_{t,c',m,h}
q_tq_{c'}|\alpha_D(rc'm,rc'ht^2)|^2.
\end{aligned}
\tag{7}
\]
此为任意 \(\alpha_D\) 的完整正项约化。整个 \(Q\) 和仍留在同一个平方内。

## 6. 用原立方支撑消去 \(c'\) 权重

在 (7) 的继承支撑上，(4) 精确给出
\[
q_tq_{c'}\le\frac{B}{q_rq_hq_t}.
\tag{8}
\]
右侧与 \(c',m\) 无关。

先在原索引集合上应用 (8)，再以
\(|\alpha_D|^2\le\mathcal B|F_D|^2\) 估计，最后才扩大正项集合。于是 (7) 最后一行不超过
\[
\mathcal B B
\sum_{q_r\le N}\frac1{q_r}
\sum_{q_t\le\sqrt B}\frac1{q_t}
\sum_{q_h\le B}\frac1{q_h}
\sum_{\substack{c',m\\\text{继承支撑}}}
|F_D(rc'm,rc'ht^2)|^2.
\tag{9}
\]
这里 \(r\le N\) 来自 \(r\mid n\)，\(h\le B\) 来自 \(h\mid b\)，
\(t\le\sqrt B\) 来自 \(t^2\mid b\)。扩大到全部理想只增大正项和。

## 7. 三次共同系数与第二次乘积碰撞

固定 \(D,r,h,t\)，保留原始零值的恒等式是
\[
\chi_Q(rc'm)^{-2}\mathbf1_{(Q,rc'ht^2)=1}
=
\chi_Q(r)^{-2}\chi_Q(c'm)^{-2}\mathbf1_{(Q,ht)=1}.
\]
令
\[
w_{D,r,h,t}(Q)=
\frac{a_D(Q)}{\sqrt{q_Q}}\chi_Q(r)^{-2}\mathbf1_{(Q,ht)=1}.
\]
则 \(F_D(rc'm,rc'ht^2)=\sum_Qw_{D,r,h,t}(Q)\chi_Q(c'm)^{-2}\)。
该列系数与 \(j=c'm\) 无关，平方质量至多 \(\mathcal A_D\)。

在正项中合并 \(j=c'm\)。它平方自由，范数至多 \(N\)，每个 \(j\) 的分解数至多 \(\Delta(N)\)。使用三次大筛统一参数 \((N,L)\) 得
\[
\sum_{c',m}|F_D(rc'm,rc'ht^2)|^2
\le
\Delta(N)C_{c,\eta}(NL)^\eta
\{N+L+(NL)^{2/3}\}\mathcal A_D.
\tag{10}
\]
此时已经合法删除 \(\beta_D\)，而原 \(b\) 支撑已在 (8) 发挥作用。不同分解具有不同 \(b\)，但残余权重仅含固定 \(r,h,t\)，故可合并 \(j\)。

## 8. 完整因子账本

记 \(F(N,L)=N+L+(NL)^{2/3}\)。综合 (1)–(10)，
\[
\begin{aligned}
E(a,\beta)\le{}&
C_{q,\eta}C_{c,\eta}
\Delta(K)^2\Delta(NB)\Delta(N)
(KNB)^\eta(NL)^\eta\\
&\times(K+NB)B F(N,L)\mathcal B\\
&\times H(\sqrt B)^2H(N)^2H(B)
\sum_D\frac{\mathcal A_D}{q_D}.
\end{aligned}
\tag{11}
\]

五个调和因子分别来自：

| 因子 | 来源 |
|---|---|
| 第一个 \(H(\sqrt B)\) | 加权 Cauchy 的 \(t\) 权重 |
| 第一个 \(H(N)\) | 加权 Cauchy 的 \(c'\) 权重 |
| 第二个 \(H(\sqrt B)\) | (8) 后的 \(t\) 正项求和 |
| \(H(B)\) | (8) 后的 \(h\) 正项求和 |
| 第二个 \(H(N)\) | (8) 后的 \(r\) 正项求和 |

最后
\[
\sum_D\frac{\mathcal A_D}{q_D}
\le\sum_P\tau(P)\frac{|a(P)|^2}{q_P}
\le\Delta(L)\mathcal A.
\tag{12}
\]
这里每个 \(P\) 只按它自己的除数数目计费，未出现全部 \(D\) 的个数。

## 9. epsilon 预算

统一以辅助指数 \(\eta\) 应用两个大筛和除数界，小幂乘积是
\[
K^{2\eta}(NB)^\eta N^\eta L^\eta
(KNB)^\eta(NL)^\eta
=
K^{3\eta}N^{4\eta}B^{2\eta}L^{2\eta}
\le M^{4\eta}.
\]
五个调和因子至多 \(O((1+\log(2M))^5)\)。

取 \(\eta=\varepsilon/8\)：小幂花费 \(M^{\varepsilon/2}\)，其余由
\((1+\log(2M))^5\ll_\varepsilon M^{\varepsilon/2}\) 吸收，得到
\[
\boxed{
E(a,\beta)\ll_\varepsilon
(KNBL)^\varepsilon(K+NB)B
\{N+L+(NL)^{2/3}\}\mathcal A\mathcal B.
}
\]

所有常数在全部参数、有限集合与系数之前选定。没有额外 \(B\)；显式主因子恰为 \((K+NB)B\)。

## 10. 对形式化的影响

保留的实质步骤仍是两个 Möbius 掩码、唯一平方部分分解、两次不同的乘积纤维、符号精确零值和三次列系数独立性。

消除的是 \(C,G,T\) 的 dyad 组织、块 Cauchy、块求和，以及移动大筛商参数的非空性分支。Lean 中可改用联合加权有限 Cauchy，保留原 \(b\) 支撑推出 (8)，然后使用已有纤维、大筛和系数质量模块。实际外部理想的符号及计数接线仍需完成。

这是对原引理证明组织的实质简化，不是新的解析大筛输入。该独立审核在完成前未与另一审核代理交换结论。

