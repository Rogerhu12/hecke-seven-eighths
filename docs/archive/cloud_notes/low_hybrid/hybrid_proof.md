# LOW-HYBRID：完整正项约化、系数质量及可形式化接口

本文仅记录可独立核查的数学推导。补传压缩包提供了项目接口文件，但未包含目标 Hecke 工程的全部传递依赖；本文中的数学推导不等于这些对象上的 Lean 实例化已经完成。

核对的原始文本是 `weil_seven_eighths_revised(1).tex`，其中 `lem:completed-quadratic-reduction` 位于第 2008 行，`lem:can-hybrid` 位于第 2050 行，`lem:can-marked-energy` 位于第 2116 行。以下给出引理 4.6–4.7 的完整证明，并把原文略去的两个因子碰撞、两个移动掩码及系数质量写明。

## 1. 结论及必需结构

令 \(\mathcal I\) 为外部非零整理想组成的交换幺半群，\(q(I)\ge1\) 为乘法范数。固定有限支撑，延拓系数为零。设

\[
q(k)\le K,\qquad q(n)\le N,\qquad q(b)\le B,\qquad q(P)\le L,
\qquad K,N,B,L\ge1,
\]

其中 \(k,n,P\) 平方自由，\(b\) 任意。固定的行限制允许任意缩小行集合。系数 \(a(P)\) 与 \(k,n,b\) 无关，\(\beta(n,b)\) 与 \(k,P\) 无关。定义

\[
\mathcal A(a)=\sum_P\frac{|a(P)|^2}{q(P)},\qquad
\mathcal B(\beta)=\sup_{n,b}|\beta(n,b)|^2.
\]

空支撑时令第二个量为零。则对任意 \(\varepsilon>0\)，

\[
\begin{aligned}
E(a,\beta)
&:=\sum_k\left|
 \sum_P\frac{a(P)}{\sqrt{q(P)}}\mathbf1_{(P,k)=1}
 \sum_{n,b}\beta(n,b)\chi_k(nb)^3\chi_P(n)^{-2}
                      \mathbf1_{(P,b)=1}\right|^2\\
&\ll_\varepsilon (KNBL)^\varepsilon
 (K+NB)B\{N+L+(NL)^{2/3}\}\,
 \mathcal A(a)\mathcal B(\beta).
\tag{H}
\end{aligned}
\]

这里 \(\chi_P(n)^{-2}\) 按复数域中的零扩张解释；零的逆仍取零。对六次根值符号，这也等于其平方的复共轭。

该加权质量版本比任务中的有界系数版本方便：若 \(|a|,|\beta|\le1\)，且 \(q(P)\asymp L\)，理想计数立即给出 \(\mathcal A(a)\ll1\)。任务中的 \(\ll\)、\(\asymp\) 支撑端点只改变固定常数。

### 1.1 除两个大筛以外，需要明确声明或调用的事实

1. 外部理想唯一分解、最大公因子和乘法范数。
2. 理想计数：存在 \(A\ge1\)，对所有 \(X\ge1\)，
   \[
   \#\{I:q(I)\le X\}\le AX.
   \tag{Count}
   \]
3. 除数界：任意 \(\eta>0\)，存在 \(D_\eta\)，使
   \[
   \tau(I):=\#\{J:J\mid I\}\le D_\eta q(I)^\eta.
   \tag{Div}
   \]
4. 理想 Möbius 恒等式
   \[
   \mathbf1_{(I,J)=1}=\sum_{D\mid I,\,D\mid J}\mu(D).
   \tag{Mob}
   \]
5. 符号在本证明所用变量中的乘法性、\(|\chi|\le1\)、公共素因子处精确为零，以及
   \[
   \chi_k(u^2v)^3=\chi_k(v)^3\mathbf1_{(k,u)=1}.
   \tag{Square}
   \]

可将第 5 项写成两个独立核 \(Q_k(u)=\chi_k(u)^3\)、\(C_P(n)=\chi_P(n)^{-2}\) 的性质；证明不再使用二次和三次核之间的其他关系。

**实现上的实质检查：**`idealSymbol D I a` 对元素 \(a\) 的乘法性，并不自动等于 \(I,J\mapsto\texttt{idealSymbol D I (D.generator J)}\) 对理想 \(J\) 的乘法性。所选允许生成元的乘法兼容、或者将缺陷消成固定类因子的有限分片，需要从现有工程真实的定义和定理证明。不能把它悄悄塞进“两个大筛已证”这一句话。本文的理想符号恒等式均以这一桥接已经完成为前提。

### 1.2 大筛方向

本证明使用

\[
\sum_{k\in R}\left|\sum_{u\in U}z_u\chi_k(u)^3\right|^2
\le Q_\eta(X,Y)\sum_{u\in U}|z_u|^2,
\quad
Q_\eta(X,Y)=C_{q,\eta}(XY)^\eta(X+Y),
\tag{QS}
\]

其中两组理想都平方自由，范数分别不超过 \(X,Y\)。任务给出的 `QuadraticSieveBound` 若使用转置方向 \(\chi_J(I)^3\)，可用有限维 \(\ell^2\) 对偶性转置，而 \(X+Y\) 和 \((XY)^\eta\) 对称；此步骤不需要新的解析输入。

精确地，若对矩阵 \(M_{ij}\) 的每个向量 \(w\) 有 \(\sum_i|\sum_jM_{ij}w_j|^2\le C\sum_j|w_j|^2\)，则对其转置也有同一界。取 \(t_j=\sum_iM_{ij}z_i\)，把 \(\sum_j|t_j|^2\) 写成 \(\sum_i z_i\sum_jM_{ij}\overline{t_j}\)，用 Cauchy 后应用原界即可。该论证适用于复数矩阵，并不要求核实值。

三次大筛以本来需要的方向应用：

\[
\sum_{j\in J}\left|\sum_{Q\in\mathcal Q}w_Q\chi_Q(j)^{-2}\right|^2
\le C_\eta(X,Y)\sum_Q|w_Q|^2,
\quad
C_\eta(X,Y)=C_{c,\eta}(XY)^\eta
 \{X+Y+(XY)^{2/3}\}.
\tag{CS}
\]

## 2. 第一个移动掩码：\((P,k)=1\)

按 (Mob) 展开整个掩码。对固定行 \(k\)，写

\[
\sum_{D\mid k}\frac{\mu(D)}{\sqrt{q(D)}}\,
G_D(k/D).
\]

这里在每个非零项中令 \(P=DQ\)、\(k=D\kappa\)，并定义

\[
a_D(Q)=a(DQ)\mathbf1_{(D,Q)=1},
\]

\[
\beta_D(n,b)=\beta(n,b)\chi_D(nb)^3\chi_D(n)^{-2}
                         \mathbf1_{(D,b)=1},
\tag{BD}
\]

\[
F_D(n,b)=\sum_Q\frac{a_D(Q)}{\sqrt{q(Q)}}
                  \chi_Q(n)^{-2}\mathbf1_{(Q,b)=1},
\tag{FD}
\]

\[
G_D(\kappa)=\sum_{n,b}\beta_D(n,b)F_D(n,b)\chi_\kappa(nb)^3.
\]

原 \(P\) 支撑仍保留在 \(a_D\) 中。残余行集合是

\[
R_D=\{\kappa:D\kappa\in R,\ (D,\kappa)=1\};
\]

它可包含任务中全部既定行限制。因为原行平方自由，\(D\) 和 \(\kappa\) 平方自由。\(Q\) 也平方自由，且 \(q(Q)\le L/q(D)\)。

对 \(D\mid k\) 作一次**行内除数 Cauchy**：

\[
E(a,\beta)
\le \Delta(K)\sum_D\frac1{q(D)}
            \sum_{\kappa\in R_D}|G_D(\kappa)|^2,
\quad
\Delta(X)=\max_{q(I)\le X}\tau(I).
\tag{D-Cauchy}
\]

\(q(D)^{-1}\) 正是原 \(q(P)^{-1/2}\) 在平方后留下的因子，不能省略。\(|\beta_D|\le\sqrt{\mathcal B(\beta)}\)，且 \(\beta_D\) 与 \(\kappa,Q\) 无关。此处所有 \(D\) 相位依赖都已经显式写进 (BD)，没有把残余行 \(\kappa\) 的依赖藏进系数。

## 3. 完成二次正项约化

本节对任意复系数 \(z(n,b)\) 进行；在应用时取 \(z=\beta_DF_D\)。

### 3.1 唯一分解及精确零值

唯一写

\[
b=gt^2,\qquad g\text{ 平方自由},
\]

再令

\[
c=(n,g),\qquad n=cm,\qquad g=ch.
\]

于是 \(c,m,h\) 两两互素且各自平方自由。\(g,t\) 允许共享素因子。恒等式是

\[
\chi_\kappa(nb)^3
=\chi_\kappa(mh)^3\mathbf1_{(\kappa,ct)=1}.
\tag{Q-exact}
\]

特别不能从该式删掉 \((\kappa,t)=1\) 的零值。

按下端点 dyad 分成

\[
C\le q(c)<2C,\qquad G\le q(g)<2G,\qquad T\le q(t)<2T,
\tag{Block}
\]

其中 \(C,G,T\) 都是 \(2\) 的非负整数次幂。非空块必满足

\[
GT^2\le B,\quad C\le N,\quad G\le B,
\quad q(mh)\le Y:=\frac{2NG}{C^2}.
\tag{Ranges}
\]

总块数记作 \(J\)，可取 \(J\ll(1+\log(2KNBL))^3\)。先在行内对块应用 Cauchy，最终最多付出 \(J^2\)，这完全可吸收到小幂中。

### 3.2 第二个移动掩码及确切的行集合

保留 \(\mathbf1_{(\kappa,t)=1}\)，展开**整个** \(\mathbf1_{(\kappa,c)=1}\)：

\[
\mathbf1_{(\kappa,c)=1}=\sum_{r\mid\kappa,\,r\mid c}\mu(r).
\]

令 \(\kappa=r\lambda\)、\(c=rc'\)。行内除数 Cauchy 再付出 \(\Delta(K/q(D))\)。对于固定 \(D,r,t\)，用于二次大筛的行是满足

\[
Dr\lambda\in R,\quad
(D,r\lambda)=1,\quad(r,\lambda)=1,\quad
(r\lambda,t)=1
\tag{Rows}
\]

的平方自由 \(\lambda\)，且 \(q(\lambda)\le K/(q(D)q(r))\)。这些都是固定行限制，与 \(c',m,h,Q\) 无关。

依次对 \(t\) 和 \(c'\) 做 Cauchy。它们的计数因子为

\[
T_\#:=\#\{t:q(t)<2T\}\le2AT,
\qquad
C_{\#,r}:=\#\{c':q(c')<2C/q(r)\}
\le\frac{2AC}{q(r)}.
\tag{TC-count}
\]

若计数上限小于 1，对应集合为空，应直接删掉该项，不能调用要求参数至少为 1 的大筛。

### 3.3 第一次乘积碰撞：\(u=mh\)

固定 \(D,r,t,c'\) 后，把平方自由互素乘积 \(mh\) 合并为 \(u\)。每个 \(u\) 的有序分解 \(u=mh\) 至多 \(\tau(u)\) 个。对应合并系数为

\[
Z_u=\chi_r(u)^3\!
\sum_{\substack{mh=u\\\text{保留全部块和原支撑}}}
 z(rc'm,rc'ht^2).
\]

\(\chi_r(u)^3\) 只依赖固定的 \(r\) 与列 \(u\)，不依赖残余行 \(\lambda\)。因而

\[
\sum_u|Z_u|^2
\le\Delta(Y)\sum_{m,h}|z(rc'm,rc'ht^2)|^2.
\tag{mh-fiber}
\]

这一步解释了为什么需要除数界，且为什么不能在合并前把含行的相位当成系数。

应用 (QS)，得到本块的完全正项上界

\[
\begin{aligned}
E_{D;C,G,T}(z)
\le{}&\Delta(K/q(D))\,T_\#\,\Delta(Y)\\
&\times\sum_r C_{\#,r}\,
 Q_\eta\!\left(\frac K{q(D)q(r)},Y\right)
 \sum_{t,c',m,h}|z(rc'm,rc'ht^2)|^2.
\tag{QP}
\end{aligned}
\]

内层求和保留所继承的块、原系数支撑、平方自由和互素条件。\(t\) 已在内层求和出现一次；外面的 \(T_\#\) 是 Cauchy 成本，而不是把同一个求和重复计算。类似地，\(C_{\#,r}\) 是一次 Cauchy 成本，内层仍然对 \(c'\) 求和。

若略去除数小幂与固定常数，(QP) 正是原稿的

\[
T\sum_t\sum_r
\left(\frac K{q(D)q(r)}+\frac{NG}{C^2}\right)
\frac C{q(r)}\sum_{c',m,h}|z(rc'm,rc'ht^2)|^2.
\]

这里的 \(D=1\) 专门化给出引理 4.6 的正项约化。

## 4. 三次大筛必须在 \(c'm\) 合并后使用

令 \(z=\beta_DF_D\)。固定 \(D,r,h,t\)，则精确恒等式为

\[
\chi_Q(rc'm)^{-2}\mathbf1_{(Q,rc'ht^2)=1}
=\chi_Q(r)^{-2}\chi_Q(c'm)^{-2}\mathbf1_{(Q,ht)=1}.
\tag{C-mask}
\]

左侧掩码在 \(r,c'\) 处的零值由右侧两个三次符号保留；\(h,t\) 的零值保留在显式掩码中。这个恒等式不需要假定 \(Q\) 与 \(r,c'\) 互素。

定义

\[
w_{D,r,h,t}(Q)=\frac{a_D(Q)}{\sqrt{q(Q)}}
                 \chi_Q(r)^{-2}\mathbf1_{(Q,ht)=1}.
\tag{w}
\]

此系数与三次行 \(j=c'm\) 无关。其质量满足

\[
\sum_Q|w_{D,r,h,t}(Q)|^2
\le\mathcal A_D,
\qquad
\mathcal A_D:=\sum_Q\frac{|a_D(Q)|^2}{q(Q)}.
\tag{AD}
\]

现在合并 \(j=c'm=n/r\)。它平方自由且 \(q(j)\le N/q(r)\)。每个 \(j\) 至多有 \(\tau(j)\) 个 \((c',m)\) 分解。由 \(|\beta_D|^2\le\mathcal B(\beta)\) 得

\[
\begin{aligned}
&\sum_{c',m}|\beta_D(rc'm,rc'ht^2)|^2
               |F_D(rc'm,rc'ht^2)|^2\\
&\quad\le\mathcal B(\beta)\Delta(N/q(r))
 \sum_{j\text{ sf},\ q(j)\le N/q(r)}
 \left|\sum_Qw_{D,r,h,t}(Q)\chi_Q(j)^{-2}\right|^2\\
&\quad\le\mathcal B(\beta)\Delta(N/q(r))
 C_\eta\!\left(\frac N{q(r)},\frac L{q(D)}\right)\mathcal A_D.
\tag{Cubic-step}
\end{aligned}
\]

这是第二次乘积碰撞。若对每个 \(c'\) 单独应用三次大筛，再把 \(c'\) 求和，会多出不允许的 \(C/q(r)\)；(Cubic-step) 正好避免此损失。对每个 \(b\) 单独在最开始做 Cauchy 也无法保留这个组合结构。

\(h\) 的计数为

\[
H_\#\le\#\{h:q(h)<2G/C\}\le2AG/C.
\]

因此将 (Cubic-step) 代入 (QP) 后，来自 \(t,c',h\) 的**全部计数和 Cauchy 因子**恰为

\[
T_\#^2\,C_{\#,r}\,H_\#
\le16A^4\,\frac{T^2G}{q(r)}
\le16A^4\,\frac B{q(r)}.
\tag{Ledger}
\]

这就是论文中 \(T^2(C/r)(G/C)=B/r\) 的精确含义。没有出现第二个 \(B\)，也没有丢掉任何移动互素掩码。

## 5. 不再对 \(D,r\) 分 dyad 的收尾

原稿对 \(D,r\) 再分 dyad。加权质量版本不需要这些分块。

首先，由理想计数和分部求和，或直接以 dyad 求和，

\[
\sum_{q(r)\le R}\frac1{q(r)}\ll_A1+\log(2R).
\tag{Harmonic}
\]

非空项的 \(r\) 至多有范数 \(N\)，故 (Ledger) 后的 \(r\) 求和只付出一个对数。

其次，由唯一分解和 \(P\) 平方自由，

\[
\begin{aligned}
\sum_D\frac{\mathcal A_D}{q(D)}
&\le\sum_{P\text{ sf}}\frac{|a(P)|^2}{q(P)}\sum_{D\mid P}1\\
&=\sum_P\tau(P)\frac{|a(P)|^2}{q(P)}
\le D_\eta L^\eta\mathcal A(a).
\tag{D-mass}
\end{aligned}
\]

若 \(D\) 的全部平方自由除数都保留，则第一行是等号；行支撑通常删去一些 \(D\)，所以实际使用不等号。此式同时追踪原列系数的质量，避免对每个 \(D\) 先丢掉 \(a\) 再估计列计数。

在所有非空块中，

\[
\frac K{q(D)q(r)}+\frac{2NG}{C^2}
\le2(K+NB),
\]

\[
\frac N{q(r)}+\frac L{q(D)}
+\left(\frac{NL}{q(r)q(D)}\right)^{2/3}
\le N+L+(NL)^{2/3}.
\]

参数小于 1 的空项不调用大筛；非空项的全部大筛参数都至少为 1。

### 5.1 小幂支出总账

令 \(M=KNBL\)。使用两大筛与除数界时统一取辅助指数 \(\eta\)。除固定常数外，各小幂因子可排列为

| 来源 | 上界 |
|---|---:|
| \((P,k)\) 掩码的行除数 Cauchy | \(K^\eta\) |
| \((\kappa,c)\) 掩码的行除数 Cauchy | \(K^\eta\) |
| \(u=mh\) 的纤维 | \((2NB)^\eta\) |
| \(j=c'm\) 的纤维 | \(N^\eta\) |
| 二次大筛的小幂 | \((2KNB)^\eta\) |
| 三次大筛的小幂 | \((NL)^\eta\) |
| \(D\) 汇总后的原列除数质量 | \(L^\eta\) |

乘积至多固定常数乘

\[
K^{3\eta}N^{4\eta}B^{2\eta}L^{2\eta}\le M^{4\eta}.
\]

块 Cauchy 与块求和共贡献 \(J^2\ll(1+\log(2M))^6\)，\(r\) 谐和和再贡献一个对数。取 \(\eta=\varepsilon/8\)，并用

\[
(1+\log(2M))^7\ll_\varepsilon M^{\varepsilon/2}\qquad(M\ge1),
\]

便得到 (H)。这是完整的量词顺序：先给定 \(\varepsilon>0\)，再选 \(\eta\)，调用两个大筛及除数界所得常数，最后对全部 \(K,N,B,L\)、行集合和系数统一成立。

## 6. 引理 4.6 的简单式也由同一约化推出

直接把 \(|z(n,b)|\le1\) 代入 (QP) 的 \(D=1\) 情形。固定 \(r,c',t\) 时，

\[
\#m\ll N/C,\quad\#h\ll G/C,
\quad\#c'\ll C/q(r),\quad\#t\ll T.
\]

于是包含外层 Cauchy 因子的全部计数为

\[
T^2\frac C{q(r)}\frac C{q(r)}\frac N C\frac G C
=\frac{T^2NG}{q(r)^2}\le\frac{NB}{q(r)^2}.
\]

二次大筛的主因子至多 \(K+2NB\)。理想计数给出 \(\sum_rq(r)^{-2}\ll1\)。除数、dyad 和大筛小幂照上述方法吸收，得到

\[
\sum_k\left|\sum_{n,b}z(n,b)\chi_k(nb)^3\right|^2
\ll_\varepsilon(KNB)^\varepsilon(K+NB)NB.
\]

注意简单式里自然保留 \(NB\) 列总量；混合式用三次大筛替换了这部分计数，从而得到 \(B\{N+L+(NL)^{2/3}\}\)。

## 7. 最强而实用的有限和形式化接口

理想数论与纯有限和线性代数宜分层。下述内核不需要任何数域对象，并能直接服务于 (QP) 和 (Cubic-step)。

### 7.1 带纤维权重的正项拉回

给定有限集合 \(S,J\)、映射 \(f:S\to J\)、权重 \(\beta:S\to\mathbb C\) 和任意 \(F:J\to\mathbb C\)，有精确恒等式

\[
\sum_{s\in S}|\beta_sF(f(s))|^2
=\sum_{j\in J}\left(\sum_{s\in S:f(s)=j}|\beta_s|^2\right)|F(j)|^2,
\]

前提是所有 \(f(s)\in J\)。若每个纤维的权重质量至多 \(W\)，右侧至多 \(W\sum_j|F(j)|^2\)。取 \(f(c',m)=c'm\)、\(W=\mathcal B(\beta)\Delta(N/r)\) 即是三次大筛之前的完整组合。

这比只提供“纤维个数至多 \(m\)”的接口更强，也允许在后续任务中利用稀疏 \(\beta\) 的实际质量。

### 7.2 合并系数的 Cauchy

对 \(z:S\to\mathbb C\)，若每个纤维元素数至多 \(m\)，则

\[
\sum_{j\in J}\left|\sum_{s\in S:f(s)=j}z_s\right|^2
\le m\sum_{s\in S}|z_s|^2.
\]

取 \(f(m,h)=mh\) 就得到二次大筛系数合并的损失。它与上一项不同：这里先在纤维内相加再取平方；上一项是在正项能量中合并重复行。

### 7.3 带冻结参数的三次估计

设对核 \(C(j,p)\) 已知

\[
\sum_j\left|\sum_pw_pC(j,p)\right|^2\le S\sum_p|w_p|^2.
\]

允许冻结参数 \(t,h,r,D\) 决定系数 \(w\)，只要它不依赖 \(j\)。若

\[
w_p=\frac{a_p}{\sqrt{q_p}}u_p,\qquad |u_p|\le1,
\]

则右侧至多 \(S\sum_p|a_p|^2/q_p\)。结合 7.1，立即得到固定 \(D,r,h,t\) 的 (Cubic-step)。

### 7.4 行内除数 Cauchy

对每行 \(k\) 给定有限指标集 \(D(k)\)，若 \(\#D(k)\le\Delta\)，则

\[
\sum_k\left|\sum_{d\in D(k)}c_{k,d}\right|^2
\le\Delta\sum_k\sum_{d\in D(k)}|c_{k,d}|^2.
\]

这里 \(D(k)\) 的行依赖必须留在陈述里；后续按 \(k=d\kappa\) 或 \(\kappa=r\lambda\) 重排是另一个明确的双射引理。不能先假装 \(d\) 的集合和系数都与行无关，再引用普通固定集合版本。

### 7.5 对原工程的出口

如果当前工程已经提供上述 1.1 的真实理想和符号接口，那么这份推导仅需要两个已证大筛，不需要 theta 反射、任何新的 L 函数输入或新的解析估计。要兑现任务的完整 Lean 标准，还必须在真实 `ExteriorIdeal K S` 上证明：

- 三次分解 \(b=gt^2\)、\(c=(n,g)\) 的双射与支撑转移；
- 两个 Möbius 掩码的有限和重排；
- 两种乘积纤维与理想除数集合之间的注入；
- 符号在允许生成元上的精确恒等式；
- 计数、除数界、对数损失的统一常数及实数幂账本。

只证明抽象有限和内核能够减少这些证明的重复，但本身不能替代上述实例化，更不能据此声称原 `hybrid_energy` 已经构建通过。
