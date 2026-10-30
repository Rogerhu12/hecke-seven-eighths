素数槽消去（MI-P-PRIME-CANCELLATION-BELOW-ONE）交付说明
====================================================

一、结论与范围
--------------
本包交付了与 momentModels 无关的 Lean 消去核心，并把它接到带受控布尔掩码的
有限配对能量界。已验证部分共 23 个模块、219 个定理、
4683 行源码。全部逐模块编译，全部逐定理执行 #print axioms；公理均只有
propext、Classical.choice、Quot.sound。最终日志无 warning/error，退出码为 0。

这里没有把原工程的 HeckeSkeleton.paired_primes_below_one 标记为已经完成。
所附项目没有完整 import 闭包；两个 actual-Hecke / actual-MomentData 适配文件
明确标作未编译稿，不能把它们的存在当成项目验证已通过。原 momentModels 本身
仍是未完成的数据义务。原附件、供包源码及既有参考文件保持不变，没有提交。

本包独立证明了下面的链条：

  无零且全纯 + 统一多项式增长 + Euler 中心对数
  -> 真正的 L'/L 对数界
  -> 光滑窗口的 Mellin 反演和有证明的竖线移动
  -> W(x)/log(Px) 的一致控制
  -> 精确 prime + higher-prime-powers 分解与 sqrt(P) 误差
  -> 在窗口之前选定有限半范数的统一素数消去
  -> 受控掩码、sqrt 归一化、槽乘积和行计数。

二、核心定理及其真正假设
----------------------
最强统一接口位于 PrimeCancellationUniformProfiles.lean：
  PrimeCancellation.UniformProfiles.exists_uniform_prime_seminorm_bound

先选一个有限集合 s ⊂ N×N 和 Cstar>0，且 (0,0)∈s；它们先于所有窗口、字符、
零边界、导子、缓冲和尺度。记 S_s(W) 为 s 中标准 Schwartz 半范数的最大值。
设 W 是支撑在 [1,2] 的复值 Schwartz 函数。给定：
  1. 可数的素对象索引，范数 nu(p) >= 2；其有限子集的计数 <= degreeBound * Y；
  2. |a(p)| <= 1；
  3. F 全纯，在 Re(s)>beta 无零，1/2 <= beta <= 1；
  4. |F(s)| <= C Q^p (2+|Im(s)|)^k 对 Re(s)>=1/2 成立，C,Q>=1,p>=0；
  5. exp(m_t)=F(2+it)，|m_t|<=A，A 不依赖 t；
  6. 真实素幂 Euler 恒等式：
       sum_{p,n>=1} log(nu(p))*a(p)^n*(nu(p)^n)^(-s) = -F'(s)/F(s)，Re(s)>1；
     以及这个级数在 Re(s)=2 的绝对收敛。
则对全部 P>=1、0<delta<=1/4，有

  |sum_p a(p) W(nu(p)/P)| <= A_delta * S_s(W) * P^(beta+delta)，

  A_delta = 24 Cstar (H+3k)/delta^2
            + degreeBound*(1+sqrt(2)) + 2*degreeBound*exp(4)，
  H = 1 + log C + p log Q + A。

素数和估计、Mellin 衰减、移线、无穷素幂分解都不是这个定理的假设。
Mellin 核的 pi 积分给出显式常数 24；最后一项处理 1<=P<exp(4)。
源窗口的半范数控制在 PrimeCancellationSchwartzControl.lean 中证明，
不是额外假设。有限指标 s 以存在方式给出，没有冒充一个已计算出的最小阶数。

通用配对模块 PrimeCancellationPairedProfiles.lean 的主定理为：
  PrimeCancellation.PairedProfiles.exists_uniform_paired_seminorm_bound

它以 SlotData 中的原始解析与 Euler 数据推导每槽消去，再计入删除项数 Bi。
在上述 beta、delta 范围内，若 X>=1、Pi=X^ell_i>=1、行数<=Crows*X^e，
且 2*delta*sum ell_i<=eps，则

  sum_rows |prod_i normalizedMaskedPrimeSum_i|^2
    <= Crows * prod_i ((Ai + Bi)*S_s(Wi))^2
       * X^(e + (2*beta-1)*sum ell_i + eps)。

这里要求每个 H_i 对全部成员行都满足 H_i>=H(data_{u,i})+3*k_{u,i}，并定义
  Ai=24*Cstar*H_i/delta^2 + d_i*(1+sqrt(2)) + 2*d_i*exp(4)。
Bi 同样对全部成员行控制删除数。Pi>=1 已覆盖任意短槽，
没有假设槽长或 shell 有正下界。data 仅在实际允许行/有效槽的成员子类型上要求，
不要求被排除的行满足整性与无零。s、Cstar 选在全部窗口和模型之前。
具体签名（包括量词顺序）见 THEOREM_STATEMENTS.txt 和完整源码。

PrimeCancellation.lean 与 PrimeCancellationPaired.lean 另外保留固定 C∞ 窗口
版本；它们不要求调用者先把窗口包装成 SchwartzMap。两条路线均已验证。

三、掩码已经怎样处理
--------------------
PrimeCancellationMaskCount.lean 证明：不同高度一素理想都整除 D，则它们的积
整除 D；对任意自然值乘法理想范数 N，若每个范数>=B>1，删去的项数至多
log(ND)/log(B)。它直接推出复杂布尔掩码的稀疏删除误差，无需把误差界当结论假设。

补传 TASK.md 说 actual originalMomentMask 只删固定坏素数，这与实际源码不符。
Moments.lean 中还存在 IsCoprime I u.val。对素理想 p，保留条件恰为：
  p 不在 S，6 不在 p，且 p 不整除 u。
所以正确支持理想是 D_fixed * u。全部 pairedRows 满足 N(u)<=momentBase，
故其代价仍只是受控对数。不能自动把它当作系数在导子素数处已经为零：原代码
特意包括行理想中的冗余六次幂，它们未必进入 primitive conductor。
这一更正有已编译的 IdealMask / MaskCount 证明，不只是文字推测。

四、有限半范数与 Euler 导数
----------------------------------
标准 Schwartz 半范数的一致控制已完成：截断后的对数坐标拉回是连续线性映射，
紧参数乘子族的 Fourier 界最终由源空间有限个半范数控制。选择先于 W，
因此适用于变化的 W_Z。项目特有 testSeminorm 与这些标准半范数的识别，以及
实际模型的 prime windows 是否具备所需统一控制，仍是项目实例化事实。

包中同时保留可显式指定阶数的中间接口：
对对数坐标 profile g，若 0 阶与 3 阶 L1 范数分别受 L0、L3 控制，则统一
三次 Mellin 衰减常数可取
  8*(1+2*pi)^3 * (L0 + L3/(2*pi)^3)。
该接口在 PrimeCancellationMellinSeminorm.lean 中证明。

PrimeCancellationEulerDerivatives.lean 证明正尺度上的精确公式。令
  D_P f(P)=P*f'(P)，T W(x)=-x*W'(x)-W(x)/2，
则每个固定 q 都满足
  D_P^q [P^(-1/2) sum_p a(p)W(nu(p)/P)]
    = P^(-1/2) sum_p a(p)(T^q W)(nu(p)/P)。
证明先由有限子集计数导出有界范数素对象集合有限，再在 P 的邻域内选共同有限池；
没有要求同一有限池对所有 P 有效，也没有假设无穷求和与导数可交换。
T 的各次迭代保持 C∞ 及支撑于 [1,2]。项目 testSeminorm 的具体导数阶数常数
并未另行宣称完成；PDF 给出普通 Euler 半范数的定量数学推导。

五、实际源码审计得到的接线缺口
----------------------------
1. WholeMomentProfileControl 只控制 inverseTest、plainTest1、plainTest2，
   没有量化 prime windows。它目前不能提供素数槽的光滑性/支撑/统一半范数。
2. SourcePolynomialCalibration.character 只校准 witness 的物理行；
   SourceRowEligibility.paired_rows 只有物理行进入模型行的单向包含。
   目标求和全部模型 pairedRows，导子增长必须覆盖全部被求和行。
3. rowCharacter 不在 theta 并不能单独推出 rowCharacter*slotCoefficient 非主。
   还须证明每个 slotCoefficient 的逆元在 theta；通用群论引理已提供。
4. 总长度校准不能限制 slotCount。实际槽与 selected 的等价或一个固定嵌入
   可以给出 slotCount<=c.geometry.slots；对应适配引理已写。
5. 实际高度参数满足 profile 控制门槛、理想行计数和 Euler 系数正规化需要接线。
6. 所附 HeckeUniformStripGrowth 的导子一致结论假设全虚数域和固定无穷型。
   它不是任意数域的无条件统一增长接口。实位分支保留显式增长前提。
7. 实际整性定理要求“不是任何范数幂”。有限阶非主到该性质的字符库接口未附。

这些是对供包实际声明的结论；没有声称完整本地项目中不存在所需引理。
最需本地复核的是：全部模型行的导子界与 prime-profile 控制，以及缺失定义中的
两个具体定义展开（Hecke Euler 级数及其导数比）。详见两份 API / wiring 报告。
因此不能说原目标只剩一次无条件的机械实例化。

六、文件导航
------------
PrimeCancellation.lean                  真正的固定窗口素数消去核心
PrimeCancellationPaired.lean            从原始解析数据到带掩码配对能量
PrimeCancellationSchwartzControl.lean   在窗口之前选定有限源半范数
PrimeCancellationUniformProfiles.lean   有限半范数控制的统一素数和界
PrimeCancellationPairedProfiles.lean    有限半范数控制的统一配对能量界
PrimeCancellationEulerDerivatives.lean  实际素数和的任意固定次尺度 Euler 导数
PrimeCancellationLogDerivative.lean     非零圆盘 -> 解析对数 -> 导数比界
PrimeCancellationDiskGeometry.lean      缓冲几何与多项式增长的对数化
PrimeCancellationMellin.lean            紧支撑 Mellin 解析性、可积性及加权反演
PrimeCancellationContour.lean           Cauchy 矩形到无限竖线移动
PrimeCancellationAnalytic.lean          解析数据、移线与明确的 24 常数
PrimeCancellationWindowControl.lean     三次衰减、sqrt 误差与归一化
PrimeCancellationCompactFamily.lean     参数族的有限阶 L1 / Fourier 控制
PrimeCancellationLogProfile.lean        W/log(Px) 的固定窗口一致 Mellin 衰减
PrimeCancellationLogWindow.lean         全实轴光滑、支撑、精确 1/k 恒等式
PrimeCancellationFixedWindow.lean       不再假设 Mellin 衰减的加权 Euler 和界
PrimeCancellationMellinSeminorm.lean     任意族的 0/3 阶 L1 定量接口
PrimeCancellationPrimePowers.lean       有限素幂的几何与 sqrt(P) 界
PrimeCancellationPrimeSeries.lean       无穷和的绝对收敛与 prime+tail 精确分解
PrimeCancellationIdealMask.lean         实际理想掩码的三条件
PrimeCancellationMaskCount.lean         删去素理想的 log(ND)/log(B) 界
PrimeCancellationAux.lean               有限代数、非主性、归一化、乘积、行数
PrimeCancellationUniformity.lean        固定高度指数的 log 吸收及 buffer 分配

project_adapters/HeckeSkeleton/
  PrimeCancellationHecke.lean           实际 Hecke API 适配稿，未编译
  PrimeCancellationMoment.lean          实际 MomentData / Moments 适配稿，未编译

PrimeCancellation_Report.pdf/.tex       一页实现报告
PrimeCancellation_Proof.pdf/.tex        完整数学证明与形式化范围
THEOREM_STATEMENTS.txt                  Lean 实际打印的全部定理类型
PROJECT_ADAPTER_STATEMENTS.txt          未编译项目定理的源声明
HECKE_API_REPORT.txt                    已见与“需核对”接口逐项清单
MOMENT_WIRING_AUDIT.txt                 实际模型接线审计
PROJECT_IMPORT_AUDIT.txt                供包中缺失的直接项目导入
BUILD_STATUS.txt / verification_summary.json / logs/
                                       版本、逐模块编译、公理和哈希证据
SHA256SUMS.txt                          交付文件哈希
BUILD_ORDER.txt                        依赖拓扑顺序
build_one.py                           每次只编译一个模块的可移植脚本
lakefile.lean / lean-toolchain          精确版本配置
LICENSE / NOTICE.txt                   Apache 2.0 与改编来源

七、复现
--------
Lean: 4.35.0-rc3
Lean commit: 470d5ce1400764999581fd26d5d72b00d990b0f4
Mathlib: 0493595ecd5da8ef14742febab99728f98e948e8

在新的解压目录中配置 elan/Lake 后：
  MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
  python3 prepare_cache.py

然后按 BUILD_ORDER.txt，每次仅运行一个命令，例如：
  python3 build_one.py PrimeCancellationAux.lean

全部证明模块结束后，可单独重打定理类型清单：
  python3 build_one.py PrimeCancellationInventory.lean

等一个命令结束后再编译下一个。脚本不会跑全量 lake build，不会并行编译模块。
该脚本将已编译模块放在解压目录，并把该目录加入本次进程的 LEAN_PATH。
具体本轮实际编译命令（含隔离路径）保存在 logs/；可移植脚本采用相同编译方式，
不依赖本轮临时机器路径。项目适配稿须放入完整原工程另行编译，不属于此脚本的
验证名单，且不能把旧 momentModels 的占位证明计成新的已验证依赖。

八、来源与披露
--------------
通用复分析、Mellin 和 profile 参数族的部分证明模式改编自 OpenAI/math
fd4aeeb2 的公开 Apache-2.0 代码，并以新命名空间去掉特殊数域依赖，在用户指定
的新 Mathlib 版本上重新编译。详见 NOTICE.txt。数学方法是标准方法，不主张为
新发现。本轮贡献是独立可验证的泛化、完整分析与素幂链条、掩码算术和具体接口审计。
