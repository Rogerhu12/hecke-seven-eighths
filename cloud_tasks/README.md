# 云端任务

**仓库**：`Rogerhu12/hecke-seven-eighths`，分支 `dtests-handoff`。论文是根目录下的 `weil_seven_eighths_revised.tex`。顶层骨架在 `HeckeSkeleton/`，其中尚未完成的部分都标有 `-- OBLIGATION <ID>`。

**参考**：openai/math（https://github.com/openai/math ，路径 `lean/OAI/NumberTheory/DirichletL/`）。

**环境**：Lean 4.35.0-rc3，Mathlib `0493595ecd5da8ef14742febab99728f98e948e8`。

**持续工作**：领到任务后要一直做到完成标准全部达到才算结束，即目标定理编译通过、公理检查只含三条标准公理、PR 标为可审查。不要中途停下来汇报阶段性进展，也不要停在"草稿"状态。某一部分被卡住时，把原因记在 PR 里，转去做其他部分，全部能做的都做完才停。

**规矩**
1. 每个任务在自己的新分支上做，用 PR 交付到 `dtests-handoff`；不要直接推送 `dtests-handoff`。
2. 一个 PR 只做一个任务。
3. **可以修改骨架中的定义和陈述**，用来修正缺陷或补上必要的假设，但必须满足以下条件：
   - **最终目标不变**：顶层定理（一般数域 Hecke L 函数在 Re s > 7/8 无零点）的陈述不能动，任何改动都不得削弱最终结论；
   - **可审查**：PR 说明列出新旧陈述对照，并说明修正版为什么仍符合论文原意（给出论文行号）；
   - **共享定义只由一个任务修改**：`WholeMomentProfileControl` 归 MOM_UNIFORM_AMPLIFY。改别的任务负责的共享定义之前，先在对方 PR 里留言；
   - **受影响的证明一起修好**：改了定义，依赖它的已有证明要一并修到编译通过；
   - **不要停在相对版本**：发现缺陷后直接修正并继续往下做，不要只写一个带额外假设的相对定理就停下。
4. 不要用 `sorry`、`axiom`、`native_decide`。
   - 每个提交信息末尾加一行署名（让 GitHub 把 ChatGPT 记为贡献者）：
     `Co-authored-by: ChatGPT <199175422+chatgpt-codex-connector[bot]@users.noreply.github.com>`
5. PR 说明写清楚四件事：
   - 主定理的陈述与假设；
   - 还差什么；
   - 编译了哪些模块、在什么环境下编译；
   - 公理清单。

## CI 预编译缓存

仓库的 release 里有 `lake-cache-<提交号>`，存放所有项目库以及 `vendor/class-field-theory`、TauCeti 两个包的 Lake 编译产物。Mathlib 及其依赖不在里面，仍由 `lake exe cache get` 下载。`dtests-handoff` 每次有改动 `.lean` 或 Lake 配置的推送，workflow "Lake cache release"（`.github/workflows/lake-cache-release.yml`）就在 GitHub runner 上增量编译全部库，发布新的 `lake-cache-<提交号前 7 位>`（只保留最新 3 个），不用再在本地生成。恢复缓存后 `lake build` 只重编分支自己改动过的模块及其下游。

**每分支增量缓存**：`restore-lake-cache` 解开 release 之后，还会从 Actions cache 恢复本分支上一次运行编出的 `.lake/build` 产物（先找同一 workflow 的同一个 job，其次本分支任意 job，PR 再退到 base 分支），并在 job 结束时（编译失败、超时也一样）把本分支编过的文件存回去，键为 `lake-build-v1-<工具链哈希>-<分支>:<job>:<run>`。这样同一分支推一个小修改后只重编改动的部分。已经接入 `@dtests-handoff` 的 workflow 不用改。实测（`ci/branch-cache`，`HeckeSkeleton.Principal`）：第一次 3 分钟超时失败，仍保存了 245 个文件；第二次接着编完剩下 235 个模块，用时 16 分钟，保存 41 MB；第三次 22 秒（全部 `Replayed`），整个 job 不到 5 分钟。每条缓存只含本分支自己编出的模块，一般几十到几百 MB。仓库的 Actions cache 共 10 GB，超出时按最久未用淘汰；"Lake cache release" 发布后会删掉已关闭 PR、已删除分支的条目，以及每条线上较旧的条目。`with: branch-cache: "false"` 关闭，`"restore"` 只恢复不保存。不要给 `leanprover/lean-action` 开 `use-github-cache: "true"`：它在编译之前就把整个 `.lake`（含 Mathlib，每条约 2 GB）存一份，不含项目产物，还会把每分支缓存挤掉。

**接入**：在 workflow 里 `actions/checkout` 和 `leanprover/lean-action`（`use-mathlib-cache: "true"`）之后、`lake build` 之前加一步：

```yaml
      - name: Restore precompiled project artifacts
        uses: Rogerhu12/hecke-seven-eighths/.github/actions/restore-lake-cache@dtests-handoff
```

分支里已经有 `.github/actions/restore-lake-cache` 时也可以写 `uses: ./.github/actions/restore-lake-cache`。默认取最新的已发布（非草稿）`lake-cache-*` release，也可以用 `with: tag: lake-cache-xxxxxxx` 指定。只需要 `contents: read` 权限。如果同一个 job 还用 `actions/cache` 恢复 `.lake`，把这一步放在它后面。

**说明**
- 缓存在哪个提交上生成，记在 release 的 `lake-cache-manifest.json` 里。分支相对这个提交改过的 `.lean` 文件和它们的下游会正常重编，其余模块都是 `Replayed`。
- 本地生成的旧 release（`lake-cache-76c696e`）不含 `HeckeSkeleton`，因为本地编出的 `HeckeSkeleton` 产物与 CI 重编出的哈希对不上，下游 44 个 `*Inputs` 模块也得重编。CI 生成的 release 包含 `HeckeSkeleton`，没有这个问题。
- 每分支缓存后解开、覆盖 release 里的同名文件，因为它是按本分支的源文件编出的。旧产物不会导致错误：Lake 按 trace 里的输入哈希判断，源文件或依赖变了就重编。唯一的代价是分支合并了 base 的新改动之后，本分支缓存里被 base 改过的模块要重编一次。
- 生成缓存时，工作区里源文件与目标提交不同的模块及其下游不打包，名单在 manifest 的 `skipped_stale_modules` 里。
- 实测（`lake-cache-76c696e`，ubuntu-24.04，`LEAN_NUM_THREADS=2`）：恢复缓存约 30–50 秒，`lake build HeckeSkeleton.Principal` 共 12540 个任务，只编译 106 个模块（73 个 `HeckeSkeleton.*`、31 个 import 了 `HeckeSkeleton` 的 `*Inputs` 模块、2 个 `skipped_stale_modules`），其余全部 `Replayed`，用时约 7 分钟；整个 job 约 10 分钟。
- 只打包 Lake 判断"已是最新"所需的文件：`.trace`、`.olean`、`.ilean`、`.c`，module 系统的模块还有 `.olean.server`、`.olean.private`、`.ir`、`.ir.sig`，以及这些文件各自的 `.hash`。`ir/**.setup.json` 每次编译前都会重新生成，不打包。缺任何一个必需文件（包括 `.c`）Lake 都会重编该模块。
- Windows 上编出的产物可以直接给 Linux CI 用：Lake 对 `.lean` 源文件按换行归一化（CRLF 转 LF）后取哈希，trace 里的路径只是说明文字，不参与哈希。

**底层库变了怎么重新生成**：一般不用管，"Lake cache release" 会自动生成并发布。需要手动时在 Actions 里对 `dtests-handoff` 运行这个 workflow（`base-tag` 可指定起点 release，可以是草稿）；编译超过约 5 小时会保存进度并自动续跑（最多两次）。在 `ci/` 分支上手动运行只会建草稿 release，各分支不会用到。本地生成的办法见 `scripts/build_lake_cache.py` 开头的说明。
