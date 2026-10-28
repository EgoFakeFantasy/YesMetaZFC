# 内部有限真值与固定源查询

本库为 YesMetaZFC 的内部程序解释、局部 Skolem 查询及相对内模型研究提供基础接口。
它使用原模型中的集合、函数图、内部自然数和实际完整见证，不要求模型外部良基或 ω 标准。

## 入口与结构

统一入口为 `import YesMetaZFC.SetTheory.InnerModel.FiniteTruth`，亦由 `InnerModel` 导出。
声明位于 `YesMetaZFC.SetTheory.InnerModel.FiniteTruth` 及其子命名空间。

| 目录 | 内容 |
| --- | --- |
| [Foundation](Foundation/ProjectCompleteness.lean) | 原推导桥、有限变量块、Lévy 替换及保护槽检查 |
| [Internal](Internal/PredicateProgram.lean) | 内部合法程序、编号、完整赋值图、真值历史及 Δ₀ 证书 |
| [Jensen](Jensen/IndexedSigma1Compiler.lean) | 原 J 层中的完整证书、规范见证选择、源编译与实际真值表 |
| [Powerless](Powerless/Theory.lean) | 无幂集背景下实际塌缩及其完整图证书，供数码构造使用 |

## 对象语言与背景理论

公式、句子和推导复用原 `SetTheory.Definitional.Project` 纯隶属语言及推导核。
公开对象结果采用 `Project.Derives ZF sentence` 或固定源索引的相应定理模式。
语义辅助定理中的 `M.Models ZF`、`M.Models KP` 等假设保持显式，不将小层自动当作 ZF 模型。

[ProjectCompleteness](Foundation/ProjectCompleteness.lean) 将任意模型中的闭句结论接回原推导。
它要求理论包含原外延性公理，并使用上游语言对应与 universe 0 的强完备性接口；
输入语义结论必须覆盖该 universe 的全部背景模型，不能仅给出一个具体模型。

[ZFMinus](Powerless/Theory.lean) 的实际定义是含无穷的 KP 加全部原分离与收集模式。
它不含 Power Set 或 Choice，也不应简称为原 KP，或据此声称已降低任意端点的理论强度。

## 已实现的对象出口

以下名称均在本库 `Jensen` 命名空间内；具体公理、参数和层预算以声明为准。

| 出口 | 精确用途 |
| --- | --- |
| [delta0Compilation_derives](Jensen/CanonicalDelta0ObjectTheorems.lean) | 原 FreeClosed Δ₀ 模板的同层代码及正负查询 |
| [predicateNumberedCompilation_derives](Jensen/CanonicalPredicateNumberedObjectTheorems.lean) | 指定保护槽的原谓词模板、内部数码与完整查询证书 |
| [indexedSigma1Source_derives](Jensen/IndexedSigma1SourceObjectTheorems.lean) | 固定保护槽 Σ₁ 正规源的同一索引及完整见证恢复 |
| [prefixSourceTable_derives](Jensen/PrefixSourceTableObjectTheorems.lean) | 全普通参数的实际前缀和受限表成员规格 |
| [restrictedTruthTableExists_derives](Jensen/RestrictedTruthTableObjectTheorems.lean) | 背景 ZF 中实际受限表的存在与唯一性 |
| [universalTruthSource_derives](Jensen/UniversalTruthSourceObjectTheorems.lean) | 任意给定同一通用表上的全部源环境查询 |
| [universalTruthProper_derives](Jensen/UniversalTruthObjectTheorems.lean) | 显式假设下通用表的包含、全参数覆盖及非成员性 |

## 外部源与内部程序的区别

`S1_binary (p+1)` 是外部固定的原 Σ₁ 正规源；`p` 是该模板的普通参数个数。
编译模式为每个这样的源生成原对象句子及推导，不把外部模板族改成一个内部全真值断言。
源代码、参数长度及空值先于全部源参数、给定通用表 T 和输入 x 选择。

内部解释器则量化模型自己的自然数码、有限长度、程序图和参数图。
合法谓词程序有五类指令：隶属、相等、或非、有界存在及只读谓词成员查询。
内部长度可以外部非标准；解释及完整历史并不将它解码为某个宿主有限 AST。
这一特定指令系统不等于任意集合 DSL 的统一解释器。

## 层预算与表的范围

同层结果保留原 `Jh_value_d α C`、层内对象及必要的 `ω ∈ C` 假设。
`Within_d` 要求原矩阵的整个见证 w 属于 C；输出属于 C 不能替代这一预算。
普通参数图保存全部普通参数，保护槽 A 经独立环境读取，不要求 `A ∈ C`。
需局部化谓词的接口显式要求 `AmenableSet_d C A`，不能从名称推断该性质自动成立。
同层有限构造不以“小层满足 Collection”作为隐含前提。

受限表在背景 ZF 的完整 `ω × U` 上实际分离得到，不预设表属于 C。
通用表使用原两参数 indexed 函数并取 `U=C`，允许第二坐标遍历全部层内参数图；
固定参数前缀的表是另一种接口，不能将事后产生的 T 偷换为已固定的普通参数。

通用表的非成员性来自固定一行对整个 C 的参数覆盖、同层传递包络和原 Foundation。
结论 `T ⊆ C ∧ T ∉ C` 中第二项是非成员性，不是 `T ≠ C` 或真子集断言。
它也不表示较小固定域上的分离失败、Tarski 非可定义性、最小 projectum 或表的 amenability。

## 尚待完成与验证

本库尚未构造 L[A] 的相对 rud 闭包、层递归及模型，也未完成任意 DSL 统一解释、
一般 Lévy Σ₁ 语法的正规化、projectum、mastercode amenability 或相应复杂度转移。
这些目标不作为当前接口的隐含前提，也不从现有局部表或非成员性结果推出。

本库沿用上游可信基与原推导可靠性／完备性桥，不添加 Lean `axiom` 声明或 `native_decide`。
`ZFMinus` 的对象公理谓词仅选择已有原公理与模式，不是新增 Lean 可信公理。
从仓库根目录运行既有验证命令：

```sh
lake --wfail build
bash scripts/check-all.sh
```
