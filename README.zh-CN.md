# 窄棋盘重力四子棋

[English](README.md) · [项目首页](https://wugang6812.github.io/narrow-connect-four/) · [在线试玩](https://wugang6812.github.io/narrow-connect-four/game/)

**一至四列、任意有限高度的重力四子棋，空盘最优结果均为和棋。** 双方各有固定不败策略；有底边、无顶边的真正无限高度也有相应结论。本仓库提供数学证明、最优主动换列次数、Lean 源码、配套算法论文和规则演示游戏。

## 阅读论文

| 论文 | 中文 | English |
|---|---|---|
| **和棋策略与最优主动换列次数**：全部有限高度、无限高度及次数的上下界 | [PDF](papers/paper-zh.pdf) · [正文](papers/paper-zh.md) | [PDF](papers/paper-en.pdf) · [source](papers/paper-en.md) |
| **统一回应算法与交替段压缩**：证书、选列顺序、九段界及区间扫描 | [PDF](papers/algorithm-zh.pdf) · [正文](papers/algorithm-zh.md) | [PDF](papers/algorithm-en.pdf) · [source](papers/algorithm-en.md) |

最优次数及其完整数学证明放在第一篇。算法和压缩在第二篇展开。[排版源码与参考文献](papers/README.md)一并提供。

## 结论范围

| 棋盘 | 空盘结果 |
|---|---|
| 一至三列，任意有限高度 | 和棋 |
| 四列，任意有限高度，含全部奇偶高度 | 和棋 |
| 一至四列，真正无限高 | 固定策略保护每个有限前缀，无人首次获胜；无限进行定义为和棋 |
| 五列及以上 | 不属于本文分类范围 |

四列棋盘保证不败所需的**最坏情形主动换列次数最优值**为：

| 高度 | 先手 | 后手 |
|---|---:|---:|
| 0、1 | 0 | 0 |
| 2、3 | 0 | 1 |
| 至少5的奇数 | 0 | 1 |
| 至少4的偶数 | 1 | 1 |
| 真正无限高 | 0 | 1 |

主动换列指对方刚下的列仍可落子，自己却改走别列。先手首子免费，立即获胜的回应照常计数。一至三列的双方最优主动预算均为零。此指标与胜负结果、总换列次数不同。

论文将经典偶数高度后手配对策略归于 Allis，并交代 Yamaguchi 等人的无限棋盘研究，不宣称整套和棋分类首次被发现。

## 核验证明

- [proof/Covering](proof/Covering/)：**55个模块**，四列全部有限高度、双方统一回应、精确主动预算及完整历史语义，只需 Lean 随附库。
- [proof/Narrow](proof/Narrow/)：**5个模块**，一至三列有限高度及一至四列无限高度，使用固定版本 Mathlib。

两工程均已重新编译并以信任级别零导入重放。20项重点声明的公理闭包仅含 `propext`、`Classical.choice`、`Quot.sound`。两工程的棋盘模型不同，模型间等价尚未形式化。

安装 Python 3.10 以上版本后，在仓库根目录执行：

~~~sh
python tools/verify_proof.py
~~~

默认核对源码哈希与回执，不运行 Lean。安装 **Lean 4.34.0-rc2** 并将 `lean` 加入 PATH，或设置 `LEAN_BIN`，再运行：

~~~sh
python tools/verify_proof.py --build --replay
~~~

这会重新构建并内核重放55模块工程。GitHub Actions 同时运行该流程和游戏测试。依赖 Mathlib 的支持工程有独立复现命令，详见[验证说明](docs/verification.md)和[验收回执](audit/proof-verification.json)。

通用多目标引理、总换列上界、九段界背后的完整事件计数、完整压缩程序的精化及成本证明，不全属于已验收的 Lean 根定理；论文逐项说明。[有限实验](experiments/)不替代任意高度证明。

## 试玩与测试

[在线试玩](https://wugang6812.github.io/narrow-connect-four/game/)，或打开 [game/index.html](game/index.html)。行列可选1至20，支持双人、C/WebAssembly 电脑及三档难度，含标准棋盘先手策略的离线使用。

电脑是单独的程序，窄棋盘定理不保证它每一步都最优。标准7列6行策略用于受支持的先手分支，其他局面采用限时搜索。详见[电脑说明](docs/bot.md)和[互打结果](docs/selfplay.md)。

Node.js 20 以上版本可运行：

~~~sh
node --test tests/engine.test.cjs tests/bot.test.cjs
python tools/check_publication.py
~~~

测试覆盖重力、各方向四连、终局优先级、悔棋与棋谱，以及全部400种尺寸的抽样对局。`tools/test_browser.py` 通过 Playwright 检查真实浏览器交互。

## 许可和引用

项目以 **GPT** 署名。原创代码 [MIT](LICENSE)，两篇论文及源码 [CC BY 4.0](papers/LICENSE.txt)；保留[第三方许可](THIRD_PARTY.md)。引用信息见 [CITATION.cff](CITATION.cff)及 [references.bib](papers/references.bib)。

公开的是研究稿件和可复核材料，不表示期刊录用或已经过人类同行评审。当前文件使用稳定地址，修改由 Git 提交和发布标签记录。
