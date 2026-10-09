# GitHub 公开研究材料的操作顺序

本项目采用本地 Git 管理版本，再推送到 GitHub 的方式发布。账号为 `wugang6812`，仓库名为 `narrow-connect-four`。

## 整理文件

把读者需要的文件放在明确的目录中。`README` 解释项目、运行方法和结论范围；`papers` 保存论文；`proof` 保存证明与验收记录；`game` 保存演示；`tests` 保存可运行检查。缓存、凭据、个人备份设置和编辑往来不上传。

`.gitignore` 负责排除临时文件，但它不会自动移除已经提交过的文件。因此首次提交前就检查文件列表。证明归档需要原字节与哈希一致，`.gitattributes` 对 `proof` 禁用换行转换。带有构建哈希的 C 源码和策略资产也保留原字节，其他文本使用统一的 LF 换行。

原创代码采用 MIT，论文采用 CC BY 4.0；第三方重放工具仍保留 Apache 2.0。这些许可说明读者能怎样复用材料。`CITATION.cff` 帮助读者引用，不能把未获录用论文写成已发表文章，也不虚构 DOI。

## 在本地提交

初始化主分支并设置本仓库作者信息：

```sh
git init -b main
git config user.name "GPT"
git config user.email "340176718+wugang6812@users.noreply.github.com"
```

这里使用 GitHub 的 noreply 邮箱，避免额外公开注册邮箱。论文中作者主动提供的通讯邮箱是另一件事。设置只影响当前仓库。

提交前先运行测试和证明来源检查，再看文件列表：

```sh
node --test tests/engine.test.cjs tests/bot.test.cjs
python tools/verify_proof.py
git status --short
git add .
git diff --cached --stat
git commit -m "Publish narrow-board proof artifact and C-powered browser game"
```

提交是一个可追溯的版本节点。后续每完成一项能说明清楚的修改，再提交一次，不需要每次按键都提交。保留完整源码比只上传可执行文件更方便复核和维护。

## 创建远端并推送

通过 GitHub 官方 CLI 的设备授权登录，密码和手机验证码只输入 GitHub 页面。普通仓库权限用于创建和推送；包含 `.github/workflows` 时，OAuth 还需要 `workflow` 权限，这是 GitHub 对工作流文件的要求。

本地已有首次提交时，创建空远端，不再在网页上另外生成一套 README 历史。设置 `origin` 指向自己的仓库，再推送 `main`。推送后核对远端提交号、文件和作者。

## 运行自动检查与在线演示

本项目的 Actions 工作流运行游戏测试和原证明文件/收据检查。它没有重新编译全部 Lean 模块，不能把绿色状态说成新的完整内核验收。工作流引用固定的官方 Action 提交号，便于追踪实际执行版本。

GitHub Pages 从主分支部署静态演示，浏览器执行游戏和 C 编译成的 WebAssembly。仓库页面用于阅读代码，Pages 地址用于实际玩游戏。启用后应打开在线地址，检查页面、棋子、电脑落子及论文链接。

## 后续更新

修改后重复“测试、检查差异、提交、推送、检查线上结果”。远端更新会触发自动检查和 Pages 部署。只使用一台工作机器时通常不需要分支协作流程；涉及较大的实验或重构，可以另建分支再合并。

不要为了上传新版本而强制覆盖旧历史。发布错误时做一次修复提交，并说明影响范围。标签适合标记可引用版本；使用 `v0.1.0` 等版本号后，记录对应提交，避免悄悄移动已有发布标签。
