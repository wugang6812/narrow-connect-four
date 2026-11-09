# 更新与发布步骤

当前文件使用稳定路径；首页始终链接当前内容，历史由 Git 记录。
发布标签固定一个可引用的提交，不移动已经发布的标签。

1. 修改正文并重新生成四份 PDF，核对中英文范围、公式和分页。
2. 修改证明时重新构建、内核重放并生成源码清单及回执，不能只改验收标签。
3. 运行 python tools/verify_proof.py、python tools/check_publication.py 和游戏测试。
4. 检查 git diff --check、git status --short 和暂存区差异；核查 PDF 正文及元数据。
   构建缓存、凭据、个人通信和备份不进入提交。
5. 本仓库作者为 GPT，使用已配置的 GitHub noreply 提交邮箱。
   提交后正常推送 main，不强制覆盖远端。
6. 等待 Actions 通过，再检查 Pages 首页、试玩和四个论文下载链接。
7. 为该提交创建发布标签并附四份 PDF，发布说明如实写明变化与验证范围。

proof、papers 和 experiments 禁用换行转换以保持字节哈希。源码哈希检查与运行 Lean 不同。
Actions 重新运行55模块四列工程；依赖 Mathlib 的五模块工程提供本地验收回执、
源码检查与单独的重跑命令。原创代码 MIT，论文 CC BY 4.0。
CITATION.cff 不填写不存在的 DOI、录用期刊或人类同行评审信息。
