# 2026-07-16 独立复测证据

本目录来自同步到 RTX 4090 服务器的本地项目工作树。代码基线为
`c024663b92c10afd9b91db5d89577121ab26f027`，其父线已合入 NesyLink
`main@036df78f7d6981000444f1e889f21435854e352a`。评测使用官方
`--info-mode safe`、显式 `--task-policy`、`seed=0`、每任务 1 个 episode。

| 任务 | 结果 | 步数 | 奖励 |
| --- | --- | ---: | ---: |
| Task 1 | 成功 | 280 | 127.150 |
| Task 2 | 成功 | 176 | 128.240 |
| Task 3 | 成功 | 541 | 164.590 |
| Task 4 | 成功 | 1514 | 264.760 |
| Task 5 | 按设计仅保留轨迹 | 1000 | 56.700 |

Task 5 不把 `world_completed` 作为项目成功要求。当次 `safe` 运行于第 1000
步 `agent_dead`；动作级冻结轨迹单独保存，不将其历史 `success` 字段当作
当次新环境的成功率证据。

关键文件：

- [`final/evaluate_5tasks.json`](final/evaluate_5tasks.json)：五任务机读汇总与事件统计。
- [`final/evaluate_5tasks.log`](final/evaluate_5tasks.log)：完整终端输出。
- [`final/evaluate_5tasks.command.txt`](final/evaluate_5tasks.command.txt)：实际执行命令。
- [`final/task5_action_trace.json`](final/task5_action_trace.json)：Task 5 动作级冻结轨迹。
- [`final/pytest_after_compat.txt`](final/pytest_after_compat.txt)：12/12 单元测试通过。
- [`final/lean_build.log`](final/lean_build.log)：Lean 4.29.0 下 26/26 目标构建成功。
- [`final/manifest.txt`](final/manifest.txt)：代码、上游、GPU、Python、模型和评测参数。
- [`final/evidence_sha256.txt`](final/evidence_sha256.txt) 与
  [`final/source_sha256.txt`](final/source_sha256.txt)：证据和关键源码校验值。

原始证据包从服务器下载时的 SHA-256 为
`2dd7fe3757f4195168e6ed0f8b118b5ecb5c6b0d5d4eb76872a8a823bfa49c38`。
