# 数理逻辑课程设计提交包说明

本提交包的 Agent 代码基线为 `c024663b92c10afd9b91db5d89577121ab26f027`，已合入
NesyLink 上游 `main@036df78f7d6981000444f1e889f21435854e352a`。

## 提交内容

- `REPORT.md`：完整项目报告，包含定理列表、实验结果、输入边界和抽象假设。
- `lean/`：Lean 4.29.0 源码、`lakefile.lean`、`lake-manifest.json` 和工具链文件。
- `submission_agent.py`、`nsi_agent/`：最终黑盒 Agent 入口和全部实现源码。
- `nesylink/`、`utils/`：NesyLink 环境与最新版统一评测脚本。
- `models/grounding-v4b/grounding_v4b_lora/`：终版 QLoRA 适配器权重。
- `evidence/`：五任务评测、Task 5 动作轨迹、pytest、Lean 构建和哈希证据。

## Python 环境

建议使用 Python 3.10–3.12、CUDA GPU，并在提交包根目录执行：

```bash
python -m venv .venv
source .venv/bin/activate
pip install -e '.[pygame]'
pip install -r requirements-inference.txt
```

2026-07-16 证据环境使用 Python 3.12.3、RTX 4090、PyTorch 2.8.0+cu128、
Transformers 5.12.1、PEFT 0.19.1。

## 感知模型

提交包已包含项目训练得到的 QLoRA adapter。由于公开基座模型约 7GB，包内不重复
附带；请将 `Qwen/Qwen2.5-VL-3B-Instruct` 下载到本地目录后设置：

```bash
export NSI_VLM_MODEL=/absolute/path/to/Qwen2.5-VL-3B-Instruct
export NSI_VLM_ADAPTER="$PWD/models/grounding-v4b/grounding_v4b_lora"
export NSI_VLM_4BIT=0
```

若显存不足，可安装 `bitsandbytes` 并设置 `NSI_VLM_4BIT=1`。Adapter 的来源和
发布资产校验值见 `models/grounding-v4b/SOURCE.md`；包内文件的 SHA-256 见
`SUBMISSION_SHA256SUMS.txt`。

## 一键黑盒测评

最新版评测器无参数调用 `reset()`。本 Agent 通过五个显式 `--task-policy` 绑定，
只接收 raw pixels、`last_reward`、显式物品栏和绑定后的 `task_id`：

```bash
python utils/evaluate_policy.py \
  --tasks mathematical_logic/task_1 mathematical_logic/task_2 \
          mathematical_logic/task_3 mathematical_logic/task_4 \
          mathematical_logic/task_5 \
  --task-policy mathematical_logic/task_1=submission_agent.py \
  --task-policy mathematical_logic/task_2=submission_agent.py \
  --task-policy mathematical_logic/task_3=submission_agent.py \
  --task-policy mathematical_logic/task_4=submission_agent.py \
  --task-policy mathematical_logic/task_5=submission_agent.py \
  --info-mode safe --num-envs 1 --seed 0 \
  --json-out evaluation.json
```

2026-07-16 同版复测中 Task 1–4 分别以 280 / 176 / 541 / 1514 步完成。
Task 5 按项目任务设计仅提交运行轨迹和阶段性进展，不把 `world_completed` 作为
成功要求；动作级轨迹位于 `evidence/final/task5_action_trace.json`。

## Lean 检查

```bash
cd lean
lake build
```

证据环境使用 Lean 4.29.0 / Lake 5.0.0，26/26 个构建目标成功。源码声明级扫描
未发现 `sorry`、`admit` 或自定义 `axiom`；完整日志见 `evidence/final/`。

## 快速完整性检查

在提交包根目录执行：

```bash
shasum -a 256 -c SUBMISSION_SHA256SUMS.txt
python -m compileall -q nesylink nsi_agent utils submission_agent.py tests
python -m pytest -q
```
