"""NSI-style neuro-symbolic agent for NesyLink.

Architecture transferred from "Lifting Traces to Logic: Programmatic Skill
Induction with Neuro-Symbolic Learning" (NSI):

- phi (neural grounding): Qwen2.5-VL-3B translates pixel frames into symbolic
  predicates at keyframes (``grounding/``).
- Z (symbolic state): ``grounding.schema.SymbolicState`` plus cross-room
  ``memory.Memory``.
- G (symbolic execution graph): ``graph.py`` interpreter over
  DataOp/CheckOp/LoopOp/PrimitiveOp/TerminalOp nodes; primitive skills live in
  ``skills.py``; top-level task programs are induced by the GPT-4o pipeline in
  ``induction/`` and frozen as JSON artifacts.
- Perceive-Think-Act: ``agent.Policy`` perceives at keyframes, propagates the
  state with the formalized transition model between keyframes (``tracker.py``),
  and emits one primitive action per ``env.step``.
"""

from __future__ import annotations
