"""Qwen2.5-VL grounding model: frame -> SymbolicState.

Heavy dependencies (torch/transformers) are imported inside functions so the
symbolic layer stays importable on machines without them.

Environment variables:
    NSI_VLM_MODEL    base model dir (default /root/autodl-tmp/models/Qwen2.5-VL-3B-Instruct)
    NSI_VLM_ADAPTER  optional LoRA adapter dir
    NSI_VLM_4BIT     "1" (default) to load the base model in 4-bit
"""

from __future__ import annotations

import os

import numpy as np

from .prompts import IMAGE_SCALE, SYSTEM_PROMPT, USER_PROMPT
from .schema import SymbolicState

DEFAULT_MODEL_DIR = "/root/autodl-tmp/models/Qwen2.5-VL-3B-Instruct"
MAX_NEW_TOKENS = 220


def frame_to_image(frame: np.ndarray):
    from PIL import Image

    image = Image.fromarray(np.asarray(frame, dtype=np.uint8))
    if IMAGE_SCALE != 1:
        image = image.resize(
            (int(round(image.width * IMAGE_SCALE)),
             int(round(image.height * IMAGE_SCALE))),
            Image.NEAREST,
        )
    return image


def build_messages(image) -> list[dict]:
    return [
        {"role": "system", "content": [{"type": "text", "text": SYSTEM_PROMPT}]},
        {
            "role": "user",
            "content": [
                {"type": "image", "image": image},
                {"type": "text", "text": USER_PROMPT},
            ],
        },
    ]


class VLMGroundingModel:
    def __init__(self, model, processor) -> None:
        self.model = model
        self.processor = processor
        self.last_raw: str = ""

    # ------------------------------------------------------------------

    @classmethod
    def load_default(cls) -> "VLMGroundingModel":
        return cls.load(
            model_dir=os.environ.get("NSI_VLM_MODEL", DEFAULT_MODEL_DIR),
            adapter_dir=os.environ.get("NSI_VLM_ADAPTER") or None,
            four_bit=os.environ.get("NSI_VLM_4BIT", "1") == "1",
        )

    @classmethod
    def load(cls, *, model_dir: str, adapter_dir: str | None = None,
             four_bit: bool = True) -> "VLMGroundingModel":
        import torch
        from transformers import AutoProcessor, Qwen2_5_VLForConditionalGeneration

        kwargs: dict = {"torch_dtype": torch.bfloat16, "device_map": "cuda:0"}
        if four_bit:
            from transformers import BitsAndBytesConfig

            kwargs["quantization_config"] = BitsAndBytesConfig(
                load_in_4bit=True,
                bnb_4bit_compute_dtype=torch.bfloat16,
                bnb_4bit_quant_type="nf4",
                bnb_4bit_use_double_quant=True,
            )
        model = Qwen2_5_VLForConditionalGeneration.from_pretrained(model_dir, **kwargs)
        if adapter_dir:
            from peft import PeftModel

            model = PeftModel.from_pretrained(model, adapter_dir)
        model.eval()
        processor = AutoProcessor.from_pretrained(model_dir)
        return cls(model, processor)

    # ------------------------------------------------------------------

    def generate(self, frame: np.ndarray, *, temperature: float = 0.0) -> str:
        import torch

        image = frame_to_image(frame)
        messages = build_messages(image)
        text = self.processor.apply_chat_template(
            messages, tokenize=False, add_generation_prompt=True
        )
        inputs = self.processor(
            text=[text], images=[image], return_tensors="pt"
        ).to(self.model.device)
        with torch.inference_mode():
            output = self.model.generate(
                **inputs,
                max_new_tokens=MAX_NEW_TOKENS,
                do_sample=temperature > 0,
                temperature=temperature if temperature > 0 else None,
                top_p=0.9 if temperature > 0 else None,
            )
        trimmed = output[0][inputs["input_ids"].shape[1]:]
        return self.processor.decode(trimmed, skip_special_tokens=True)

    def ground(self, frame: np.ndarray) -> SymbolicState:
        """Parse-validated grounding with one sampled retry on failure."""
        self.last_raw = self.generate(frame, temperature=0.0)
        try:
            return SymbolicState.from_text(self.last_raw)
        except ValueError:
            self.last_raw = self.generate(frame, temperature=0.3)
            return SymbolicState.from_text(self.last_raw)
