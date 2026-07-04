"""Merge the QLoRA adapter into a bf16 model for faster inference.

    python -m nsi_agent.grounding.merge_lora \
        --model /root/autodl-tmp/models/Qwen2.5-VL-3B-Instruct \
        --adapter /root/autodl-tmp/ckpt/grounding_lora/final \
        --out /root/autodl-tmp/models/grounding_merged
"""

from __future__ import annotations

import argparse

import torch
from peft import PeftModel
from transformers import AutoProcessor, Qwen2_5_VLForConditionalGeneration


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--adapter", required=True)
    parser.add_argument("--out", required=True)
    args = parser.parse_args()

    model = Qwen2_5_VLForConditionalGeneration.from_pretrained(
        args.model, torch_dtype=torch.bfloat16, device_map="cpu"
    )
    model = PeftModel.from_pretrained(model, args.adapter)
    model = model.merge_and_unload()
    model.save_pretrained(args.out)
    AutoProcessor.from_pretrained(args.model).save_pretrained(args.out)
    print(f"merged model saved to {args.out}")


if __name__ == "__main__":
    main()
