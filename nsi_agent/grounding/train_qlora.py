"""QLoRA fine-tuning of Qwen2.5-VL-3B on (frame, symbolic-state) pairs.

    python -m nsi_agent.grounding.train_qlora \
        --data /root/autodl-tmp/data/grounding \
        --model /root/autodl-tmp/models/Qwen2.5-VL-3B-Instruct \
        --out /root/autodl-tmp/ckpt/grounding_lora
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import torch
from PIL import Image
from torch.utils.data import Dataset
from transformers import (
    AutoProcessor,
    BitsAndBytesConfig,
    Qwen2_5_VLForConditionalGeneration,
    Trainer,
    TrainingArguments,
)
from peft import LoraConfig, get_peft_model, prepare_model_for_kbit_training

from .prompts import IMAGE_SCALE, SYSTEM_PROMPT, USER_PROMPT

IGNORE_INDEX = -100


class GroundingDataset(Dataset):
    def __init__(self, root: Path, split: str) -> None:
        self.root = root
        self.rows = [
            json.loads(line)
            for line in (root / f"{split}.jsonl").read_text("utf-8").splitlines()
            if line.strip()
        ]

    def __len__(self) -> int:
        return len(self.rows)

    def __getitem__(self, index: int) -> dict:
        row = self.rows[index]
        image = Image.open(self.root / row["image"]).convert("RGB")
        if IMAGE_SCALE != 1:
            image = image.resize(
                (int(round(image.width * IMAGE_SCALE)),
                 int(round(image.height * IMAGE_SCALE))),
                Image.NEAREST,
            )
        return {"image": image, "label": row["label"]}


class Collator:
    def __init__(self, processor) -> None:
        self.processor = processor

    def __call__(self, batch: list[dict]) -> dict:
        prompts, fulls, images = [], [], []
        for item in batch:
            messages = [
                {"role": "system", "content": [{"type": "text", "text": SYSTEM_PROMPT}]},
                {"role": "user", "content": [
                    {"type": "image", "image": item["image"]},
                    {"type": "text", "text": USER_PROMPT},
                ]},
            ]
            prompt = self.processor.apply_chat_template(
                messages, tokenize=False, add_generation_prompt=True
            )
            prompts.append(prompt)
            fulls.append(prompt + item["label"] + "<|im_end|>")
            images.append(item["image"])

        encoded = self.processor(
            text=fulls, images=images, return_tensors="pt", padding=True
        )
        labels = encoded["input_ids"].clone()
        labels[encoded["attention_mask"] == 0] = IGNORE_INDEX
        # Mask everything up to the end of each prompt (train on the answer
        # only). The prompt length must be measured on PROCESSED ids: the
        # processor expands the image placeholder into many vision tokens,
        # so the raw-tokenizer length would cut the mask far too early.
        for i, (prompt, image) in enumerate(zip(prompts, images)):
            prompt_ids = self.processor(
                text=[prompt], images=[image], return_tensors="pt"
            )["input_ids"]
            labels[i, : prompt_ids.shape[1]] = IGNORE_INDEX
        encoded["labels"] = labels
        return encoded


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--model", type=str, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--epochs", type=float, default=2.0)
    parser.add_argument("--batch", type=int, default=4)
    parser.add_argument("--grad-accum", type=int, default=4)
    parser.add_argument("--lr", type=float, default=1e-4)
    parser.add_argument("--lora-rank", type=int, default=16)
    parser.add_argument("--init-adapter", type=str, default=None,
                        help="continue training from an existing LoRA adapter")
    args = parser.parse_args()

    processor = AutoProcessor.from_pretrained(args.model)
    model = Qwen2_5_VLForConditionalGeneration.from_pretrained(
        args.model,
        torch_dtype=torch.bfloat16,
        device_map="cuda:0",
        quantization_config=BitsAndBytesConfig(
            load_in_4bit=True,
            bnb_4bit_compute_dtype=torch.bfloat16,
            bnb_4bit_quant_type="nf4",
            bnb_4bit_use_double_quant=True,
        ),
    )
    model = prepare_model_for_kbit_training(model)
    if args.init_adapter:
        from peft import PeftModel

        model = PeftModel.from_pretrained(
            model, args.init_adapter, is_trainable=True
        )
    else:
        lora = LoraConfig(
            r=args.lora_rank,
            lora_alpha=args.lora_rank * 2,
            lora_dropout=0.05,
            bias="none",
            task_type="CAUSAL_LM",
            target_modules=[
                "q_proj", "k_proj", "v_proj", "o_proj",
                "gate_proj", "up_proj", "down_proj",
            ],
        )
        model = get_peft_model(model, lora)
    model.print_trainable_parameters()
    model.config.use_cache = False

    dataset = GroundingDataset(args.data, "train")
    print(f"train samples: {len(dataset)}")

    trainer = Trainer(
        model=model,
        args=TrainingArguments(
            output_dir=str(args.out),
            num_train_epochs=args.epochs,
            per_device_train_batch_size=args.batch,
            gradient_accumulation_steps=args.grad_accum,
            learning_rate=args.lr,
            lr_scheduler_type="cosine",
            warmup_ratio=0.03,
            logging_steps=20,
            save_strategy="epoch",
            bf16=True,
            gradient_checkpointing=True,
            gradient_checkpointing_kwargs={"use_reentrant": False},
            remove_unused_columns=False,
            dataloader_num_workers=4,
            report_to=[],
        ),
        train_dataset=dataset,
        data_collator=Collator(processor),
    )
    trainer.train()
    model.save_pretrained(str(args.out / "final"))
    processor.save_pretrained(str(args.out / "final"))
    print(f"saved adapter to {args.out / 'final'}")


if __name__ == "__main__":
    main()
