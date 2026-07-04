"""GPT-4o client for the induction pipeline (training time only)."""

from __future__ import annotations

import json
import os
import time
from pathlib import Path

CONFIG_FILE = Path.home() / ".config" / "nsi_agent" / "openai.env"
MODEL = os.environ.get("NSI_INDUCTION_MODEL", "gpt-4o")


def _load_config() -> dict[str, str]:
    config: dict[str, str] = {}
    if CONFIG_FILE.exists():
        for line in CONFIG_FILE.read_text("utf-8").splitlines():
            if "=" in line and not line.startswith("#"):
                key, _, value = line.partition("=")
                config[key.strip()] = value.strip()
    for key in ("OPENAI_API_KEY", "OPENAI_BASE_URL"):
        if os.environ.get(key):
            config[key] = os.environ[key]
    return config


_CLIENT = None


def client():
    global _CLIENT
    if _CLIENT is None:
        from openai import OpenAI

        config = _load_config()
        _CLIENT = OpenAI(
            api_key=config.get("OPENAI_API_KEY"),
            base_url=config.get("OPENAI_BASE_URL"),
        )
    return _CLIENT


def structured_completion(system: str, user: str, json_schema: dict,
                          *, schema_name: str = "program",
                          temperature: float = 0.0, retries: int = 5) -> dict:
    """Chat completion constrained to a JSON schema; returns the parsed dict."""
    last_error: Exception | None = None
    for attempt in range(retries):
        try:
            response = client().chat.completions.create(
                model=MODEL,
                temperature=temperature,
                max_tokens=14000,
                messages=[
                    {"role": "system", "content": system},
                    {"role": "user", "content": user},
                ],
                response_format={
                    "type": "json_schema",
                    "json_schema": {
                        "name": schema_name,
                        "strict": True,
                        "schema": json_schema,
                    },
                },
            )
            return json.loads(response.choices[0].message.content)
        except Exception as exc:   # noqa: BLE001 - retry then surface
            last_error = exc
            time.sleep(2.0 * (attempt + 1))
    raise RuntimeError(f"GPT-4o structured completion failed: {last_error}")
