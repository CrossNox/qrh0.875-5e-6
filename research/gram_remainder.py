# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Compile the centered Gram remainder checkpoint against pinned upstream."""

import logging
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY / "scripts"))

from verify_oai import compile_local_oai_module, verify_upstream_checkout, UPSTREAM_REVISION


def verify_centered_gram_remainder() -> None:
    """Check the source-connected centered remainder proofs."""
    upstream_repository = REPOSITORY.parent / "rh-upstream"
    verify_upstream_checkout(upstream_repository, UPSTREAM_REVISION)
    compile_local_oai_module(upstream_repository, REPOSITORY / "lean", "GramCenteredRemainder")


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(message)s", stream=sys.stdout)
    verify_centered_gram_remainder()
