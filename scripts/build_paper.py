# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Build the manuscript and publish its PDF at the repository root."""

import logging
import shutil
import subprocess
from pathlib import Path


def build_paper() -> None:
    """Compile the TeX twice and copy the completed PDF to the root."""
    repo_dir = Path(__file__).resolve().parents[1]
    build_dir = repo_dir / "build/tex"
    build_dir.mkdir(parents=True, exist_ok=True)

    for pass_number in range(1, 3):
        logging.info("Compiling tex/paper.tex, pass %s of 2", pass_number)
        subprocess.run(
            [
                "pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                f"-output-directory={build_dir}", "tex/paper.tex",
            ],
            cwd=repo_dir,
            check=True,
        )

    shutil.copyfile(build_dir / "paper.pdf", repo_dir / "paper.pdf")
    logging.info("Built %s", repo_dir / "paper.pdf")


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    build_paper()
