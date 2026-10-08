# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Compile the research notes into PDFs."""

import logging
import subprocess
from pathlib import Path


def build_research_notes() -> None:
    repository = Path(__file__).resolve().parents[1]
    notes_directory = repository / "research"
    output_directory = repository / "build/research"
    output_directory.mkdir(parents=True, exist_ok=True)

    for source_path in sorted(notes_directory.glob("*.tex")):
        for pass_number in range(1, 3):
            logging.info("Compiling %s, pass %s of 2", source_path.name, pass_number)
            compilation = subprocess.run(
                [
                    "pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                    f"-output-directory={output_directory}", str(source_path),
                ],
                cwd=repository,
                capture_output=True,
                text=True,
            )
            if compilation.returncode != 0:
                logging.error("%s\n%s", compilation.stdout, compilation.stderr)
                compilation.check_returncode()

            for line in compilation.stdout.splitlines():
                if line.startswith(("LaTeX Warning:", "Overfull ", "Underfull ")):
                    logging.warning("%s: %s", source_path.name, line)

        logging.info("Built %s", output_directory / source_path.with_suffix(".pdf").name)


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    build_research_notes()
