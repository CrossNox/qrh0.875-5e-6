# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

import argparse
import shlex
import subprocess
from pathlib import Path


LEAN_IMAGE = "ghcr.io/leanprover-community/mathlib4/lean:latest"
TOOLCHAIN_VOLUME = "rh-lean-toolchains"

UPSTREAM_TARGETS = {
    "OAILowReflected": "OAI.NumberTheory.DirichletL.Detector.LowReflectedLength",
    "OAILowExponent": "OAI.NumberTheory.DirichletL.Reflection.LowExponent",
    "OAILowBranchSum": "OAI.NumberTheory.DirichletL.Reflection.LowBranchSum",
    "OAILowSector": "OAI.NumberTheory.DirichletL.Reflection.LowSector",
}


def build_upstream_oai_target(upstream_repo: Path, target: str) -> None:
    print(f"Building upstream OAI target {target}", flush=True)

    subprocess.run(
        [
            "docker",
            "run",
            "--rm",
            "--cpuset-cpus",
            "0-7",
            "--cpus",
            "8",
            "--memory",
            "14g",
            "--entrypoint",
            "/bin/bash",
            "--mount",
            f"type=bind,src={upstream_repo},dst=/home/lean/project",
            "--mount",
            f"type=volume,src={TOOLCHAIN_VOLUME},dst=/home/lean/.elan/toolchains",
            "--workdir",
            "/home/lean/project/lean",
            LEAN_IMAGE,
            "-lc",
            f"lake --quiet build +{target}:olean",
        ],
        check=True,
    )


def compile_local_oai_module(upstream_repo: Path, rh_repo: Path, module: str) -> None:
    print(f"Compiling {module}.lean against upstream OAI", flush=True)

    lean_command = (
        "LEAN_PATH=/home/lean/rh:${LEAN_PATH:?Lake did not set LEAN_PATH} "
        f"lean -R /home/lean/rh -o /home/lean/rh/{module}.olean "
        f"/home/lean/rh/{module}.lean"
    )

    subprocess.run(
        [
            "docker",
            "run",
            "--rm",
            "--cpuset-cpus",
            "0-3",
            "--cpus",
            "4",
            "--memory",
            "8g",
            "--entrypoint",
            "/bin/bash",
            "--mount",
            f"type=bind,src={upstream_repo},dst=/home/lean/project",
            "--mount",
            f"type=bind,src={rh_repo},dst=/home/lean/rh",
            "--mount",
            f"type=volume,src={TOOLCHAIN_VOLUME},dst=/home/lean/.elan/toolchains",
            "--workdir",
            "/home/lean/project/lean",
            LEAN_IMAGE,
            "-lc",
            f"lake env /bin/bash -lc {shlex.quote(lean_command)}",
        ],
        check=True,
    )


def verify_oai_proofs() -> None:
    argument_parser = argparse.ArgumentParser()
    argument_parser.add_argument("through", choices=tuple(UPSTREAM_TARGETS))
    arguments = argument_parser.parse_args()

    rh_repo = Path(__file__).resolve().parent
    upstream_repo = rh_repo.parent / "rh-upstream"
    if not (upstream_repo / "lean" / "lakefile.lean").is_file():
        raise FileNotFoundError(f"Missing upstream Lean checkout: {upstream_repo}")

    build_upstream_oai_target(upstream_repo, UPSTREAM_TARGETS[arguments.through])

    for module in UPSTREAM_TARGETS:
        compile_local_oai_module(upstream_repo, rh_repo, module)
        if module == arguments.through:
            break


if __name__ == "__main__":
    verify_oai_proofs()
