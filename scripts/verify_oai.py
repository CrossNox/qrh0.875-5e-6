# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Check Lean proofs and their axioms against the pinned upstream source."""

import argparse
import logging
import shlex
import subprocess
import sys
from pathlib import Path


LEAN_IMAGE = "ghcr.io/leanprover-community/mathlib4/lean:latest"
TOOLCHAIN_VOLUME = "rh-lean-toolchains"
UPSTREAM_REVISION = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"


def verify_upstream_checkout(upstream_repo: Path, expected_revision: str) -> None:
    """Require the pinned upstream commit and a clean working tree."""
    revision = subprocess.run(
        ["git", "-C", str(upstream_repo), "rev-parse", "HEAD"],
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout.strip()
    if revision != expected_revision:
        raise ValueError(
            f"Upstream revision mismatch in {upstream_repo}: "
            f"expected {expected_revision}, found {revision}"
        )

    changes = subprocess.run(
        ["git", "-C", str(upstream_repo), "status", "--porcelain", "--untracked-files=normal"],
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout.strip()
    if len(changes) != 0:
        raise ValueError(f"Upstream checkout has uncommitted changes:\n{changes}")

    logging.info("Verified upstream revision %s with a clean working tree", revision)


def read_module_imports(module_path: Path) -> list[str]:
    """Read the imports declared by a local Lean module."""
    imports = []
    for line in module_path.read_text().splitlines():
        if line.startswith("import "):
            imports.extend(line.removeprefix("import ").split("--", 1)[0].split())
    return imports


def order_local_dependencies(lean_dir: Path, target: str) -> list[str]:
    """Order the target's local imports before their consumers."""
    ordered_modules = []
    completed_modules = set()
    active_modules = set()

    def visit_module(module: str) -> None:
        if module in completed_modules:
            return
        if module in active_modules:
            raise ValueError(f"Cyclic local Lean import: {module}")

        active_modules.add(module)
        for dependency in read_module_imports(lean_dir / f"{module}.lean"):
            if (lean_dir / f"{dependency}.lean").is_file():
                visit_module(dependency)
        active_modules.remove(module)
        completed_modules.add(module)
        ordered_modules.append(module)

    visit_module(target)
    return ordered_modules


def find_upstream_targets(lean_dir: Path, modules: list[str]) -> list[str]:
    """Collect upstream imports required by the local proof chain."""
    return sorted({
        dependency
        for module in modules
        for dependency in read_module_imports(lean_dir / f"{module}.lean")
        if not (lean_dir / f"{dependency}.lean").is_file()
    })


def build_upstream_oai_targets(upstream_repo: Path, targets: list[str]) -> None:
    """Build the imported upstream proof objects."""
    logging.info("Building %s upstream Lean targets", len(targets))
    command = "lake --quiet build " + " ".join(
        shlex.quote(f"+{target}:olean") for target in targets
    )
    compilation = subprocess.run(
        [
            "docker", "run", "--rm", "--cpuset-cpus", "0-7", "--cpus", "8",
            "--memory", "14g", "--entrypoint", "/bin/bash",
            "--mount", f"type=bind,src={upstream_repo},dst=/home/lean/project",
            "--mount",
            f"type=volume,src={TOOLCHAIN_VOLUME},dst=/home/lean/.elan/toolchains",
            "--workdir", "/home/lean/project/lean", LEAN_IMAGE, "-lc", command,
        ],
        capture_output=True,
        text=True,
    )
    print(compilation.stdout, end="", flush=True)
    print(compilation.stderr, end="", file=sys.stderr, flush=True)
    compilation.check_returncode()
    logging.info("Upstream Lean targets are ready")


def has_current_proof_object(lean_dir: Path, upstream_repo: Path, module: str) -> bool:
    """Check source and direct dependency timestamps before resuming a build."""
    proof_dir = lean_dir / ".lake/build/lib/lean"
    proof_path = proof_dir / f"{module}.olean"
    if not proof_path.is_file():
        return False

    proof_time = proof_path.stat().st_mtime_ns
    source_path = lean_dir / f"{module}.lean"
    if proof_time < source_path.stat().st_mtime_ns:
        return False

    for dependency in read_module_imports(source_path):
        if (lean_dir / f"{dependency}.lean").is_file():
            dependency_path = proof_dir / f"{dependency}.olean"
        elif dependency.startswith("OAI."):
            dependency_path = (
                upstream_repo / "lean/.lake/build/lib/lean"
                / f"{dependency.replace('.', '/')}.olean"
            )
        else:
            continue

        if not dependency_path.is_file():
            return False
        if proof_time < dependency_path.stat().st_mtime_ns:
            return False

    return True


def compile_local_oai_module(upstream_repo: Path, lean_dir: Path, module: str) -> None:
    """Compile one module and retain its proof object for subsequent imports."""
    logging.info("Compiling %s.lean against upstream OAI", module)
    lean_command = (
        "LEAN_PATH=/home/lean/rh/.lake/build/lib/lean:${LEAN_PATH:?Lake did not set LEAN_PATH} "
        "lean -R /home/lean/rh -o "
        f"{shlex.quote(f'/home/lean/rh/.lake/build/lib/lean/{module}.olean')} "
        f"{shlex.quote(f'/home/lean/rh/{module}.lean')}"
    )
    compilation = subprocess.run(
        [
            "docker", "run", "--rm", "--network", "none",
            "--cpuset-cpus", "0-3", "--cpus", "4", "--memory", "8g",
            "--entrypoint", "/bin/bash",
            "--mount",
            f"type=bind,src={upstream_repo},dst=/home/lean/project,readonly",
            "--mount", f"type=bind,src={lean_dir},dst=/home/lean/rh",
            "--mount",
            f"type=volume,src={TOOLCHAIN_VOLUME},dst=/home/lean/.elan/toolchains,readonly",
            "--workdir", "/home/lean/project/lean", LEAN_IMAGE, "-lc",
            f"lake env /bin/bash -c {shlex.quote(lean_command)}",
        ],
        capture_output=True,
        text=True,
    )
    print(compilation.stdout, end="", flush=True)
    print(compilation.stderr, end="", file=sys.stderr, flush=True)
    compilation.check_returncode()


def verify_oai_proofs() -> None:
    """Build the requested theorem chain in dependency order."""
    rh_repo = Path(__file__).resolve().parents[1]
    lean_dir = rh_repo / "lean"
    modules = sorted(path.stem for path in lean_dir.glob("*.lean")
                     if path.stem != "lakefile")
    argument_parser = argparse.ArgumentParser(description=__doc__)
    argument_parser.add_argument("through", choices=modules)
    argument_parser.add_argument(
        "--only", action="store_true",
        help="Compile only the requested module, using existing local imports.",
    )
    argument_parser.add_argument(
        "--resume", action="store_true",
        help="Reuse proof objects newer than their sources and direct imports.",
    )
    arguments = argument_parser.parse_args()

    upstream_repo = rh_repo.parent / "rh-upstream"
    if not (upstream_repo / "lean/lakefile.lean").is_file():
        raise FileNotFoundError(f"Missing upstream Lean checkout: {upstream_repo}")
    verify_upstream_checkout(upstream_repo, UPSTREAM_REVISION)
    (lean_dir / ".lake/build/lib/lean").mkdir(parents=True, exist_ok=True)

    ordered_modules = order_local_dependencies(lean_dir, arguments.through)
    build_upstream_oai_targets(
        upstream_repo, find_upstream_targets(lean_dir, ordered_modules)
    )

    modules_to_compile = [arguments.through] if arguments.only else ordered_modules
    compiled_count = 0
    for module in modules_to_compile:
        is_audit = module == arguments.through and module.endswith("Audit")
        if arguments.resume and not is_audit and has_current_proof_object(
            lean_dir, upstream_repo, module
        ):
            continue
        compile_local_oai_module(upstream_repo, lean_dir, module)
        compiled_count += 1
    logging.info(
        "Verified %s: compiled %s local modules", arguments.through, compiled_count,
    )


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(message)s", stream=sys.stdout)
    verify_oai_proofs()
