# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Compile the local Lean dependency chain and report theorem axioms."""

import argparse
import shlex
import subprocess
from pathlib import Path


LEAN_IMAGE = "ghcr.io/leanprover-community/mathlib4/lean:latest"
TOOLCHAIN_VOLUME = "rh-lean-toolchains"


def read_module_imports(module_path: Path) -> list[str]:
    """Read the imports declared by a local Lean module."""
    imports = []
    for line in module_path.read_text().splitlines():
        if line.startswith("import "):
            imports.extend(line.removeprefix("import ").split("--", 1)[0].split())
    return imports


def order_local_dependencies(rh_repo: Path, target: str) -> list[str]:
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
        for dependency in read_module_imports(rh_repo / f"{module}.lean"):
            if (rh_repo / f"{dependency}.lean").is_file():
                visit_module(dependency)
        active_modules.remove(module)
        completed_modules.add(module)
        ordered_modules.append(module)

    visit_module(target)
    return ordered_modules


def find_upstream_targets(rh_repo: Path, modules: list[str]) -> list[str]:
    """Collect upstream imports required by the local proof chain."""
    return sorted({
        dependency
        for module in modules
        for dependency in read_module_imports(rh_repo / f"{module}.lean")
        if not (rh_repo / f"{dependency}.lean").is_file()
    })


def build_upstream_oai_targets(upstream_repo: Path, targets: list[str]) -> None:
    """Build the imported upstream proof objects."""
    print(f"Building {len(targets)} upstream Lean targets", flush=True)
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
    if compilation.returncode != 0:
        print(compilation.stdout, end="")
        print(compilation.stderr, end="")
        compilation.check_returncode()
    print("Upstream Lean targets are ready", flush=True)


def has_current_proof_object(rh_repo: Path, upstream_repo: Path, module: str) -> bool:
    """Check source and direct dependency timestamps before resuming a build."""
    proof_path = rh_repo / f"{module}.olean"
    if not proof_path.is_file():
        return False

    proof_time = proof_path.stat().st_mtime_ns
    source_path = rh_repo / f"{module}.lean"
    if proof_time < source_path.stat().st_mtime_ns:
        return False

    for dependency in read_module_imports(source_path):
        if (rh_repo / f"{dependency}.lean").is_file():
            dependency_path = rh_repo / f"{dependency}.olean"
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


def compile_local_oai_module(upstream_repo: Path, rh_repo: Path, module: str) -> None:
    """Compile one module and retain its proof object for subsequent imports."""
    print(f"Compiling {module}.lean against upstream OAI", flush=True)
    lean_command = (
        "LEAN_PATH=/home/lean/rh:${LEAN_PATH:?Lake did not set LEAN_PATH} "
        "lean -R /home/lean/rh -o "
        f"{shlex.quote(f'/home/lean/rh/{module}.olean')} "
        f"{shlex.quote(f'/home/lean/rh/{module}.lean')}"
    )
    compilation = subprocess.run(
        [
            "docker", "run", "--rm", "--network", "none",
            "--cpuset-cpus", "0-3", "--cpus", "4", "--memory", "8g",
            "--entrypoint", "/bin/bash",
            "--mount",
            f"type=bind,src={upstream_repo},dst=/home/lean/project,readonly",
            "--mount", f"type=bind,src={rh_repo},dst=/home/lean/rh",
            "--mount",
            f"type=volume,src={TOOLCHAIN_VOLUME},dst=/home/lean/.elan/toolchains,readonly",
            "--workdir", "/home/lean/project/lean", LEAN_IMAGE, "-lc",
            f"lake env /bin/bash -c {shlex.quote(lean_command)}",
        ],
        capture_output=True,
        text=True,
    )
    if compilation.returncode != 0:
        print(compilation.stdout, end="")
        print(compilation.stderr, end="")
        compilation.check_returncode()
    if len(compilation.stdout.strip()) != 0:
        print(compilation.stdout, end="")


def verify_oai_proofs() -> None:
    """Build the requested theorem chain in dependency order."""
    rh_repo = Path(__file__).resolve().parent
    modules = sorted(path.stem for path in rh_repo.glob("*.lean")
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

    ordered_modules = order_local_dependencies(rh_repo, arguments.through)
    build_upstream_oai_targets(
        upstream_repo, find_upstream_targets(rh_repo, ordered_modules)
    )

    modules_to_compile = [arguments.through] if arguments.only else ordered_modules
    compiled_count = 0
    for module in modules_to_compile:
        is_audit = module == arguments.through and module.endswith("Audit")
        if arguments.resume and not is_audit and has_current_proof_object(
            rh_repo, upstream_repo, module
        ):
            continue
        compile_local_oai_module(upstream_repo, rh_repo, module)
        compiled_count += 1
    print(
        f"Verified {arguments.through}: compiled {compiled_count} local modules",
        flush=True,
    )


if __name__ == "__main__":
    verify_oai_proofs()
