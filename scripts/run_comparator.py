# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Check the final theorems with Comparator inside the pinned upstream project.

The upstream `lean/` tree is exported from the pinned commit into
`build/comparator/lean`. The local Lean modules, the challenge, and the
solution are added to that copy, and Comparator builds both modules in a
Landlock sandbox, compares the statements, and replays the solution through
the Lean kernel.
"""

import argparse
import logging
import os
import shlex
import shutil
import subprocess
from pathlib import Path

from verify_oai import (
    LEAN_IMAGE,
    TOOLCHAIN_VOLUME,
    UPSTREAM_REVISION,
    verify_upstream_checkout,
)


LEAN_TOOLCHAIN = "leanprover/lean4:v4.34.1"
GO_IMAGE = "golang:1.24"
COMPARATOR_TOOLS = {
    "comparator": ("https://github.com/leanprover/comparator.git", "v4.34.0"),
    "lean4export": ("https://github.com/leanprover/lean4export.git", "v4.34.0"),
    "landrun": ("https://github.com/Zouuup/landrun.git", "811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"),
}
CHALLENGE_NAME = "PerturbedQuasiRiemann"
SOLUTION_MODULE = "PerturbedQuasiRiemannSolution"
LOCAL_LIBRARY_STANZA_MARKER = "-- Local perturbed zero-free modules"


def run_logged_command(command: list[str], **kwargs) -> None:
    """Run a command, streaming its output, and raise on failure."""
    logging.info("Running %s", shlex.join(command[:6]) + (" ..." if len(command) > 6 else ""))
    subprocess.run(command, check=True, **kwargs)


def clone_pinned_tool(tools_dir: Path, tool_name: str) -> Path:
    """Clone one Comparator tool at its pinned revision."""
    repository_url, revision = COMPARATOR_TOOLS[tool_name]
    tool_dir = tools_dir / tool_name
    if not tool_dir.is_dir():
        run_logged_command(["git", "clone", "--quiet", repository_url, str(tool_dir)])
    run_logged_command(["git", "-C", str(tool_dir), "checkout", "--quiet", revision])
    return tool_dir


def build_comparator_tools(tools_dir: Path) -> Path:
    """Build landrun, lean4export, and comparator against the pinned Lean toolchain."""
    tools_bin_dir = tools_dir / "bin"
    tools_bin_dir.mkdir(parents=True, exist_ok=True)

    landrun_dir = clone_pinned_tool(tools_dir, "landrun")
    if not (tools_bin_dir / "landrun").is_file():
        run_logged_command([
            "docker", "run", "--rm", "--user", f"{os.getuid()}:{os.getgid()}",
            "-e", "CGO_ENABLED=0", "-e", "GOCACHE=/tmp/gocache", "-e", "GOPATH=/tmp/gopath",
            "--mount", f"type=bind,src={landrun_dir},dst=/src",
            "--mount", f"type=bind,src={tools_bin_dir},dst=/out",
            "--workdir", "/src", GO_IMAGE,
            "go", "build", "-buildvcs=false", "-o", "/out/landrun", "./cmd/landrun",
        ])

    # Exported proof objects record the Lean version, so both Lean tools must be
    # compiled with the same patch release as the proofs rather than their tagged 4.34.0.
    for tool_name in ["lean4export", "comparator"]:
        tool_dir = clone_pinned_tool(tools_dir, tool_name)
        (tool_dir / "lean-toolchain").write_text(LEAN_TOOLCHAIN + "\n")
        if (tools_bin_dir / tool_name).is_file():
            continue
        run_in_lean_container(
            f"lake build && cp .lake/build/bin/{tool_name} /tools/bin/{tool_name}",
            workdir=f"/tools/{tool_name}",
            mounts=[f"type=bind,src={tools_dir},dst=/tools"],
        )

    logging.info("Comparator tools are ready in %s", tools_bin_dir)
    return tools_bin_dir


def run_in_lean_container(shell_command: str, workdir: str, mounts: list[str]) -> None:
    """Run a shell command in the Lean image with the shared toolchain volume."""
    command = [
        "docker", "run", "--rm", "--cpuset-cpus", "0-7", "--cpus", "8", "--memory", "14g",
        "--entrypoint", "/bin/bash",
        "--mount", f"type=volume,src={TOOLCHAIN_VOLUME},dst=/home/lean/.elan/toolchains",
    ]
    for mount in mounts:
        command += ["--mount", mount]
    command += ["--workdir", workdir, LEAN_IMAGE, "-lc", shell_command]
    run_logged_command(command)


def export_pinned_upstream_project(upstream_repo: Path, project_dir: Path) -> None:
    """Replace the project's sources with the upstream `lean/` tree at the pinned commit."""
    project_dir.mkdir(parents=True, exist_ok=True)
    for entry in project_dir.iterdir():
        if entry.name == ".lake":
            continue
        if entry.is_dir():
            shutil.rmtree(entry)
        else:
            entry.unlink()

    archive = subprocess.run(
        ["git", "-C", str(upstream_repo), "archive", UPSTREAM_REVISION, "lean"],
        check=True, stdout=subprocess.PIPE,
    )
    subprocess.run(
        ["tar", "-x", "--strip-components=1", "-C", str(project_dir)],
        input=archive.stdout, check=True,
    )
    logging.info("Exported upstream lean/ at %s into %s", UPSTREAM_REVISION, project_dir)


def seed_upstream_lake_directories(upstream_repo: Path, project_dir: Path) -> None:
    """Copy upstream build objects and packages once so that unchanged modules are not rebuilt.

    Lake writes missing hash files next to package build objects, so the packages
    are copied rather than mounted from the upstream checkout.
    """
    for lake_subdirectory in ["build", "packages"]:
        project_lake_dir = project_dir / ".lake" / lake_subdirectory
        if project_lake_dir.is_dir() and len(list(project_lake_dir.iterdir())) > 0:
            logging.info("Reusing %s", project_lake_dir)
            continue

        upstream_lake_dir = upstream_repo / "lean/.lake" / lake_subdirectory
        if not upstream_lake_dir.is_dir():
            raise FileNotFoundError(f"Missing upstream Lake directory: {upstream_lake_dir}")
        logging.info("Copying %s", upstream_lake_dir)
        project_lake_dir.parent.mkdir(parents=True, exist_ok=True)
        run_logged_command(["cp", "-a", "--reflink=auto", str(upstream_lake_dir), str(project_lake_dir)])


def add_local_modules_to_project(lean_dir: Path, project_dir: Path) -> None:
    """Add the local modules, challenge, and solution to the exported project."""
    local_module_paths = sorted(lean_dir.glob("OAI*.lean"))
    for module_path in local_module_paths:
        shutil.copy2(module_path, project_dir / module_path.name)

    comparator_dir = lean_dir / "comparator"
    shutil.copy2(comparator_dir / f"{SOLUTION_MODULE}.lean", project_dir / f"{SOLUTION_MODULE}.lean")
    shutil.copy2(
        comparator_dir / f"{CHALLENGE_NAME}.lean",
        project_dir / "ComparatorChallenges" / f"{CHALLENGE_NAME}.lean",
    )
    shutil.copy2(
        comparator_dir / f"{CHALLENGE_NAME}.json",
        project_dir / "ComparatorChallenges" / f"{CHALLENGE_NAME}.json",
    )

    local_module_names = [module_path.stem for module_path in local_module_paths] + [SOLUTION_MODULE]
    module_roots = ", ".join(f"`{module_name}" for module_name in local_module_names)
    library_stanza = (
        f"\n{LOCAL_LIBRARY_STANZA_MARKER}\n"
        f"lean_lib PerturbedZeroFree where\n"
        f"  roots := #[{module_roots}]\n"
    )
    with (project_dir / "lakefile.lean").open("a") as lakefile:
        lakefile.write(library_stanza)
    logging.info("Added %s local modules and the Comparator challenge", len(local_module_names))


def run_comparator(project_dir: Path, tools_bin_dir: Path) -> None:
    """Build the challenge and solution, then run Comparator in the sandbox."""
    config_path = f"ComparatorChallenges/{CHALLENGE_NAME}.json"
    shell_command = (
        "export PATH=/tools/bin:$PATH && "
        f"lake build ComparatorChallenges.{CHALLENGE_NAME} {SOLUTION_MODULE} && "
        f"lake env comparator {shlex.quote(config_path)}"
    )
    run_in_lean_container(
        shell_command,
        workdir="/home/lean/project",
        mounts=[
            f"type=bind,src={project_dir},dst=/home/lean/project",
            f"type=bind,src={tools_bin_dir},dst=/tools/bin,readonly",
        ],
    )
    logging.info("Comparator accepted %s", config_path)


def main() -> None:
    argument_parser = argparse.ArgumentParser(description=__doc__)
    argument_parser.parse_args()

    rh_repo = Path(__file__).resolve().parents[1]
    lean_dir = rh_repo / "lean"
    upstream_repo = rh_repo.parent / "rh-upstream"
    comparator_build_dir = rh_repo / "build/comparator"
    project_dir = comparator_build_dir / "lean"

    verify_upstream_checkout(upstream_repo, UPSTREAM_REVISION)
    tools_bin_dir = build_comparator_tools(comparator_build_dir / "tools")
    export_pinned_upstream_project(upstream_repo, project_dir)
    seed_upstream_lake_directories(upstream_repo, project_dir)
    add_local_modules_to_project(lean_dir, project_dir)
    run_comparator(project_dir, tools_bin_dir)


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    main()
