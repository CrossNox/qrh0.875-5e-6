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
    "OAIHighEulerRegion": "OAI.NumberTheory.DirichletL.Detector.EulerRegion",
    "OAIHighPrincipalProduct": "OAI.NumberTheory.DirichletL.Detector.PrincipalProduct",
    "OAIHighRamifiedBound": "OAI.NumberTheory.DirichletL.Detector.HighRowsRamified",
    "OAIHighHolomorphic": "OAI.NumberTheory.DirichletL.Detector.HighRowsHolomorphic",
    "OAIHighGlobalRegion": "OAI.NumberTheory.DirichletL.Detector.GlobalRegion",
    "OAIHighGlobalCorrection": "OAI.NumberTheory.DirichletL.Detector.GlobalCorrection",
    "OAIHighSlotEstimate": "OAI.NumberTheory.DirichletL.PrincipalSlotEstimate",
    "OAIHighFiniteProductBounds": "OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds",
    "OAIHighFiniteProductX": "OAI.NumberTheory.DirichletL.Detector.FiniteProductX",
    "OAIHighFixedSource": "OAI.NumberTheory.DirichletL.ParametersFixedSource",
    "OAIHighFiniteProductWZ": "OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds",
    "OAIHighSourceWZ": "OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds",
    "OAIHighComplexSlotBounds": "OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds",
    "OAIHighSourceContours": "OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds",
    "OAIHighArithmeticLines": "OAI.NumberTheory.DirichletL.Detector.PrincipalContours",
    "OAIHighOrderedContours": "OAI.NumberTheory.DirichletL.Detector.PrincipalContours",
    "OAIHighResidueBounds": "OAI.NumberTheory.DirichletL.Detector.PrincipalContours",
    "OAIHighOuterContours": "OAI.NumberTheory.DirichletL.Detector.PrincipalContours",
    "OAIHighUniformTails": "OAI.NumberTheory.DirichletL.Detector.PrincipalContours",
    "OAIHighHighSlices": "OAI.NumberTheory.DirichletL.Detector.PrincipalContours",
    "OAIHighResidueMoments": "OAI.NumberTheory.DirichletL.Detector.PrincipalContours",
    "OAIHighXTransport": "OAI.NumberTheory.DirichletL.Detector.PrincipalTransport",
    "OAIHighZTransport": "OAI.NumberTheory.DirichletL.Detector.PrincipalTransport",
    "OAIHighTripleTransport": "OAI.NumberTheory.DirichletL.Detector.PrincipalTransport",
    "OAIHighInitialPlacement": "OAI.NumberTheory.DirichletL.Detector.PrincipalTransport",
    "OAIHighSelectedTerms": "OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedTerms",
    "OAIHighSelectedError": "OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedError",
    "OAIHighSelectedUnramified": "OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedUnramified",
    "OAIHighSelectedBound": "OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedBound",
    "OAIHighSelectedRamified": "OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedRamified",
    "OAIHighSelectedActual": "OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedActual",
    "OAIHighSelectedLocal": "OAI.NumberTheory.DirichletL.PrimeRows.SelectedBounds",
    "OAIHighSelectedSlotSums": "OAI.NumberTheory.DirichletL.PrimeRows.SlotSums",
    "OAIHighWGrowth": "OAI.NumberTheory.DirichletL.PrimeRows.WGrowth",
    "OAIHighNonprincipalShift": "OAI.NumberTheory.DirichletL.PrimeRows.NonprincipalShift",
    "OAIHighTupleSums": "OAI.NumberTheory.DirichletL.PrimeRows.TupleSums",
    "OAIHighTupleBound": "OAI.NumberTheory.DirichletL.PrimeRows.TupleBound",
    "OAIHighPhysicalTuple": "OAI.NumberTheory.DirichletL.PrimeRows.PhysicalBound",
    "OAIHighDyadBound": "OAI.NumberTheory.DirichletL.PrimeRows.DyadBound",
    "OAIHighDyadIntegral": "OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral",
    "OAIHighFixedIntegral": "OAI.NumberTheory.DirichletL.PrimeRows.FixedIntegral",
    "OAIHighWZTransport": "OAI.NumberTheory.DirichletL.PrimeRows.WZTransport",
    "OAIHighSourceTransport": "OAI.NumberTheory.DirichletL.PrimeRows.SourceTransport",
    "OAIHighPhysicalDyad": "OAI.NumberTheory.DirichletL.PrimeRows.PhysicalDyad",
    "OAIHighTailScales": "OAI.NumberTheory.DirichletL.PrimeRows.TailScales",
    "OAIHighSmallDyad": "OAI.NumberTheory.DirichletL.PrimeRows.SmallDyad",
    "OAIHighSmallTail": "OAI.NumberTheory.DirichletL.PrimeRows.SmallTail",
    "OAIHighLargeDyad": "OAI.NumberTheory.DirichletL.PrimeRows.LargeDyad",
    "OAIHighLargeTail": "OAI.NumberTheory.DirichletL.PrimeRows.LargeTail",
    "OAIHighLargeSaving": "OAI.NumberTheory.DirichletL.PrimeRows.LargeSaving",
    "OAIHighCentralCrude": "OAI.NumberTheory.DirichletL.PrimeRows.CentralErrorSaving",
    "OAIHighCentralFiniteError": "OAI.NumberTheory.DirichletL.PrimeRows.CentralFiniteError",
    "OAIHighCentralExponent": "OAI.NumberTheory.DirichletL.Detector.CentralMixedMargins",
    "OAIHighCentralSlotExponent": "OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent",
    "OAIHighCentralClassArithmetic": "OAI.NumberTheory.DirichletL.Detector.CentralClassArithmetic",
    "OAIHighCentralBatch": "OAI.NumberTheory.DirichletL.Detector.SourceBatch",
    "OAIHighCentralAmplitudeBatch": "OAI.NumberTheory.DirichletL.Detector.SourceAmplitudeClasses",
    "OAIHighCentralClassMoments": "OAI.NumberTheory.DirichletL.PrimeRows.NonfloorClass",
    "OAIHighCentralArithmetic": "OAI.NumberTheory.DirichletL.PrimeRows.NonfloorArithmetic",
    "OAIHighCentralIntegral": "OAI.NumberTheory.DirichletL.PrimeRows.NonfloorIntegral",
    "OAIHighCentralNormalizer": "OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer",
    "OAIHighCentralNormalized": "OAI.NumberTheory.DirichletL.PrimeRows.NonfloorNormalized",
    "OAIHighCentralCollected": "OAI.NumberTheory.DirichletL.PrimeRows.NonfloorCollected",
    "OAIHighSlotLengths": "OAI.NumberTheory.DirichletL.ParametersSlotLengths",
    "OAIHighCentralBudget": "OAI.NumberTheory.DirichletL.ParametersCentralBudget",
    "OAIHighData": "OAI.NumberTheory.DirichletL.ParametersHighData",
    "OAIHighAudit": "OAI.NumberTheory.DirichletL.Detector.CentralMixedMargins",
    "OAILowReflected": "OAI.NumberTheory.DirichletL.Detector.LowReflectedLength",
    "OAILowExponent": "OAI.NumberTheory.DirichletL.Reflection.LowExponent",
    "OAILowBranchSum": "OAI.NumberTheory.DirichletL.Reflection.LowBranchSum",
    "OAILowSector": "OAI.NumberTheory.DirichletL.Reflection.LowSector",
    "OAILowRetained": "OAI.NumberTheory.DirichletL.Reflection.LowRetained",
    "OAILowRetainedBudget": "OAI.NumberTheory.DirichletL.Reflection.LowRetainedBudget",
    "OAILowFull": "OAI.NumberTheory.DirichletL.Reflection.LowFull",
    "OAILowFullBudget": "OAI.NumberTheory.DirichletL.Reflection.LowFullBudget",
    "OAILowGlobalBudget": "OAI.NumberTheory.DirichletL.Reflection.LowGlobalBudget",
    "OAILowMemberBudget": "OAI.NumberTheory.DirichletL.Reflection.LowMemberBudget",
    "OAILowMemberGeometry": "OAI.NumberTheory.DirichletL.Reflection.LowMemberGeometry",
    "OAILowCaps": "OAI.NumberTheory.DirichletL.Reflection.LowCaps",
    "OAILowFixedMember": "OAI.NumberTheory.DirichletL.Reflection.LowFixedMember",
    "OAILowDyads": "OAI.NumberTheory.DirichletL.Reflection.LowDyads",
    "OAILowChoiceEnergy": "OAI.NumberTheory.DirichletL.Reflection.LowChoiceEnergy",
    "OAILowInactiveEnergy": "OAI.NumberTheory.DirichletL.Reflection.LowInactiveEnergy",
    "OAILowFrozenEnergy": "OAI.NumberTheory.DirichletL.Reflection.LowFrozenEnergy",
    "OAILowCompletedFiber": "OAI.NumberTheory.DirichletL.Reflection.LowCompletedFiber",
    "OAILowCompletedRows": "OAI.NumberTheory.DirichletL.Reflection.LowCompletedRows",
    "OAILowOriginalEnergy": "OAI.NumberTheory.DirichletL.Reflection.LowOriginalEnergy",
    "OAILowSelectedBound": "OAI.NumberTheory.DirichletL.Detector.LowSelectedBound",
    "OAILowNominalEnergy": "OAI.NumberTheory.DirichletL.Detector.LowNominalEnergy",
    "OAILowInverseNormalize": "OAI.NumberTheory.DirichletL.Detector.LowPhysicalInverseBound",
    "OAILowPhysicalInverseBound": "OAI.NumberTheory.DirichletL.Detector.LowPhysicalInverseBound",
    "OAILowSourceScales": "OAI.NumberTheory.DirichletL.Detector.LowSourceScales",
    "OAILowSlotScales": "OAI.NumberTheory.DirichletL.Detector.LowSlotScales",
    "OAILowUnselectedMass": "OAI.NumberTheory.DirichletL.Detector.LowUnselectedMass",
    "OAILowCentralTuple": "OAI.NumberTheory.DirichletL.Detector.LowCentralTuple",
    "OAILowGaussianDyad": "OAI.NumberTheory.DirichletL.Detector.LowGaussianDyad",
    "OAILowGaussianCentral": "OAI.NumberTheory.DirichletL.Detector.LowGaussianCentral",
    "OAILowRemoteMass": "OAI.NumberTheory.DirichletL.Detector.LowRemoteMass",
    "OAILowGaussianRemote": "OAI.NumberTheory.DirichletL.Detector.LowGaussianRemote",
    "OAILowGaussianSum": "OAI.NumberTheory.DirichletL.Detector.LowGaussianSum",
    "OAILowCommonBound": "OAI.NumberTheory.DirichletL.Detector.LowCommonBound",
    "OAILowWindowBound": "OAI.NumberTheory.DirichletL.Detector.LowWindowBound",
    "OAILowNormalizer": "OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer",
    "OAILowNormalized": "OAI.NumberTheory.DirichletL.Detector.LowNormalized",
    "OAILowAudit": "OAI.NumberTheory.DirichletL.Detector.LowNormalized",
}


def build_upstream_oai_target(upstream_repo: Path, target: str) -> None:
    print(f"Building upstream OAI target {target}", flush=True)

    compilation = subprocess.run(
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
        capture_output=True,
        text=True,
    )
    if compilation.returncode != 0:
        print(compilation.stdout, end="")
        print(compilation.stderr, end="")
        compilation.check_returncode()


def compile_local_oai_module(upstream_repo: Path, rh_repo: Path, module: str) -> None:
    print(f"Compiling {module}.lean against upstream OAI", flush=True)

    lean_command = (
        "LEAN_PATH=/home/lean/rh:${LEAN_PATH:?Lake did not set LEAN_PATH} "
        f"lean -R /home/lean/rh -o /home/lean/rh/{module}.olean "
        f"/home/lean/rh/{module}.lean"
    )

    compilation = subprocess.run(
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
        capture_output=True,
        text=True,
    )
    if compilation.returncode != 0:
        print(compilation.stdout, end="")
        print(compilation.stderr, end="")
        compilation.check_returncode()
    if compilation.stdout.strip():
        print(compilation.stdout, end="")


def verify_oai_proofs() -> None:
    argument_parser = argparse.ArgumentParser()
    argument_parser.add_argument("through", choices=tuple(UPSTREAM_TARGETS))
    argument_parser.add_argument("--only", action="store_true")
    arguments = argument_parser.parse_args()

    rh_repo = Path(__file__).resolve().parent
    upstream_repo = rh_repo.parent / "rh-upstream"
    if not (upstream_repo / "lean" / "lakefile.lean").is_file():
        raise FileNotFoundError(f"Missing upstream Lean checkout: {upstream_repo}")

    build_upstream_oai_target(upstream_repo, UPSTREAM_TARGETS[arguments.through])

    modules = [arguments.through] if arguments.only else UPSTREAM_TARGETS
    for module in modules:
        compile_local_oai_module(upstream_repo, rh_repo, module)
        if module == arguments.through:
            break


if __name__ == "__main__":
    verify_oai_proofs()
