# src/SMT4ModPlant/cli.py
import argparse
import json
from pathlib import Path

from .AASxmlCapabilityParser import parse_capabilities_robust
from .GeneralRecipeParser import parse_general_recipe

SUPPORTED_RESOURCE_SUFFIXES = {".xml", ".aasx", ".json"}


def load_capabilities_from_directory(resource_dir: Path):
    capabilities = {}

    for path in sorted(resource_dir.iterdir()):
        if path.suffix.lower() not in SUPPORTED_RESOURCE_SUFFIXES:
            continue

        parsed = parse_capabilities_robust(path)
        if parsed:
            capabilities[path.stem] = parsed

    return capabilities


def build_parser():
    parser = argparse.ArgumentParser(
        prog="smt4modplant",
        description="Run SMT4ModPlant resource matching from the command line.",
    )
    parser.add_argument("recipe", type=Path, help="Path to the General Recipe XML file.")
    parser.add_argument("resources", type=Path, help="Directory containing AAS XML/AASX/JSON files.")
    parser.add_argument("--json-out", type=Path, help="Optional path for JSON solution output.")
    parser.add_argument("--first", action="store_true", help="Stop after the first valid solution.")
    return parser


def main(argv=None):
    args = build_parser().parse_args(argv)

    from .feasibility import run_feasibility

    recipe_data = parse_general_recipe(args.recipe)
    capabilities_data = load_capabilities_from_directory(args.resources)

    results, json_solutions, _debug = run_feasibility(
        recipe_data,
        capabilities_data,
        generate_json=args.json_out is not None,
        find_all_solutions=not args.first,
    )

    if args.json_out:
        args.json_out.write_text(
            json.dumps(json_solutions, indent=2),
            encoding="utf-8",
        )

    print(f"Found {len(json_solutions) if args.json_out else len(results)} result entries.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
