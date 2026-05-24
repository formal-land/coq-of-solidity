"""
Compile the Rocq files in the RocqOfSolidityTests directory in parallel.

We cannot use a standard Makefile as `rocqdep` is too slow on this directory (several minutes).
"""
import os
from pathlib import Path
import subprocess
from concurrent.futures import ProcessPoolExecutor, as_completed
import multiprocessing as mp
from multiprocessing import cpu_count
import argparse

# Files that we avoid to compile due to errors
black_list_file = 'scripts/tests_blacklist.txt'
black_list = []
if os.path.exists(black_list_file):
    with open(black_list_file, 'r') as f:
        black_list = f.read().splitlines()

dependency_files = [
    Path('RocqOfSolidity/RocqOfSolidity.vo'),
    Path('RocqOfSolidity/simulations/RocqOfSolidity.vo'),
]
dependency_mtime = max(
    (path.stat().st_mtime for path in dependency_files if path.exists()),
    default=0,
)


def compile_rocq_file(rocq_file: Path, force: bool):
    """Compile a single Rocq file usings coqc if it's outdated."""
    vo_file = rocq_file.with_suffix('.vo')
    rocq_file_mtime = rocq_file.stat().st_mtime

    # Check if the .vo file exists and is up-to-date
    if not force and vo_file.exists():
        vo_file_mtime = vo_file.stat().st_mtime
        if vo_file_mtime >= max(rocq_file_mtime, dependency_mtime):
            return None

    # Check if the file is in the black list
    if str(rocq_file) in black_list:
        return None

    try:
        command = [
            'coqc',
            '-R', 'RocqOfSolidity', 'RocqOfSolidity',
            '-R', 'RocqOfSolidityTests', 'RocqOfSolidityTests',
            '-impredicative-set',
            rocq_file
        ]
        print(*command)
        subprocess.run(
            command,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )
        return None
    except subprocess.CalledProcessError as e:
        print(f"Error compiling {rocq_file}:\n{e.stderr.decode()}")
        return rocq_file


def compile_directory(root_path: Path, force: bool):
    """Compile all .v files in a directory."""
    failures = []
    rocq_files = [f for f in os.listdir(root_path) if f.endswith('.v')]
    has_generated_test = 'GeneratedTest.v' in rocq_files
    other_rocq_files = [
        root_path / f
        for f in rocq_files
        if f != 'GeneratedTest.v'
    ]
    # Compile other .v files first
    for rocq_file in sorted(other_rocq_files):
        failure = compile_rocq_file(rocq_file, force)
        if failure is not None:
            failures.append(failure)
    # Then compile GeneratedTest.v
    if has_generated_test:
        generated_test_path = root_path / 'GeneratedTest.v'
        failure = compile_rocq_file(generated_test_path, force)
        if failure is not None:
            failures.append(failure)
    return failures


def main():
    parser = argparse.ArgumentParser(description='Compile Rocq files in parallel.')
    parser.add_argument(
        '-j', '--jobs', type=int, default=cpu_count(),
        help='Number of parallel jobs (default: number of CPUs)'
    )
    parser.add_argument(
        '--force', action='store_true',
        help='Recompile files even when their .vo file looks up-to-date.'
    )
    args = parser.parse_args()

    test_dir = 'RocqOfSolidityTests/'
    # Collect all directories containing .v files
    dirs_to_compile = []
    for root, _dirs, files in os.walk(test_dir):
        if any(f.endswith('.v') for f in files):
            dirs_to_compile.append(Path(root))

    with ProcessPoolExecutor(
        max_workers=args.jobs,
        mp_context=mp.get_context("fork"),
    ) as executor:
        futures = {
            executor.submit(compile_directory, dir_path, args.force): dir_path
            for dir_path in dirs_to_compile
        }
        failures = []
        for future in as_completed(futures):
            dir_path = futures[future]
            try:
                failures += future.result()
            except Exception as exc:
                print(f'Exception occurred while compiling directory {dir_path}: {exc}')
                failures.append(dir_path)

    if failures:
        print("Compilation failed for:")
        for failure in sorted(failures):
            print(failure)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
