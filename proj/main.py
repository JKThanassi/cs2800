import argparse
import time
import csv
from typing import List, Union, Any

from solver import NQueensSolver


def run_timing_experiments(runs: int = 10, start_size: int = 0, end_size: int = 8, out_file: str = "out.csv"):
    """
    This function will run the solver _runs_ times from board size start_size to end size and output a
    csv where each row is the board size, time to solve, and num solutions.
    Args:
        runs:
        start_size: The board size to start the experiments at (inclusive)
        end_size: The board size to stop the experiments at (exclusive)
        out_file: The filepath to write the csv out to. Defaults to out.csv

    Returns: None

    """
    data_headers = ["Board Size", "Time to solve", "Num Solutions"]
    run_data = gen_run_data(runs, start_size, end_size)
    write_to_csv(data_headers, run_data, out_file)


def write_to_csv(headers: List[str], run_data: List[List[Any]], path: str):
    """
    This function is responsible for writing the run data out to a csv. The first row will be the data labels
    The headers and run data rows must be the same length or an exception will be raised.
    Args:
        headers: The labels for the data
        run_data: A list of lists of run data
        path: The path to write the file

    Returns: None

    """
    for i in range(len(run_data)):
        if not len(headers) == len(run_data[0]):
            raise ValueError("Headers and rows must be of the same length")
    with open(path, 'w') as csvfile:
        queenwriter = csv.writer(csvfile, dialect='excel')
        queenwriter.writerow(headers)
        queenwriter.writerows(run_data)


def gen_run_data(runs: int, start_size: int, end_size: int) -> List[List[Union[int, float]]]:
    """
    This function runs the solver and records the data for each interval specified by the arguments of the function
    Args:
        runs: The number of runs to preform for each permutation of board size
        start_size: The start value for the range of board sizes to run (inclusive)
        end_size: The end value for the range of board sizes to run (exclusive)

    Returns: A list containing the run data for each solver iteration

    """
    run_data = list()  # type: List[List[Union[int, float]]]
    if runs < 1 or start_size >= end_size or start_size < 0:
        raise ValueError(
            "Runs must be greater than or equal to 1, start size must be less than end_size, and start size must be 0 or larger")
    for size in range(start_size, end_size):
        for run in range(runs):
            print(f"Run {run} of {runs} of size {size}")
            start_time = time.perf_counter()
            nq = NQueensSolver(size, False)
            nq.solve()
            end_time = time.perf_counter()
            run_data.append([size, end_time - start_time, nq._solution_printer.count()])
    return run_data

def run_interactive(should_print: bool, timer_on: bool, infinite: bool):
    """
    Startpoint for our program. Makes the solver into a REPL where a user enters a numbner and we output solutions.
    Args:
        should_print: Boolean flag determining whether or not to print each solution
        timer_on: Boolean flag determining whether or not to time each run
        infinite: Boolean flag determining whether to keep incrementing N of the board indefinitely

    Returns: None

    """
    num_queens = 0
    while True:
        num_queens = (num_queens + 1) if infinite else int(input("How many queens? "))
        start_time = time.perf_counter() if timer_on else None

        # Instantiate the solver and solve
        NQueensSolver(num_queens, should_print).solve()

        if start_time is not None: # Using this and not the flag so mypy can unwrap the optional
            print(f"Time to solve {num_queens} queens: {time.perf_counter() - start_time:0.4f} seconds")

        if infinite:
            # This sleep keeps the while True from getting ahead of itself
            time.sleep(1)


def setup_parser() -> argparse.ArgumentParser:
    """
    This function sets up the argument parser with two commands: interactive and experiment
    Each command has its subcommands that are defined in the help text below
    Returns: the set up ArgumentParser object

    """
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(
        help="Experiment will run the solver a specified number of times and output a csv and run creates an interactive environment")
    exp_parser = subparsers.add_parser('experiment', help='Flag to run the experiment')
    exp_parser.add_argument('--n-runs', dest='runs', type=int,
                            help="Flag that takes the number of runs to preform per board size.", required=True)
    exp_parser.add_argument('--start', dest='start_size', type=int,
                            help="Flag that takes the start of the board size range.", required=True)
    exp_parser.add_argument('--end', dest='end_size', type=int,
                            help="Flag that takes the end of the board size range. EXCLUSIVE", required=True)
    exp_parser.add_argument('--out', dest='out_file', type=str, help="Flag that sets the output file path.",
                            required=True)
    normal_run_group = subparsers.add_parser("interactive", help="flag that sets the mode to interactive")
    normal_run_group.add_argument('--print', dest='print', action='store_true')
    normal_run_group.add_argument('--time', dest='time', action='store_true')
    normal_run_group.add_argument('--infinite', dest='infinite', action='store_true')
    return parser


if __name__ == "__main__":
    # Parse arguments for the script
    parser = setup_parser()
    args = parser.parse_args()

    arg_map = vars(args)
    if arg_map.get('runs'):
        run_timing_experiments(**arg_map)
    else:
        run_interactive(args.print, args.time, args.infinite)
