import argparse
import time
from typing import List, Union

from ortools.sat.python.cp_model import CpModel, CpSolver, CpSolverSolutionCallback, _SumArray


class NQueensSolver(object):
    def __init__(self,
                 num_queens: int,
                 printer: bool):
        # Initialize model and solver
        self._cp_model = CpModel()
        self._cp_solver = CpSolver()

        self._num_queens = num_queens
        self._indices = range(num_queens)

        # Initialize the board
        self._board = self._initialize_board()

        # Add constraint for exactly 1 queen in each row, col
        self._constrain_rows_and_columns()
        # Add constraint for at most 1 queen in each diagonal
        self.constrain_diagonal(self.backwards_diagonal_func())
        self.constrain_diagonal(self.forwards_diagonal_func())
        # Add constraint for exactly N queens on board
        self._constrain_num_queens()

        # initialize solution printer
        self._solution_printer = NQueensPrinter(self._board, printer)

    def solve(self):
        self._cp_solver.SearchForAllSolutions(self._cp_model, self._solution_printer)
        print('Total Solutions: %i' % self._solution_printer.count())

    def _initialize_board(self) -> List[List[CpModel.NewIntVar]]:
        # Add NxN new spots to the model
        return [
            [self._add_new_spot(i, j) for i in self._indices]
            for j in self._indices
        ]

    def _add_new_spot(self, i: int, j: int) -> CpModel.NewIntVar:
        # Adds a new boolean variable ot the solver, with the name 'posx,y'
        return self._cp_model.NewBoolVar(f"pos{i},{j}")

    def _constrain_rows_and_columns(self):
        for i in self._indices:
            # AddBoolXOr ensures exactly one queen in each row & each col
            self._cp_model.AddBoolXOr(self._board[i])
            self._cp_model.AddBoolXOr(list(zip(*self._board))[i])

    def _constrain_num_queens(self):
        queens = None
        for i in self._indices:
            for j in self._indices:
                queens = self.add(queens, self._board[i][j])
        self._cp_model.Add(queens == self._num_queens)

    def constrain_diagonal(self, function):
        b = [None] * (self._num_queens - 1)
        board = [function(b, i, r) for i, r in enumerate(self._board)]
        [self._cp_model.Add(self.sum_queens(diag) <= 1) for diag in list(zip(*board))]

    def sum_queens(self, diag):
        fd_sum = None
        for item in diag:
            if item is not None:
                fd_sum = self.add(fd_sum, item)
        return fd_sum

    @staticmethod
    def add(l: Union[_SumArray, None], item) -> _SumArray:
        return l + item if l is not None else item

    @staticmethod
    def backwards_diagonal_func():
        return lambda b, i, r: (b[i:] + r + b[:i])

    @staticmethod
    def forwards_diagonal_func():
        return lambda b, i, r: (b[:i] + r + b[i:])


class NQueensPrinter(CpSolverSolutionCallback):
    def __init__(self,
                 board: List[List[CpModel.NewIntVar]],
                 printer: bool):
        CpSolverSolutionCallback.__init__(self)

        # Flatten board into list of variables
        self.__variables = [q for row in board for q in row]
        self.__solution_count = 0
        self.__total_queens = len(board)
        self.__should_print = printer

    # Callback method for each solution
    def OnSolutionCallback(self):
        self.__solution_count += 1
        if self.__should_print:
            for idx, v in enumerate(self.__variables):
                has_newline = idx % self.__total_queens == 0
                self._draw_space(self.Value(v), has_newline)
            self._print_new_line(self.__total_queens)
            print()

    def count(self):
        return self.__solution_count

    def _draw_space(self, is_queen: bool, has_newline: bool):
        if has_newline:
            self._print_new_line(self.__total_queens)
            print('|', end='')
        print(' Q |' if is_queen else ' - |', end='')

    @staticmethod
    def _print_new_line(length: int):
        print('\n+' + ('---+' * length))


def main(should_print: bool, timer_on: bool, infinite: bool):
    num_queens = 0
    while True:
        num_queens = (num_queens + 1) if infinite else int(input("How many queens? "))
        start_time = time.perf_counter() if timer_on else None

        # Instantiate the solver and solve
        NQueensSolver(num_queens, should_print).solve()

        if timer_on:
            print(f"Time to solve {num_queens} queens: {time.perf_counter() - start_time:0.4f} seconds")

        if infinite:
            # This sleep keeps the while True from getting ahead of itself
            time.sleep(1)


if __name__ == "__main__":
    # Parse arguments for the script
    parser = argparse.ArgumentParser()
    parser.add_argument('--print', dest='print', action='store_true')
    parser.add_argument('--time', dest='time', action='store_true')
    parser.add_argument('--infinite', dest='infinite', action='store_true')
    args = parser.parse_args()

    main(args.print, args.time, args.infinite)
