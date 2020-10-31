import argparse
import time
from typing import List, Union

from ortools.sat.python.cp_model import CpModel, CpSolver, CpSolverSolutionCallback, IntVar, _SumArray


class NQueensSolver(object):
    def __init__(self, num_queens: int, printer: bool):
        self._cp_model = CpModel()
        self._cp_solver = CpSolver()
        self._num_queens = num_queens
        self._indices = range(num_queens)
        self._board = [
            [self._add_new_spot(i, j) for i in self._indices]
            for j in self._indices
        ]  # type:List[List[CpModel.NewIntVar]]

        self._constrain_rows_and_columns()
        self._constrain_diagonals()
        self._constrain_num_queens()
        self._solution_printer = NQueensPrinter(self._board, printer)

    def solve(self):
        self._cp_solver.SearchForAllSolutions(self._cp_model, self._solution_printer)
        print('Total Solutions: %i' % self._solution_printer.count())

    def _add_new_spot(self, i: int, j: int) -> CpModel.NewIntVar:
        return self._cp_model.NewBoolVar(f"pos{i},{j}")

    def _constrain_rows_and_columns(self):
        for i in self._indices:
            # AddBoolXOr ensures exactly one queen in each row & each col
            self._cp_model.AddBoolXOr(self._board[i])
            self._cp_model.AddBoolXOr(list(zip(*self._board))[i])

    def _constrain_diagonals(self):
        # (List[None], int, int) -> List[Optional[NewIntVar]]
        back_diag = lambda b, i, r: (b[i:] + r + b[:i])
        self.constrain_diagonal(back_diag)

        front_diag = lambda b, i, r: (b[:i] + r + b[i:])
        self.constrain_diagonal(front_diag)

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
        return lambda b, i, r: ()


class NQueensPrinter(CpSolverSolutionCallback):
    def __init__(self, board, printer: bool):
        CpSolverSolutionCallback.__init__(self)
        self.__variables = [q for row in board for q in row]
        self.__solution_count = 0
        self.__total_queens = len(board)
        self.__should_print = printer

    def OnSolutionCallback(self):
        self.__solution_count += 1
        if self.__should_print:
            for idx, v in enumerate(self.__variables):
                has_newline = idx % self.__total_queens == 0
                self._draw_space(self.Value(v), has_newline)
            self._print_new_line(self.__total_queens)
            print()

    def _draw_space(self, is_queen: bool, has_newline: bool):
        if has_newline:
            self._print_new_line(self.__total_queens)
            print('|', end='')
        print(' Q |' if is_queen else ' - |', end='')

    @staticmethod
    def _print_new_line(length: int):
        print('\n+' + ('---+' * length))

    def count(self):
        return self.__solution_count


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('--print', dest='print', action='store_true')
    parser.add_argument('--time', dest='time', action='store_true')
    parser.add_argument('--infinite', dest='infinite', action='store_true')

    should_print = parser.parse_args().print
    timer_on = parser.parse_args().time
    infinite = parser.parse_args().infinite

    n = 0
    while True:
        if infinite:
            n += 1
        else:
            n = int(input("How many queens? "))
        if timer_on:
            start_time = time.perf_counter() if timer_on else None

        NQueensSolver(n, should_print).solve()

        if timer_on:
            print(f"Time to find {n}: {time.perf_counter() - start_time:0.4f} seconds")

        if infinite:
            time.sleep(1)