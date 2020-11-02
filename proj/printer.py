from typing import List

from ortools.sat.python.cp_model import CpSolverSolutionCallback  # type: ignore
from ortools.sat.python.cp_model import IntVar


class NQueensPrinter(CpSolverSolutionCallback):
    def __init__(self,
                 board: List[List[IntVar]],
                 printer: bool):
        CpSolverSolutionCallback.__init__(self)

        # Flatten board into list of variables
        self.__variables = [q for row in board for q in row]
        self.__solution_count = 0
        self.__total_queens = len(board)
        self.__should_print = printer

    # Callback method for each solution
    def OnSolutionCallback(self):
        """
        This function is a callback for the SAT solver whenever a solution is found.
        When called it increments the solution count and prints if the program is started with the --print flag
        Returns: None

        """
        self.__solution_count += 1
        if self.__should_print:
            for idx, v in enumerate(self.__variables):
                has_newline = idx % self.__total_queens == 0
                self._draw_space(self.Value(v), has_newline)
            self._print_new_line(self.__total_queens)
            print()

    def count(self) -> int:
        """
        Getter for the solution count
        Returns: The number of solutions for this board

        """
        return self.__solution_count

    def _draw_space(self, is_queen: bool, has_newline: bool):
        """
        This function pretty prints out the board as a NxN grid of boxes containing a Q or " "
        Args:
            is_queen: Bool flag representing if this space is a queen
            has_newline: if this square is at the end of a line and should contain a newline char

        Returns: None

        """
        if has_newline:
            self._print_new_line(self.__total_queens)
            print('|', end='')
        print(' Q |' if is_queen else ' - |', end='')

    @staticmethod
    def _print_new_line(length: int):
        """
        Handles printing newlines for the pretty printer
        Args:
            length: the length of the line to be drawn

        Returns:

        """
        print('\n+' + ('---+' * length))