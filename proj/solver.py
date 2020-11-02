from typing import List, Callable, Union, Any

from ortools.sat.python.cp_model import CpModel  # type: ignore
from ortools.sat.python.cp_model import CpSolver, IntVar, _SumArray

from printer import NQueensPrinter


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
        """
        This function runs the SAT solver on the generated constraint model and prints the number of solutions
        """
        self._cp_solver.SearchForAllSolutions(self._cp_model, self._solution_printer)
        print('Total Solutions: %i' % self._solution_printer.count())

    def _initialize_board(self) -> List[List[IntVar]]:
        """
        This function initalized a NxN board of IntVars to be constrained
        This can be thought of as the board where a 0 represents an empty space
        and a 1 represents a queen.
        Returns: A 2d list of size NxN containing IntVars

        """
        # Add NxN new spots to the model
        return [
            [self._add_new_spot(i, j) for i in self._indices]
            for j in self._indices
        ]

    def _add_new_spot(self, i: int, j: int) -> IntVar:
        """
        This function Generates the IntVar to be added to the board
        Args:
            i: the row index of the IntVar
            j: the col index of the IntVar

        Returns: A newly generated IntVar constrained to the values 0..1

        """
        # Adds a new boolean variable ot the solver, with the name 'posx,y'
        return self._cp_model.NewBoolVar(f"pos{i},{j}")

    def _constrain_rows_and_columns(self):
        """
        This function  generates the row and column constraints for the board.
        We ensure that there is 1 and only 1 queen in a given row and column
        Returns: None

        """
        for i in self._indices:
            # AddBoolXOr ensures exactly one queen in each row & each col
            self._cp_model.AddBoolXOr(self._board[i])
            # lets break this down part by part:
            # *a is destructuring the list into separate arguments to zip
            # zip takes each element at the same index and assembles them into their own list
            # so zip([1,2,3], [3,2,1]) = [(1,3), (2,2) (1,3)]
            # In our case, this results in getting the columns of our board!
            self._cp_model.AddBoolXOr(list(zip(*self._board))[i])

    def _constrain_num_queens(self):
        """
        This function adds the constraint that we must have N queens on the board.
        No more, no less.

        Returns: None

        """
        queens = None
        for i in self._indices:
            for j in self._indices:
                queens = self.add(queens, self._board[i][j])
        self._cp_model.Add(queens == self._num_queens)

    def constrain_diagonal(self, function: Callable[[List[None], int, List[IntVar]], List[List[IntVar]]]):
        """
        This function ensures that there are either 0 or 1 queens in a diagonal.
        Args:
            function: A function which returns a list of lists of IntVars. Each sublist represents the IntVars on a diagonal.

        Returns: None

        """
        b = [None] * (self._num_queens - 1)
        board = [function(b, i, r) for i, r in enumerate(self._board)]
        [self._cp_model.Add(self.sum_queens(diag) <= 1) for diag in list(zip(*board))]

    def sum_queens(self, diag: List[IntVar]) -> _SumArray:
        """
        This function generates a sum of the IntVars on a diagonal.
        Args:
            diag: A list of IntVars to create the sum constraint on

        Returns: a SumArray to constrain on a particular diagonal

        """
        fd_sum = None
        for item in diag:
            if item is not None:
                fd_sum = self.add(fd_sum, item)
        return fd_sum

    @staticmethod
    def add(l: Union[_SumArray, None], item: IntVar) -> Union[_SumArray, IntVar]:
        """
        This function either adds an item (IntVar) into a SumArray
        The union type allows us to handle the case of the sumarray being null on the first iteration
        Args:
            l: A union type representing either a SumArray or None
            item: The constraint to add to the SumArray

        Returns: Either an IntVar or a SumArray

        """
        return l + item if l is not None else item

    @staticmethod
    def backwards_diagonal_func() -> Callable[[List[Any], int, List[Any]], List[List[Any]]]:
        """
        This function returns a lambda fn that will get the backwards diagonals from a list
        Returns: The aformentioned lambda fn (go functions as values!!)

        """
        return lambda b, i, r: (b[i:] + r + b[:i])

    @staticmethod
    def forwards_diagonal_func() -> Callable[[List[Any], int, List[Any]], List[List[Any]]]:
        """
        This function returns a lambda fn that will get the forwards diagonals from a list
        Returns: The aforementioned Lambda fn

        """
        return lambda b, i, r: (b[:i] + r + b[i:])