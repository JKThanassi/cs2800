from typing import List
from ortools.sat.python.cp_model import CpModel, CpSolver, CpSolverSolutionCallback

class SolutionPrinter(CpSolverSolutionCallback):
    def __init__(self, variables, size):
        CpSolverSolutionCallback.__init__(self)
        self.__variables = variables
        self.__solution_count = 0
        self.__board_size = size

    def OnSolutionCallback(self):
        self.__solution_count += 1
        for idx, v in enumerate(self.__variables):
            if idx % self.__board_size == 0:
                print()
            print(self.Value(v), end = ' ')
        print()
    
    def SolutionCount(self):
        return self.__solution_count

def solve_n(board_size):
    board, queens_on_board = create_n(board_size)
    cp_solver = CpSolver()
    solution_printer = SolutionPrinter([q for row in queens_on_board for q in row], board_size)
    results = cp_solver.SearchForAllSolutions(board, solution_printer)
    print('Total Solutions: %i' % solution_printer.SolutionCount())



def create_n(board_size: int):
    board = CpModel()
    # initializing board position variables
    queens_on_board = [
        [board.NewBoolVar(f"pos{i},{j}") for j in range(board_size)]
        for i in range(board_size)
    ]  # type: List[List[CpModel.IntVar]]

    for i in range(board_size):
        # Set the XOr constraint on row[i] for each row in queens_on_board
        row_vars = queens_on_board[i]
        board.AddBoolXOr(row_vars)
        # Set the XOr constraint on col[i] for each col in queens_on_board
        col_vars = [queens_on_board[j][i] for j in range(board_size)]
        board.AddBoolXOr(col_vars)

    constrain_backward_diagonals(queens_on_board, board)
    constrain_forward_diagonals(queens_on_board, board)
    

    summed_board = None
    for i in range(board_size):
        for j in range(board_size):
            if summed_board:
                summed_board += queens_on_board[i][j]
            else:
                summed_board = queens_on_board[i][j]

    board.Add(summed_board == board_size)

    return board, queens_on_board


    # Every true value represents a queen on the board of size N
    # create constraints 
    # 1. No more or fewer than N variables can be true
    # 2. No two "true" variables can have the same i value
    # 3. No two "true" variables can have the same j value
    # 4. No two "true" variables can have (i,x - j,x) == (i,y - j,y)

    # For each row, the sum of the booleans is exactly 1

def get_rows(grid):
    return [[c for c in r] for r in grid]

def get_cols(grid):
    return zip(*grid)

def constrain_backward_diagonals(grid, board):
    b = [None] * (len(grid) - 1)
    grid = [b[i:] + r + b[:i] for i, r in enumerate(get_rows(grid))]
    diagonals = [[c for c in r if c is not None] for r in get_cols(grid)]
    constrain_diagonal(diagonals, board)

def constrain_forward_diagonals(grid, board):
    b = [None] * (len(grid) - 1)
    grid = [b[:i] + r + b[i:] for i, r in enumerate(get_rows(grid))]
    diagonals = [[c for c in r if c is not None] for r in get_cols(grid)]
    constrain_diagonal(diagonals, board)


def constrain_diagonal(diagonals, board):
    for diag in diagonals:
        fd_sum = None
        for item in diag:
            if fd_sum:
                fd_sum += item 
            else:
                fd_sum = item  
        board.Add(fd_sum <= 1)

if __name__ == "__main__":
    while True:
        print(solve_n(int(input("Queens? "))))

