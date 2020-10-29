from ortools.sat.python import cp_model
from typing import List


def solve_n(board_size: int):
    board = cp_model.CpModel()
    # initializing board position variables
    queens_on_board = [
        [board.NewBoolVar(f"pos{i},{j}") for j in range(board_size)]
        for i in range(board_size)
    ]  # type: List[List[cp_model.IntVar]]

    for i in range(board_size):
        # Set the XOr constraint on row[i] for each row in queens_on_board
        row_vars = queens_on_board[i]
        board.AddBoolXOr(row_vars)
        # Set the XOr constraint on col[i] for each col in queens_on_board
        col_vars = [queens_on_board[j][i] for j in range(board_size)]
        board.AddBoolXOr(col_vars)

        for j in range(board_size):
            pass
            # Set the diagonal constraint for each cell

    # Every true value represents a queen on the board of size N
    # create constraints 
    # 1. No more than N variables can be true
    # 2. No two "true" variables can have the same i value
    # 3. No two "true" variables can have the same j value
    # 4. No two "true" variables can have (i,x - j,x) == (i,y - j,y)

    # For each row, the sum of the booleans is exactly 1


if __name__ == "__main__":
    solve_n(int(input("Number of queens!")))
