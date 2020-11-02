import pytest
from solver import NQueensSolver


def test_solution_count_1(capsys):
    nq = NQueensSolver(1, False)
    nq.solve()
    captured = capsys.readouterr()
    assert captured.out == "Total Solutions: 1\n"


def test_solution_count_2(capsys):
    nq = NQueensSolver(2, False)
    nq.solve()
    captured = capsys.readouterr()
    assert captured.out == "Total Solutions: 0\n"


def test_solution_count_3(capsys):
    nq = NQueensSolver(3, False)
    nq.solve()
    captured = capsys.readouterr()
    assert captured.out == "Total Solutions: 0\n"

def test_solution_count_4(capsys):
    nq = NQueensSolver(4, False)
    nq.solve()
    captured = capsys.readouterr()
    assert captured.out == "Total Solutions: 2\n"

def test_solution_count_5(capsys):
    nq = NQueensSolver(5, False)
    nq.solve()
    captured = capsys.readouterr()
    assert captured.out == "Total Solutions: 10\n"


def test_solution_count_6(capsys):
    nq = NQueensSolver(6, False)
    nq.solve()
    captured = capsys.readouterr()
    assert captured.out == "Total Solutions: 4\n"

def test_solution_count_7(capsys):
    nq = NQueensSolver(7, False)
    nq.solve()
    captured = capsys.readouterr()
    assert captured.out == "Total Solutions: 40\n"

def test_solution_count_8(capsys):
    nq = NQueensSolver(8, False)
    nq.solve()
    captured = capsys.readouterr()
    assert captured.out == "Total Solutions: 92\n"

def test_solution_count_9(capsys):
    nq = NQueensSolver(9, False)
    nq.solve()
    captured = capsys.readouterr()
    assert captured.out == "Total Solutions: 352\n"

def test_solution_count_10(capsys):
    nq = NQueensSolver(10, False)
    nq.solve()
    captured = capsys.readouterr()
    assert captured.out == "Total Solutions: 724\n"
