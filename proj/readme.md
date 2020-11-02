# CS2800 Project

### How to run
1. Make sure you have python 3.8.1 and pipenv installed
    - If on mac, run `brew install pipenv`
    - I use pyenv to manage my python versions, see the below section to use that if desired.
        - Do this before running pipenv
2. In the root directory of the project, run `pipenv install`
    - This will install the necessary dependencies
    - **Note:** If you want to be able to run tests and check types via mypy, you must run `pipenv install --dev`
3. Once that is complete, run pipenv shell to activate the generated virtualenv
4. To run the program
    - usage: `main.py [-h] [--print] [--time] [--infinite]`
    - where `--print` is a boolean flag that enables printing of board solutions
    - where `--time` is a boolean flag that enables solution generation timing
    - where `--infinite` is a boolean flag that will infinitely increase the board size until interrupted with `c-c` (emacs notation for ctrl+c)
5. To exit the program
    - Hit `c-c`
6. Running tests **must install with --dev flag**
    - In the root directory with the pipenv shell activated run:
        - `pytest tests.py`
    - if all goes well, all the tests will pass!
7. Running mypy **must install with --dev flag**
    - To check the program for type-correctness, we will need to run mypy
    - in the root directory run `mypy main.py` and address any errors that occur
        - In my experience most bugs in dynamically typed languages are data-shape induced bugs

### Using pyenv to install python 3.8.1
1. Install pyenv
    - if on mac, run: `brew install pyenv`
2. Then run `pyenv install 3.8.1`
3. add `eval "$(pyenv init -)"` to your .bashrc or .zshrc and restart your terminal
    - Run `which python` to see if it worked
    - The output should be something like this: `~/.pyenv/versions/3.8.1/bin/python`
