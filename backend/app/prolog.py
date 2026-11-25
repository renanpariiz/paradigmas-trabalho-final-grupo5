"""conecta a api python aos predicados do ocaso em prolog"""

from pathlib import Path
from typing import Any

import janus_swi as janus

PROLOG_FILE = Path(__file__).parent.parent / "prolog" / "ocaso.pl"
janus.consult(str(PROLOG_FILE))


class NoSolution(Exception):
    """usada quando o puzzle não tem solução"""


def generate(difficulty: str) -> dict[str, Any]:
    """gera um puzzle na dificuldade escolhida"""
    result = janus.query_once(
        "ocaso:api_generate(Name, Puzzle)",
        {"Name": difficulty},
    )
    return result["Puzzle"]


def solve(puzzle: dict[str, Any]) -> list[list[int]]:
    """resolve o puzzle ou levanta `nosolution` se não houver solução"""
    result = janus.query_once(
        "ocaso:api_solve(Puzzle, Towers)",
        {"Puzzle": puzzle},
    )
    if not result["truth"]:
        raise NoSolution
    return result["Towers"]


def hint(puzzle: dict[str, Any], placed: list[list[int]]) -> dict[str, Any]:
    """pede uma dica para o puzzle com as casas já preenchidas"""
    result = janus.query_once(
        "ocaso:api_hint(Puzzle, Placed, Hint)",
        {
            "Puzzle": puzzle,
            "Placed": placed,
        },
    )
    return result["Hint"]
