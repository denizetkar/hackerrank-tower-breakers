#!/bin/python3

import math
import os
import random
import re
import sys

#
# Complete the 'towerBreakers' function below.
#
# The function is expected to return an INTEGER.
# The function accepts following parameters:
#  1. INTEGER n
#  2. INTEGER m
#
from collections import defaultdict
from typing import DefaultDict, Dict, FrozenSet, Tuple

StateType = Tuple[DefaultDict[int, int], int]
HashableStateType = Tuple[FrozenSet[Tuple[int, int]], int]


def change_factorcnt_cnt(factorcnt_cnt: DefaultDict[int, int], factorcnt: int, delta_factor: int):
    factorcnt_cnt[factorcnt] -= 1
    factorcnt_cnt[factorcnt + delta_factor] += 1
    if factorcnt_cnt[factorcnt] <= 0:
        factorcnt_cnt.pop(factorcnt)


# def value_fn(state: StateType, val_memory: Dict[HashableStateType, int] = {}):
#     factorcnt_cnt, player_id = state
#     frozen_state = (frozenset(factorcnt_cnt.items()), player_id)
#     if frozen_state in val_memory:
#         return val_memory[frozen_state]

#     other_player_id = 1 - player_id
#     # If all prime factor counts are 0 (heights == 1), then the game is over.
#     if len(factorcnt_cnt) == 1 and 0 in factorcnt_cnt:
#         val_memory[frozen_state] = other_player_id
#         return other_player_id

#     # Calculate the value of the current state over all possible actions.
#     state_val = -float("inf") if player_id == 1 else float("inf")
#     for factorcnt in tuple(factorcnt_cnt.keys()):
#         for factor_reduction in range(1, factorcnt + 1):
#             change_factorcnt_cnt(factorcnt_cnt, factorcnt, -factor_reduction)
#             next_state_val = value_fn((factorcnt_cnt, other_player_id), val_memory)
#             state_val = max(state_val, next_state_val) if player_id == 1 else min(state_val, next_state_val)
#             change_factorcnt_cnt(factorcnt_cnt, factorcnt - factor_reduction, factor_reduction)

#     val_memory[frozen_state] = state_val
#     return state_val


class ExecPtr:
    BEFORE_RECURSION = 0
    AFTER_RECURSION = 1


def value_fn(state: StateType):
    val_memory: Dict[HashableStateType, int] = {}
    factorcnt_cnt, player_id = state
    frozen_state = (frozenset(factorcnt_cnt.items()), player_id)
    local_vars = (state, frozen_state, None, None, None, None)
    exec_ptr = ExecPtr.BEFORE_RECURSION
    execution_stack = [(local_vars, exec_ptr)]

    while len(execution_stack) > 0:
        local_vars, exec_ptr = execution_stack[-1]
        state, frozen_state, state_val, factorcnts, next_i, next_factor_reduction = local_vars
        factorcnt_cnt, player_id = state
        other_player_id = 1 - player_id

        if exec_ptr == ExecPtr.BEFORE_RECURSION:
            if frozen_state in val_memory:
                execution_stack.pop(-1)
                continue

            # If all prime factor counts are 0 (heights == 1), then the game is over.
            if len(factorcnt_cnt) == 1 and 0 in factorcnt_cnt:
                val_memory[frozen_state] = other_player_id
                execution_stack.pop(-1)
                continue

        # Calculate the value of the current state over all possible actions.
        if state_val is None:
            state_val = -float("inf") if player_id == 1 else float("inf")
        if factorcnts is None:
            factorcnts = tuple(factorcnt_cnt.keys())
        if next_i is None:
            next_i = 0
        if next_factor_reduction is None:
            next_factor_reduction = 1
        recurse = False
        for i in range(next_i, len(factorcnts)):
            factorcnt = factorcnts[i]
            for factor_reduction in range(next_factor_reduction, factorcnt + 1):
                if exec_ptr == ExecPtr.BEFORE_RECURSION:
                    change_factorcnt_cnt(factorcnt_cnt, factorcnt, -factor_reduction)
                    # next_state_val = value_fn((factorcnt_cnt, other_player_id), val_memory)
                    execution_stack[-1] = (
                        (state, frozen_state, state_val, factorcnts, i, factor_reduction),
                        ExecPtr.AFTER_RECURSION,
                    )
                    next_state = (factorcnt_cnt, other_player_id)
                    next_frozen_state = (frozenset(factorcnt_cnt.items()), other_player_id)
                    execution_stack.append(((next_state, next_frozen_state, None, None, None, None), ExecPtr.BEFORE_RECURSION))
                    recurse = True
                    break
                next_state_val = val_memory[(frozenset(factorcnt_cnt.items()), other_player_id)]
                state_val = max(state_val, next_state_val) if player_id == 1 else min(state_val, next_state_val)
                change_factorcnt_cnt(factorcnt_cnt, factorcnt - factor_reduction, factor_reduction)
                exec_ptr = ExecPtr.BEFORE_RECURSION
            if recurse:
                break
            next_factor_reduction = 1
        if recurse:
            continue

        val_memory[frozen_state] = state_val
        execution_stack.pop(-1)
        # continue
    return val_memory[frozen_state]


# return a dict or a list of primes up to N
# create full prime sieve for N=10^6 in 1 sec
def prime_sieve(n, output={}):
    nroot = int(math.sqrt(n))
    sieve = list(range(n + 1))
    sieve[1] = 0

    for i in range(2, nroot + 1):
        if sieve[i] != 0:
            m = n // i - i
            sieve[i * i : n + 1 : i] = [0] * (m + 1)

    if isinstance(output, dict):
        pmap = {}
        for x in sieve:
            if x != 0:
                pmap[x] = True
        return pmap
    elif isinstance(output, list):
        return [x for x in sieve if x != 0]
    else:
        return None


# get a list of prime factors
# ex: get_prime_factors(140) -> ((2,2), (5,1), (7,1))
#     140 = 2^2 * 5^1 * 7^1
def get_prime_factors(n, primelist=None):
    if primelist is None:
        primelist = prime_sieve(n, output=[])

    fs = []
    for p in primelist:
        count = 0
        while n % p == 0:
            n //= p
            count += 1
        if count > 0:
            fs.append((p, count))

    return fs


def towerBreakers(n, m):
    fs = get_prime_factors(m)
    factorcnt = sum(f[1] for f in fs)
    factorcnt_cnt = defaultdict(int)
    factorcnt_cnt[factorcnt] = n
    player_id = 0  # Always the first player starts
    state_val = value_fn((factorcnt_cnt, player_id))
    return state_val + 1  # 1 if player 1 wins, 2 if player 2 wins.


if __name__ == "__main__":
    with open(os.environ["INPUT_PATH"], "r") as f, open(os.environ["OUTPUT_PATH"], "w") as fptr:
        t = int(f.readline().strip())

        for t_itr in range(t):
            first_multiple_input = f.readline().rstrip().split()

            n = int(first_multiple_input[0])

            m = int(first_multiple_input[1])

            result = towerBreakers(n, m)

            fptr.write(str(result) + "\n")
