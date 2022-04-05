#!/usr/bin/python3

import random
from sys import argv

def partition(lst, num_parts):
  "partition a list into `num_parts` non-empty lists"
  parts = [[] for _ in range(num_parts)]
  random.shuffle(lst)
  i = 0
  # put 1 element in each partition to start
  for p in parts:
    p.append(lst[i])
    i += 1
  # distribute the rest of the elements randomly
  while i < len(lst):
    random.choice(parts).append(lst[i])
    i += 1
  return parts

def gen_dialog_rec(questions, level, levels_of_Ws):
  if len(questions) == 0:
    print("Error, must be at least one question")
  elif len(questions) == 1:
    ret = f'(Atom "{questions[0]}")'
    if len(levels_of_Ws) > 0 and random.random() < 0.5:
      # add an arrow with 50% probability (still could be zero arrows though)
      num_arrows = level - 1 - random.choice(levels_of_Ws)
      while num_arrows > 0:
        ret = f'(Up {ret})'
        num_arrows -= 1
    return ret
  else:
    mnemonic = ["C", "W"][random.randrange(0, 2)]
    num_subdialogs = random.randrange(2, len(questions) + 1)
    parts = partition(questions, num_subdialogs)
    levels_of_Ws_new = levels_of_Ws.copy()
    if mnemonic == "W":
      levels_of_Ws_new.append(level)
    subdialogs = list(map(lambda part: gen_dialog_rec(part, level+1, levels_of_Ws_new), parts))
    return f'({mnemonic} [{", ".join(subdialogs)}])'

def gen_dialog(questions):
  if len(questions) <= 1:
    return gen_dialog_rec(questions, 0, [])
  else:
    num_subdialogs = random.randrange(2, len(questions) + 1)
    parts = partition(questions, num_subdialogs)
    subdialogs = list(map(lambda part: gen_dialog_rec(part, 1, [0]), parts))
    return f'W [{", ".join(subdialogs)}]'


if __name__ == "__main__":
  numDialogsToGenerate = int(argv[1])
  for i in range(numDialogsToGenerate):
    print("  "+gen_dialog(["a", "b", "c", "d"]), sep="", end="")
    if i < numDialogsToGenerate - 1:
      print(",", end="\n")
    else:
      print(end="\n")