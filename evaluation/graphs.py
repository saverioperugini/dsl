#!/usr/bin/python3

import matplotlib.pyplot as plt

if __name__ == '__main__':
  f = open("numbers.txt", "r")
  lines = f.readlines()
  f.close()
  if lines[-1] == '\n':
    lines = lines[:-1]
  nums = [int(v) for v in lines]

  num_bins = max(nums)
  xlabels = list(range(1, num_bins+1))
  counts = [nums.count(x) for x in xlabels]
  ratiolabels = [f"{xlab}:1" for xlab in xlabels]
  plt.xlabel("# terms in mined dialogue")
  plt.ylabel("quantity")
  plt.bar(xlabels, counts)
  plt.show()

