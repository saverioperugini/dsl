#!/usr/bin/python3

import matplotlib.pyplot as plt

if __name__ == '__main__':
  data = []
  with open("numbers.txt", "r") as f:
    for line in f.readlines():
      if line != "\n":
        n1, n2 = line.split(";")
        data.append((int(n1), int(n2)))

  noPrevRed = []
  prevRed = []
  for p, n in data:
    if p == n:
      noPrevRed.append(n)
    else:
      prevRed.append(n)
    
  print(f"There were {len(noPrevRed)} dialogs that previously had no reduction")

  average = 0
  for v in noPrevRed + prevRed:
    average += v/len(data)
  print(f"The average is {average}")

  num_bins = max(max(noPrevRed), max(prevRed))
  xlabels = list(range(1, num_bins+1))
  noPrevRedCounts = [noPrevRed.count(x) for x in xlabels]
  prevRedCounts = [prevRed.count(x) for x in xlabels]
  #ratiolabels = [f"{xlab}:1" for xlab in xlabels]

  print(f"Previously-reduced counts (blue): {prevRedCounts}")
  print(f"Not previously-reduced counts: {noPrevRedCounts}")

  plt.xlabel("# terms in mined dialogue")
  plt.ylabel("quantity")
  plt.ylim(0, (prevRedCounts[0] // 50)*50 + 50)
  plt.grid(linestyle='--', axis='y', zorder=0)
  plt.bar(xlabels, prevRedCounts, zorder=3)
  plt.bar(xlabels, noPrevRedCounts, bottom=prevRedCounts, zorder=3)
  plt.show()

