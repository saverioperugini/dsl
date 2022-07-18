#!/usr/bin/python3

import matplotlib.pyplot as plt

if __name__ == '__main__':
  data = []
  with open("numbers.txt", "r") as f:
    for line in f.readlines():
      if line != "\n":
        n1, n2 = line.split(";")
        data.append((int(n1), int(n2)))

  # --------------------------------------------------------------
  # Frequency vs. Compression Factor from Enumerated Specification
  # --------------------------------------------------------------
  
  enum_spec_lens = [pn[0] for pn in data]
  num_bins = max(enum_spec_lens)
  xlabels = list(range(1, num_bins+1))
  counts = [enum_spec_lens.count(x) for x in xlabels]
  average = sum(enum_spec_lens) / len(enum_spec_lens)

  print("The average episode length is ", average)

  plt.xlabel("Number of episodes")
  plt.ylabel("Frequency")
  plt.grid(linestyle='--', axis='y', zorder=0)
  plt.bar(xlabels, counts)
  plt.axvline(x=average, color='red', linestyle='--')
  plt.show()

  # --------------------------------------------------
  # Frequency vs. Compression Factor from Original DSL
  # --------------------------------------------------

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

  plt.xlabel("Number of terms")
  plt.ylabel("Frequency")
  plt.ylim(0, (prevRedCounts[0] // 50)*50 + 50)
  plt.grid(linestyle='--', axis='y', zorder=0)
  plt.bar(xlabels, prevRedCounts, zorder=3)
  plt.bar(xlabels, noPrevRedCounts, bottom=prevRedCounts, zorder=3)
  plt.axvline(x=average, color='red', linestyle='--')
  plt.show()

  # Original thing

  plt.xlabel("Number of terms")
  plt.ylabel("Frequency")
  plt.grid(linestyle='--', axis='y', zorder=0)
  plt.bar(range(0, 30+1), [0,1000]+ [0]*29)
  plt.show()
