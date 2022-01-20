defmodule DProc do
  def procAtomic(parent, jumpTo, resp) do
    if parent == nil or jumpTo == nil do
      receive do
        {p, j} -> procAtomic(p, j, resp)
      end
    else
      receive do
        {:con, input} ->
          cond do
            length(input) == 0 ->
              send(parent, :err)
            hd(input) == resp ->
              send(parent, :fin)
              send(jumpTo, {:con, tl input})
            true ->
              send(parent, :err)
          end
      end
      procAtomic(parent, jumpTo, resp)
    end
  end

  def procC(parent, children) do
    if parent == nil do
      receive do
        p -> procC(p, children)
      end
    else
      receive do
        {:con, input} ->
          if length(children) > 0 do
            send(hd(children), {:con, input})
          else
            send(parent, :fin)
            send(parent, {:con, input})
          end
          procC(parent, children)
        :fin ->
          procC(parent, tl children)
        :err ->
          send(parent, :err)
          procC(parent, children)
      end
    end
  end

  def procW(parent, children) do
    receive do
      p -> DProc.procWHelp(p, [], children, [])
    end
  end

  def procWHelp(parent, tested, untested, input) do
    receive do
      {:con, inp} ->
        if length(tested) + length(untested) > 0 do
          children = Enum.reverse(tested) ++ untested
          send(hd(children), {:con, inp})
          procWHelp(parent, [hd children], tl(children), inp)
        else
          send(parent, :fin)
          send(parent, {:con, inp})
          procWHelp(parent, tested, untested, input)
        end
      :fin ->
        procWHelp(parent, tl(tested), untested, input)
      :err ->
        if length(untested) == 0 do
          send(parent, :err)
          procWHelp(parent, [], Enum.reverse(tested), input)
        else
          send(hd(untested), {:con, input})
          procWHelp(parent, [hd(untested)|tested], tl(untested), input)
        end
    end
  end
end

# main program
# stage (W (C a^ b) (C x y))

a = spawn(DProc, :procAtomic, [nil, nil, "a"])
b = spawn(DProc, :procAtomic, [nil, nil, "b"])
x = spawn(DProc, :procAtomic, [nil, nil, "x"])
y = spawn(DProc, :procAtomic, [nil, nil, "y"])

c1 = spawn(DProc, :procC, [nil, [a, b]])
c2 = spawn(DProc, :procC, [nil, [x, y]])

w = spawn(DProc, :procW, [nil, [c1, c2]])

send(w, self)
send(c1, w)
send(c2, w)
send(a, {c1, w})
send(b, {c1, c1})
send(x, {c2, c2})
send(y, {c2, c2})

send(w, {:con, ["a", "x", "y", "b", "rest"]})
receive do
  result -> IO.puts result
end
receive do
  {:con, rest} -> IO.puts rest
end
