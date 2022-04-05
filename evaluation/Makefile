numDialogsToGenerate = 1000

numbers.txt : TestDialogs.hs GenEpisodes.hs mine-expr.rkt
	runhaskell TestDialogs.hs | racket mine-expr.rkt > numbers.txt

TestDialogs.hs : random_dialogs.py
	echo "import GenEpisodes" > TestDialogs.hs
	echo "" >> TestDialogs.hs
	echo "main = GenEpisodes.mainLoop testDialogs" >> TestDialogs.hs
	echo "" >> TestDialogs.hs
	echo "testDialogs :: [Dialog]" >> TestDialogs.hs
	echo "testDialogs = [" >> TestDialogs.hs
	python3 random_dialogs.py $(numDialogsToGenerate) >> TestDialogs.hs
	echo "  ]" >> TestDialogs.hs

clean:
	rm numbers.txt
	rm TestDialogs.hs