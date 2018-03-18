.PHONY: all
all: master.agda split.hs
	ghc split.hs
	./split < master.agda

.PHONY: clean
clean:
	rm -f *.o *.hi *.agdai
