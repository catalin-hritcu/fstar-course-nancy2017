
FSTAR_HOME=/home/hritcu/Projects/fstar/pub

include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: init-freeze
	fstar.exe --verify_all Incr.fst Ex04c.fst RefinedStackLengthClient.fst RefinedStackLength.fst FactorialST.fst

init-freeze:
	fstar.exe --include ../code/03 --verify_all InitFreeze.fst
