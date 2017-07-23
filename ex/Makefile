
FSTAR_HOME=/home/hritcu/Projects/fstar/pub

include $(FSTAR_HOME)/ulib/ml/Makefile.include

all:
	fstar.exe --verify_all Incr.fst Ex04c.fst RefinedStackClient.fst RefinedStack.fst FactorialST.fst

init-freeze:
	fstar.exe --include ../code/03 --verify_all InitFreeze.fst
