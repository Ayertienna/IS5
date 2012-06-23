COQBIN=
#/home/charguer/coq/trunk/bin/
COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

LIB=\
	LibTactics.v \
	LibAxioms.v \
	LibEqual.v \
	LibLogic.v \
	LibEpsilon.v \
	LibFunc.v \
	LibChoice.v \
	LibOperation.v \
	LibBool.v \
	LibReflect.v \
	LibUnit.v \
	LibProd.v \
	LibSum.v \
	LibOption.v \
	LibStruct.v \
	LibRelation.v \
	LibOrder.v \
	LibWf.v \
	LibNat.v \
	LibInt.v \
	LibStruct.v \
	LibList.v \
	LibListSorted.v \
	LibListZ.v \
	LibBag.v \
	LibSet.v \
	LibMultiset.v \
	LibMap.v \
	LibArray.v \
	LibGraph.v \
	LibPer.v \
	LibCore.v 

#	LibBigop.v \
#  LibQuotient.v \
#	LibOperator.v \
#	LibGroup.v \
#	LibFset.v \
#	LibEnv.v \
#	LibRelationb.v \
#	LibRing.v \
#	LibMonoid.v \
#	LibAtom.v \
#	LibData.v \

EXTRA=\
	LibFix.v \
	LibStream.v 

DEMO=\
	LibTacticsDemos.v \
	LibFixDemos.v 

#	LibCoreDemos.v \

TACTICS=\
	LibTactics.v \
	LibTacticsDemos.v 

ALL= $(LIB) $(EXTRA) $(DEMO)

.SUFFIXES: .v .vo
.PHONY: all lib demo depend

all: $(ALL:.v=.vo) 
lib: $(LIB:.v=.vo) 
extra: $(EXTRA:.v=.vo)
demo: $(DEMO:.v=.vo) 
tactics: $(TACTICS:.v=.vo)

.v.vo : .depend
	$(COQC) $<

depend: .depend

.depend : $(ALL)
	$(COQDEP) -I . $(ALL) > .depend


ifeq ($(findstring $(MAKECMDGOALS),depend clean),)
include .depend
endif

clean:
	@rm -f *.vo || echo ok
	@rm -f .depend || echo ok


