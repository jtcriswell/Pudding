all: Multi.vo VG.vo SVAOS.vo ThreadProofs.vo ThreadTextProofs.vo InvProofs.vo

Multi.vo: SVAOS.vo ICProofs.vo ThreadTextProofs.vo

ICText.vo: Semantics.vo

InvProofs.vo: Semantics.vo ThreadProofs.vo

Thread.vo: IC.vo

ICProofs.vo ThreadProofs.vo: Semantics.vo ICText.vo

ThreadTextProofs.vo: Semantics.vo InvProofs.vo ICProofs.vo

VG.vo: Semantics.vo
  
SVAOS.vo: Semantics.vo ICProofs.vo

Semantics.vo: Config.vo

Config.vo: MMU.vo Stack.vo IC.vo Thread.vo

MMU.vo: Memory.vo TLB.vo
  
Memory.vo: Instructions.vo

Instructions.vo: TLB.vo

%.vo: %.v
	coqc $<

%.tex: %.v
	coqdoc --latex $<

clean:
	rm -f *.vo *.glob

