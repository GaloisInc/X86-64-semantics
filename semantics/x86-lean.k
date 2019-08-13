require "x86-abstract-semantics.k"

module X86-LEAN
  imports X86-ABSTRACT-SEMANTICS

  syntax MInt ::= leanEvaluateAddress(Mem, Map) [function]
  rule
    <k> AddrExpr:Mem => memOffset(leanEvaluateAddress(AddrExpr, RSMap)) ...</k>
    <regstate> RSMap </regstate>

  syntax R8 ::= convRegKeyToR8(String) [function]
  syntax R16 ::= convRegKeyToR16(String) [function]
  syntax R32 ::= convRegKeyToR32(String) [function]
  syntax Rh ::= convRegKeyToRh(String) [function]
  syntax R64 ::= convRegKeyToR64(String) [function]
  syntax Xmm ::= convRegKeyToXmm(String) [function]
  syntax Ymm ::= convRegKeyToYmm(String) [function]
  syntax Flag ::= convRegKeyToFlag(String) [function]
  syntax String ::= convFlagToRegKey(Flag) [function]
  rule convRegKeyToR32("RAX") => %eax
  rule convRegKeyToR32("RDX") => %edx
  rule convRegKeyToR32("RSI") => %esi
  rule convRegKeyToR32("RDI") => %edi
  rule convRegKeyToR32("RSP") => %esp
  rule convRegKeyToR32("RBP") => %ebp
  rule convRegKeyToR64("RAX") => %rax
  rule convRegKeyToR64("RDX") => %rdx
  rule convRegKeyToR64("RSI") => %rsi
  rule convRegKeyToR64("RDI") => %rdi
  rule convRegKeyToR64("RSP") => %rsp
  rule convRegKeyToR64("RBP") => %rbp
  rule convRegKeyToYmm("YMM0") => %ymm0
  rule convRegKeyToYmm("YMM1") => %ymm1
  rule convRegKeyToYmm("YMM2") => %ymm2
  rule convRegKeyToYmm("YMM3") => %ymm3
  rule convRegKeyToYmm("YMM4") => %ymm4
  rule convRegKeyToYmm("YMM5") => %ymm5
  rule convRegKeyToYmm("YMM6") => %ymm6
  rule convRegKeyToYmm("YMM7") => %ymm7
  rule convRegKeyToYmm("YMM8") => %ymm8
  rule convRegKeyToYmm("YMM9") => %ymm9
  rule convRegKeyToYmm("YMM10") => %ymm10
  rule convRegKeyToYmm("YMM11") => %ymm11
  rule convRegKeyToYmm("YMM12") => %ymm12
  rule convRegKeyToYmm("YMM13") => %ymm13
  rule convRegKeyToYmm("YMM14") => %ymm14
  rule convRegKeyToYmm("YMM15") => %ymm15
  rule convRegKeyToFlag("CF") => %cf
  rule convRegKeyToFlag("DF") => %df
  rule convRegKeyToFlag("PF") => %pf
  rule convRegKeyToFlag("AF") => %af
  rule convRegKeyToFlag("ZF") => %zf
  rule convRegKeyToFlag("SF") => %sf
  rule convRegKeyToFlag("OF") => %of
  rule convFlagToRegKey(%cf) => "CF"
  rule convFlagToRegKey(%df) => "DF"
  rule convFlagToRegKey(%pf) => "PF"
  rule convFlagToRegKey(%af) => "AF"
  rule convFlagToRegKey(%zf) => "ZF"
  rule convFlagToRegKey(%sf) => "SF"
  rule convFlagToRegKey(%of) => "OF"
  rule convRegKeyToR8(convToRegKeysHelper(convSubRegsToRegs(R:R8))) => R [lemma]
  rule convRegKeyToR16(convToRegKeysHelper(convSubRegsToRegs(R:R16))) => R [lemma]
  rule convRegKeyToR32(convToRegKeysHelper(convSubRegsToRegs(R:R32))) => R [lemma]
  rule convRegKeyToRh(convToRegKeysHelper(convSubRegsToRegs(R:Rh))) => R [lemma]
  rule convRegKeyToR64(convToRegKeysHelper(convSubRegsToRegs(R:R64))) => R [lemma]
  rule convRegKeyToXmm(convToRegKeysHelper(convSubRegsToRegs(X:Xmm))) => X [lemma]
  rule convRegKeyToYmm(convToRegKeysHelper(convSubRegsToRegs(Y:Ymm))) => Y [lemma]
  syntax Bool ::= isR8RegKey(String) [function]
  syntax Bool ::= isR16RegKey(String) [function]
  syntax Bool ::= isR32RegKey(String) [function]
  syntax Bool ::= isRhRegKey(String) [function]
  syntax Bool ::= isR64RegKey(String) [function]
  syntax Bool ::= isGPRegKey(String) [function]
  syntax Bool ::= isXmmRegKey(String) [function]
  syntax Bool ::= isYmmRegKey(String) [function]
  syntax Bool ::= isFlagRegKey(String) [function]
  rule isGPRegKey("RAX") => true
  rule isGPRegKey("RDX") => true
  rule isGPRegKey("RSI") => true
  rule isGPRegKey("RDI") => true
  rule isGPRegKey("RSP") => true
  rule isGPRegKey("RBP") => true
  //rule isR8RegKey(RK:String) => true
  //  requires isGPRegKey(RK)
  //rule isR16RegKey(RK:String) => true
  //  requires isGPRegKey(RK)
  rule isR32RegKey(RK:String) => true
    requires isGPRegKey(RK)
  //rule isRhRegKey(RK:String) => true
  //  requires isGPRegKey(RK)
  rule isR64RegKey(RK:String) => true
    requires isGPRegKey(RK)
  rule isYmmRegKey("YMM0") => true
  rule isYmmRegKey("YMM1") => true
  rule isYmmRegKey("YMM2") => true
  rule isYmmRegKey("YMM3") => true
  rule isYmmRegKey("YMM4") => true
  rule isYmmRegKey("YMM5") => true
  rule isYmmRegKey("YMM6") => true
  rule isYmmRegKey("YMM7") => true
  rule isYmmRegKey("YMM8") => true
  rule isYmmRegKey("YMM9") => true
  rule isYmmRegKey("YMM10") => true
  rule isYmmRegKey("YMM11") => true
  rule isYmmRegKey("YMM12") => true
  rule isYmmRegKey("YMM13") => true
  rule isYmmRegKey("YMM14") => true
  rule isYmmRegKey("YMM15") => true
  rule isFlagRegKey("CF") => true
  rule isFlagRegKey("DF") => true
  rule isFlagRegKey("PF") => true
  rule isFlagRegKey("AF") => true
  rule isFlagRegKey("ZF") => true
  rule isFlagRegKey("SF") => true
  rule isFlagRegKey("OF") => true
  rule isR8RegKey(convToRegKeysHelper(convSubRegsToRegs(R:R8))) => true [lemma]
  rule isR16RegKey(convToRegKeysHelper(convSubRegsToRegs(R:R16))) => true [lemma]
  rule isR32RegKey(convToRegKeysHelper(convSubRegsToRegs(R:R32))) => true [lemma]
  rule isRhRegKey(convToRegKeysHelper(convSubRegsToRegs(R:Rh))) => true [lemma]
  rule isR64RegKey(convToRegKeysHelper(convSubRegsToRegs(R:R64))) => true [lemma]
  rule isXmmRegKey(convToRegKeysHelper(convSubRegsToRegs(X:Xmm))) => true [lemma]
  rule isYmmRegKey(convToRegKeysHelper(convSubRegsToRegs(Y:Ymm))) => true [lemma]

  syntax Map ::= leanSetRegister(Register, MInt, Map) [function]
               | leanSetRegister(Register, Bool, Map) [function]
  rule
    <k> setRegisterValue(MI:MInt, R:Register) => . ...</k>
    <regstate> RSMap:Map => leanSetRegister(R, MI, RSMap) </regstate>

  rule updateMap(RSMap:Map, UpdatesMap:Map) => updateMapEntries(RSMap, mapEntries(UpdatesMap)) [lemma]
  rule RSMap:Map[RK:String <- MI:MInt] => leanSetRegister(convRegKeyToFlag(RK), MI, RSMap)
    requires isFlagRegKey(RK)
    [lemma]

  syntax MapEntry ::= mapEntry(KItem, KItem)
  syntax MapEntryList ::= List{MapEntry, ","}
                        | mapEntries(Map) [function]
  rule mapEntries(K:KItem |-> V:KItem M:Map) => mapEntry(K, V), mapEntries(M)
  rule mapEntries(.Map) => .MapEntryList

  syntax Map ::= updateMapEntries(Map, MapEntryList) [function]
  rule updateMapEntries(RSMap:Map, .MapEntryList) => RSMap [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, concatenateMInt(extractMInt(getParentValue(R:R8, RSMap), 0, 56), MI:MInt)), UpdateEntries:MapEntryList)
    => leanSetRegister(R, MI, updateMapEntries(RSMap, UpdateEntries))
    requires convToRegKeys(R) ==K RK
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, concatenateMInt(extractMInt(getParentValue(R:R16, RSMap), 0, 48), MI:MInt)), UpdateEntries:MapEntryList)
    => leanSetRegister(R, MI, updateMapEntries(RSMap, UpdateEntries))
    requires convToRegKeys(R) ==K RK
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, concatenateMInt(ZMI:MInt, MI:MInt)), UpdateEntries:MapEntryList)
    => leanSetRegister(convRegKeyToR32(RK), MI, updateMapEntries(RSMap, UpdateEntries))
    requires isR32RegKey(RK) andBool ZMI ==K mi(32, 0)
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, concatenateMInt(ZMI:MInt, MI:MInt)), UpdateEntries:MapEntryList)
    => leanSetRegister(convRegKeyToR32(RK), concatenateMInt(mi(bitwidthMInt(ZMI) -Int 32, 0), MI:MInt), updateMapEntries(RSMap, UpdateEntries))
    requires isR32RegKey(RK) andBool zeroMInt(ZMI) andBool bitwidthMInt(ZMI) >Int 32
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, concatenateMInt(concatenateMInt(extractMInt(getParentValue(R:Rh, RSMap), 0, 48), MI:MInt), extractMInt(getParentValue(R, RSMap), 56, 64))), UpdateEntries:MapEntryList)
    => leanSetRegister(R, MI, updateMapEntries(RSMap, UpdateEntries))
    requires convToRegKeys(R) ==K RK
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, concatenateMInt(extractMInt(getParentValue(X:Xmm, RSMap), 0, 128), MI:MInt)), UpdateEntries:MapEntryList)
    => leanSetRegister(X, MI, updateMapEntries(RSMap, UpdateEntries))
    requires convToRegKeys(X) ==K RK
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, concatenateMInt(extractMInt(getParentValue(X:Xmm, RSMap), 0, 224), MI:MInt)), UpdateEntries:MapEntryList)
    => leanSetRegister(X, concatenateMInt(extractMInt(leanGetRegister(X:Xmm, RSMap), 0, 96), MI:MInt), updateMapEntries(RSMap, UpdateEntries))
    requires convToRegKeys(X) ==K RK
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, concatenateMInt(extractMInt(getParentValue(X:Xmm, RSMap), 0, 192), MI:MInt)), UpdateEntries:MapEntryList)
    => leanSetRegister(X, concatenateMInt(extractMInt(leanGetRegister(X:Xmm, RSMap), 0, 64), MI:MInt), updateMapEntries(RSMap, UpdateEntries))
    requires convToRegKeys(X) ==K RK
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, concatenateMInt(ZMI:MInt, MI:MInt)), UpdateEntries:MapEntryList)
    => leanSetRegister(convRegKeyToXmm(RK), MI, updateMapEntries(RSMap, UpdateEntries))
    requires isXmmRegKey(RK) andBool ZMI ==K mi(128, 0)
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, concatenateMInt(ZMI:MInt, MI:MInt)), UpdateEntries:MapEntryList)
    => leanSetRegister(convRegKeyToXmm(RK), concatenateMInt(mi(bitwidthMInt(ZMI) -Int 128, 0), MI:MInt), updateMapEntries(RSMap, UpdateEntries))
    requires isXmmRegKey(RK) andBool zeroMInt(ZMI) andBool bitwidthMInt(ZMI) >Int 128
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, MI:MInt), UpdateEntries:MapEntryList)
    => leanSetRegister(convRegKeyToR64(RK), MI, updateMapEntries(RSMap, UpdateEntries))
    requires isR64RegKey(RK)
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, MI:MInt), UpdateEntries:MapEntryList)
    => leanSetRegister(convRegKeyToYmm(RK), MI, updateMapEntries(RSMap, UpdateEntries))
    requires isYmmRegKey(RK)
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, MI:MInt), UpdateEntries:MapEntryList)
    => leanSetRegister(convRegKeyToFlag(RK), MI, updateMapEntries(RSMap, UpdateEntries))
    requires isFlagRegKey(RK)
    [lemma]

  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, UDMI:MInt), UpdateEntries:MapEntryList)
    => leanSetRegister(convRegKeyToR8(RK), undefMInt8, updateMapEntries(RSMap, UpdateEntries))
    requires isR8RegKey(RK) andBool isUndefMInt(UDMI)
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, UDMI:MInt), UpdateEntries:MapEntryList)
    => leanSetRegister(convRegKeyToR16(RK), undefMInt16, updateMapEntries(RSMap, UpdateEntries))
    requires isR16RegKey(RK) andBool isUndefMInt(UDMI)
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, UDMI:MInt), UpdateEntries:MapEntryList)
    => leanSetRegister(convRegKeyToR32(RK), undefMInt32, updateMapEntries(RSMap, UpdateEntries))
    requires isR32RegKey(RK) andBool isUndefMInt(UDMI)
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, UDMI:MInt), UpdateEntries:MapEntryList)
    => leanSetRegister(convRegKeyToRh(RK), undefMInt8, updateMapEntries(RSMap, UpdateEntries))
    requires isRhRegKey(RK) andBool isUndefMInt(UDMI)
    [lemma]
  rule updateMapEntries(RSMap:Map, mapEntry(RK:String, UDMI:MInt), UpdateEntries:MapEntryList)
    => leanSetRegister(convRegKeyToR64(RK), undefMInt64, updateMapEntries(RSMap, UpdateEntries))
    requires isR64RegKey(RK) andBool isUndefMInt(UDMI)
    [lemma]

  rule leanSetRegister(R:Register, concatenateMInt(ZMI:MInt, MI:MInt), RSMap:Map)
    => leanSetRegister(convRegKeyToR32(convToRegKeysHelper(R)), MI, RSMap)
    requires isR32RegKey(convToRegKeysHelper(R)) andBool ZMI ==K mi(32, 0)
    [lemma]

  rule leanSetRegister(R:Register, MI1:MInt, leanSetRegister(F:Flag, MI2:MInt, RSMap:Map))
    => leanSetRegister(F, MI2, leanSetRegister(R, MI1, RSMap))
    requires notBool isFlag(R)
    [lemma]

  syntax Bool ::= isUndefMInt(MInt) [function]
  rule isUndefMInt(undefMInt) => true
  rule isUndefMInt(undefMInt8) => true
  rule isUndefMInt(undefMInt16) => true
  rule isUndefMInt(undefMInt32) => true
  rule isUndefMInt(undefMInt64) => true

  syntax MInt ::= leanGetRegister(Register, Map) [function]
  syntax Bool ::= leanGetFlag(Flag, Map) [function]
  rule getRegisterValue(R:Register, RSMap:Map) => leanGetRegister(R, RSMap)
    requires notBool isFlag(R)
  rule getRegisterValue(F:Flag, RSMap:Map) => boolToBv1(leanGetFlag(F, RSMap))
  rule extractMInt(getParentValue(R:R8, RSMap:Map), 56, 64) => getRegisterValue(R, RSMap) [lemma]
  rule extractMInt(getParentValue(R:R8, RSMap:Map), I:Int, J:Int)
    => extractMInt(getRegisterValue(R, RSMap), I -Int 56, J -Int 56)
    requires I >=Int 56 andBool J <=Int 64 andBool 0 <=Int J -Int I andBool J -Int I <Int 8
    [lemma]
  rule extractMInt(getParentValue(R:R16, RSMap:Map), 48, 64) => getRegisterValue(R, RSMap) [lemma]
  rule extractMInt(getParentValue(R:R16, RSMap:Map), I:Int, J:Int)
    => extractMInt(getRegisterValue(R, RSMap), I -Int 48, J -Int 48)
    requires I >=Int 48 andBool J <=Int 64 andBool 0 <=Int J -Int I andBool J -Int I <Int 16
    [lemma]
  rule extractMInt(getParentValue(R:R32, RSMap:Map), 32, 64) => getRegisterValue(R, RSMap) [lemma]
  rule extractMInt(getParentValue(R:R32, RSMap:Map), I:Int, J:Int)
    => extractMInt(getRegisterValue(R, RSMap), I -Int 32, J -Int 32)
    requires I >=Int 32 andBool J <=Int 64 andBool 0 <=Int J -Int I andBool J -Int I <Int 32
    [lemma]
  rule getParentValue(R:R64, RSMap:Map) => getRegisterValue(R, RSMap) [lemma]
  rule extractMInt(getParentValue(R:R64, RSMap:Map), I:Int, J:Int)
    => extractMInt(getRegisterValue(R, RSMap), I, J)
    requires 0 <=Int J -Int I andBool J -Int I <Int 64
    [lemma]
  rule extractMInt(getParentValue(R:Rh, RSMap:Map), 48, 56) => getRegisterValue(R, RSMap) [lemma]
  rule extractMInt(getParentValue(R:Rh, RSMap:Map), I:Int, J:Int)
    => extractMInt(getRegisterValue(R, RSMap), I -Int 48, J -Int 48)
    requires I >=Int 48 andBool J <=Int 56 andBool 0 <=Int J -Int I andBool J -Int I <Int 8
    [lemma]
  rule extractMInt(getParentValue(X:Xmm, RSMap:Map), 128, 256) => getRegisterValue(X, RSMap) [lemma]
  rule extractMInt(getParentValue(X:Xmm, RSMap:Map), I:Int, J:Int)
    => extractMInt(getRegisterValue(X, RSMap), I -Int 128, J -Int 128)
    requires I >=Int 128 andBool J <=Int 256 andBool 0 <=Int J -Int I andBool J -Int I <Int 128
    [lemma]
  rule getParentValue(Y:Ymm, RSMap:Map) => getRegisterValue(Y, RSMap) [lemma]
  rule extractMInt(getParentValue(Y:Ymm, RSMap:Map), I:Int, J:Int)
    => extractMInt(getRegisterValue(Y, RSMap), I, J)
    requires 0 <=Int J -Int I andBool J -Int I <Int 256
    [lemma]
  rule RSMap:Map[RK:String] => boolToBv1(leanGetFlag(convRegKeyToFlag(RK), RSMap))
    requires isFlagRegKey(RK)
    [lemma]
  rule {RSMap[RK:String]}:>MInt => leanGetRegister(convRegKeyToR64(RK), RSMap)
    requires isR64RegKey(RK)
    [lemma]

  rule getMemLoc(_:PointerVal) => loc(0, 0, 0, 0) [lemma]
  rule getMIntVal(PV:PointerVal) => PV [lemma]
  rule ptr(loc(0, 0, 0, 0), MI:MInt) => MI [lemma]
  rule convertPV(MI:MInt) => MI [lemma]

  syntax MInt ::= leanLoad(MInt, Int, Map) [function]
  rule
    <k> loadFromMemory(MI:MInt, Nbits:Int) => memLoadValue(leanLoad(MI, Nbits /Int 8, MemMap)) ...</k>
    <leanmemory> MemMap </leanmemory>
    requires Nbits %Int 8 ==Int 0

  syntax Map ::= leanStore(MInt, StoreVal, Int, Map) [function]
  rule
    <k> storeToMemory(Val:StoreVal, MI:MInt, Nbits:Int) => .K ...</k>
    <leanmemory> MemMap => leanStore(MI, Val, Nbits /Int 8, MemMap) </leanmemory>
    requires Nbits %Int 8 ==Int 0

  rule #ifMInt B:Bool #then concatenateMInt(MI1:MInt, MI2:MInt) #else concatenateMInt(MI1, MI3:MInt) #fi
    => concatenateMInt(MI1, #ifMInt B #then MI2 #else MI3 #fi)
    [lemma]
  rule #ifMInt B:Bool #then concatenateMInt(MI1:MInt, MI2:MInt) #else concatenateMInt(MI3:MInt, MI2) #fi
    => concatenateMInt(#ifMInt B #then MI1 #else MI3 #fi, MI2)
    [lemma]
  rule #ifMInt B:Bool #then concatenateMInt(ZMI1:MInt, MI:MInt) #else ZMI2:MInt #fi
    => concatenateMInt(mi(bitwidthMInt(ZMI1), 0), #ifMInt B #then MI #else mi(bitwidthMInt(ZMI2) -Int bitwidthMInt(ZMI1), 0) #fi)
    requires zeroMInt(ZMI1) andBool zeroMInt(ZMI2)
    [lemma]
  rule #ifMInt B:Bool #then ZMI1:MInt #else concatenateMInt(ZMI2:MInt, MI:MInt) #fi
    => concatenateMInt(mi(bitwidthMInt(ZMI2), 0), #ifMInt B #then mi(bitwidthMInt(ZMI1) -Int bitwidthMInt(ZMI2), 0) #else MI #fi)
    requires zeroMInt(ZMI1) andBool zeroMInt(ZMI2)
    [lemma]
  rule concatenateMInt(concatenateMInt(ZMI:MInt, MI1:MInt), MI2:MInt) => concatenateMInt(ZMI, concatenateMInt(MI1, MI2))
    requires zeroMInt(ZMI)
    [lemma]
  rule concatenateMInt(ZMI1:MInt, concatenateMInt(ZMI2:MInt, MI:MInt)) => concatenateMInt(mi(bitwidthMInt(ZMI1) +Int bitwidthMInt(ZMI2), 0), MI)
    requires zeroMInt(ZMI1) andBool zeroMInt(ZMI2)
    [lemma]

  rule notBool (notBool B:Bool) => B [lemma]
  rule #if B:Bool #then true #else false #fi => B [lemma]
  rule #if B:Bool #then false #else true #fi => notBool B [lemma]
  rule ((B1:Bool andBool B2:Bool) orBool ((notBool B) andBool B3:Bool))
    => (#ifBool B #then B2 #else B3 #fi)
    [lemma]
  rule (((notBool B1:Bool) andBool B2:Bool) orBool (B andBool B3:Bool))
    => (#ifBool B #then B3 #else B2 #fi)
    [lemma]

  rule bitwidthMInt(leanGetRegister(R:R8, _:Map)) => 8 [lemma]
  rule bitwidthMInt(leanGetRegister(R:R16, _:Map)) => 16 [lemma]
  rule bitwidthMInt(leanGetRegister(R:R32, _:Map)) => 32 [lemma]
  rule bitwidthMInt(leanGetRegister(R:Rh, _:Map)) => 8 [lemma]
  rule bitwidthMInt(leanGetRegister(R:R64, _:Map)) => 64 [lemma]
  rule bitwidthMInt(leanGetRegister(X:Xmm, _:Map)) => 128 [lemma]
  rule bitwidthMInt(leanGetRegister(Y:Ymm, _:Map)) => 256 [lemma]
  rule bitwidthMInt(leanLoad(_, I:Int, _:Map)) => I *Int 8 [lemma]
  rule bitwidthMInt(handleImmediateWithSignExtend(_, _, I:Int)) => I [lemma]
  rule bitwidthMInt(mi(I:Int, _:Int)) => I [lemma]
  rule bitwidthMInt(concatenateMInt(MI1:MInt, MI2:MInt)) => bitwidthMInt(MI1) +Int bitwidthMInt(MI2) [lemma]
  rule bitwidthMInt(extractMInt(_:MInt, I:Int, J:Int)) => J -Int I [lemma]
  rule bitwidthMInt(addMInt(MI:MInt, _:MInt)) => bitwidthMInt(MI) [lemma]
  rule bitwidthMInt(subMInt(MI:MInt, _:MInt)) => bitwidthMInt(MI) [lemma]
  rule bitwidthMInt(mulMInt(MI:MInt, _:MInt)) => bitwidthMInt(MI) [lemma]
  rule bitwidthMInt(andMInt(MI:MInt, _:MInt)) => bitwidthMInt(MI) [lemma]
  rule bitwidthMInt(orMInt(MI:MInt, _:MInt)) => bitwidthMInt(MI) [lemma]
  rule bitwidthMInt(xorMInt(MI:MInt, _:MInt)) => bitwidthMInt(MI) [lemma]
  rule bitwidthMInt(shlMInt(MI:MInt, _:Int)) => bitwidthMInt(MI) [lemma]
  rule bitwidthMInt(lshrMInt(MI:MInt, _:Int)) => bitwidthMInt(MI) [lemma]
  rule bitwidthMInt(ashrMInt(MI:MInt, _:Int)) => bitwidthMInt(MI) [lemma]
  rule bitwidthMInt(negMInt(MI:MInt)) => bitwidthMInt(MI) [lemma]
  rule bitwidthMInt(#ifMInt _:Bool #then MI:MInt #else _:MInt #fi) => bitwidthMInt(MI) [lemma]
  rule bitwidthMInt(leanSignExtend(_:MInt, I:Int)) => I [lemma]
  rule bitwidthMInt(leanZeroExtend(_:MInt, I:Int)) => I [lemma]
  rule bitwidthMInt(leanShl(MI:MInt, _:MInt)) => bitwidthMInt(MI) [lemma]
  rule bitwidthMInt(leanAshr(MI:MInt, _:MInt)) => bitwidthMInt(MI) [lemma]
  rule bitwidthMInt(leanLshr(MI:MInt, _:MInt)) => bitwidthMInt(MI) [lemma]

  syntax MInt ::= leanSignExtend(MInt, Int) [function]
                | leanZeroExtend(MInt, Int) [function]
  rule mi(I:Int, svalueMInt(MI:MInt)) => MI
    requires I ==K bitwidthMInt(MI)
    [lemma]
  rule mi(I:Int, uvalueMInt(MI:MInt)) => MI
    requires I ==K bitwidthMInt(MI)
    [lemma]
  rule mi(I:Int, svalueMInt(MI:MInt)) => leanSignExtend(MI, I)
    requires bitwidthMInt(MI) <Int I
    [lemma]
  rule mi(I:Int, uvalueMInt(MI:MInt)) => leanZeroExtend(MI, I)
    requires bitwidthMInt(MI) <Int I
    [lemma]

  syntax MInt ::= leanShl(MInt, MInt) [function]
                | leanAshr(MInt, MInt) [function]
                | leanLshr(MInt, MInt) [function]
  rule shlMInt(MI:MInt, I:Int) => leanShl(MI, mi(bitwidthMInt(MI), I))
  rule ashrMInt(MI:MInt, I:Int) => leanAshr(MI, mi(bitwidthMInt(MI), I))
  rule lshrMInt(MI:MInt, I:Int) => leanLshr(MI, mi(bitwidthMInt(MI), I))

  rule andMInt(extractMInt(MI1:MInt, I:Int, J:Int), extractMInt(MI2:MInt, I, J))
    => extractMInt(andMInt(MI1, MI2), I, J)
    requires bitwidthMInt(MI1) ==K bitwidthMInt(MI2)
    [lemma]
  rule orMInt(extractMInt(MI1:MInt, I:Int, J:Int), extractMInt(MI2:MInt, I, J))
    => extractMInt(orMInt(MI1, MI2), I, J)
    requires bitwidthMInt(MI1) ==K bitwidthMInt(MI2)
    [lemma]
  rule xorMInt(extractMInt(MI1:MInt, I:Int, J:Int), extractMInt(MI2:MInt, I, J))
    => extractMInt(xorMInt(MI1, MI2), I, J)
    requires bitwidthMInt(MI1) ==K bitwidthMInt(MI2)
    [lemma]

  rule leanSetRegister(F:Flag, MI:MInt, M:Map)
    => leanSetRegister(F, bv1ToBool(MI), M)

  syntax Bool ::= bv1ToBool(MInt) [function]
  syntax MInt ::= boolToBv1(Bool) [function]
  rule bv1ToBool(boolToBv1(B:Bool)) => B [lemma]
  rule bv1ToBool(TMI:MInt) => true
    requires TMI ==K mi(1, 1)
    [lemma]
  rule bv1ToBool(FMI:MInt) => false
    requires FMI ==K mi(1, 0)
    [lemma]
  rule bv1ToBool(#ifMInt B:Bool #then MI1:MInt #else MI2:MInt #fi)
    => #if B #then bv1ToBool(MI1) #else bv1ToBool(MI2) #fi
    [lemma]
  rule bv1ToBool(andMInt(MI1:MInt, MI2:MInt)) => bv1ToBool(MI1) andBool bv1ToBool(MI2)
  rule bv1ToBool(orMInt(MI1:MInt, MI2:MInt)) => bv1ToBool(MI1) orBool bv1ToBool(MI2)
  rule bv1ToBool(xorMInt(MI1:MInt, MI2:MInt)) => bv1ToBool(MI1) xorBool bv1ToBool(MI2)
  rule bv1ToBool(extractMInt(MI:MInt, I:Int, J:Int)) => isBitSet(MI, I)
    requires J ==K I +Int 1
    [lemma]
  rule bv1ToBool(undefMInt) => undefBool
    [lemma]
  rule eqMInt(boolToBv1(B:Bool), TMI:MInt) => B
    requires TMI ==K mi(1, 1)
    [lemma]
  rule eqMInt(TMI:MInt, boolToBv1(B:Bool)) => B
    requires TMI ==K mi(1, 1)
    [lemma]

  syntax Bool ::= isBitSet(MInt, Int) [function]
                | isBitClear(MInt, Int) [function]
  rule eqMInt(extractMInt(MI:MInt, I:Int, J:Int), TMI:MInt) => isBitSet(MI, I)
    requires J ==K I +Int 1 andBool TMI ==K mi(1, 1)
    [lemma]
  rule eqMInt(extractMInt(MI:MInt, I:Int, J:Int), FMI:MInt) => isBitClear(MI, I)
    requires J ==K I +Int 1 andBool FMI ==K mi(1, 0)
    [lemma]
  rule notBool isBitSet(MI:MInt, I:Int) => isBitClear(MI, I)
    [lemma]
  rule notBool isBitClear(MI:MInt, I:Int) => isBitSet(MI, I)
    [lemma]

  syntax Bool ::= parityFlag(MInt) [function]
  rule (isBitSet(MI:MInt, J:Int) ==K isBitSet(MI, I:Int))
    => parityFlag(extractMInt(MI, I, I +Int 2))
    requires J ==K I +Int 1
    [lemma]
  rule ((notBool parityFlag(extractMInt(MI:MInt, J:Int, K:Int))) ==K isBitSet(MI, I:Int))
    => parityFlag(extractMInt(MI, I, K))
    requires J ==K I +Int 1
    [lemma]

  syntax Bool ::= zeroFlag(MInt) [function]
  rule leanSetRegister(%zf, eqMInt(MI:MInt, ZMI:MInt), M:Map)
    => leanSetRegister(%zf, zeroFlag(MI), M:Map)
    requires zeroMInt(ZMI)
    [lemma]

  syntax Bool ::= overflowFlag(MInt, MInt, MInt) [function]
  rule (isBitSet(MI1:MInt, 0) ==K isBitSet(MI2:MInt, 0)) andBool (notBool (isBitSet(MI1, 0) ==K isBitSet(MI3:MInt, 1)))
    => overflowFlag(MI1, MI2, extractMInt(MI3, 1, bitwidthMInt(MI3)))
    requires bitwidthMInt(MI1) ==K bitwidthMInt(MI2) andBool bitwidthMInt(MI3) ==K bitwidthMInt(MI1) +Int 1
    [lemma]

  rule leanSetRegister(R:Register, MI:MInt, leanSetRegister(F:Flag, B:Bool, M:Map))
    => leanSetRegister(F, B, leanSetRegister(R, MI, M:Map))
    requires notBool isFlag(R)
    [lemma]
  rule leanSetRegister(R1:Register, MI1:MInt, leanSetRegister(R2:Register, MI2:MInt, M:Map))
    => leanSetRegister(R2, MI2, leanSetRegister(R1, MI1, M:Map))
    requires (notBool isFlag(R1)) andBool (notBool isFlag(R2)) andBool convToRegKeys(R1) <String convToRegKeys(R2)
    [lemma]
  rule leanSetRegister(F1:Flag, B1:Bool, leanSetRegister(F2:Flag, B2:Bool, M:Map))
    => leanSetRegister(F2, B2, leanSetRegister(F1, B1, M:Map))
    requires convFlagToRegKey(F1) <String convFlagToRegKey(F2)
    [lemma]
endmodule

